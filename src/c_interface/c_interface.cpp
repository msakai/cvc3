/*****************************************************************************/
/*!
 * \file c_interface.cpp
 * 
 * Authors: Clark Barrett  
 *          Cristian Cadar 
 * 
 * Created: Thu Jun  5 10:34:02 2003
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


#include <strings.h>
#include "c_interface_defs.h"
#include "vc.h"
#include "command_line_flags.h"
#include "parser.h"
#include "vc_cmd.h"
#include "theory_bitvector.h"
#include "fdstream.h"
#include <assert.h>

using namespace std;
//using namespace CVC3;



// -------------------------------------------------------------------------
//  Debugging                                                               
// -------------------------------------------------------------------------

// + will mean OK
// - will mean error
int c_interface_error_flag = 1;
const int error_int = -100;
const char* c_interface_error_message = "An Exception Occured: System in a compromised state.";
string c_interface_error_string;
// Used to return char* values.  Note that the value is only good until
// the next call to a function returning char*
static string tmpString;

void signal_error(char* message,int flag_val,CVC3::Exception ex){
  ostringstream ss;
  ss << c_interface_error_message << endl;
  ss << "Message: " << message << endl;
  ss << "Exception: " << ex << endl;
  IF_DEBUG(cerr << ss.str());
  c_interface_error_string = ss.str();
  c_interface_error_flag = flag_val;
}

extern "C" int get_error_status(){
  return c_interface_error_flag;
}

extern "C" void reset_error_status(){
  c_interface_error_flag = 1;
  c_interface_error_string = "";  
}

extern "C" char* get_error_string() {
  return (char*) (c_interface_error_string.c_str());
}


// ---------------------------

class CInterface {
public:
  static CVC3::Type fromType(Type t);
  static Type toType(const CVC3::Type& t);
  static CVC3::Expr fromExpr(Expr e);
  static Expr toExpr(const CVC3::Expr& e);
  static CVC3::Op fromOp(Op op);
  static Op toOp(VC vc, const CVC3::Op& op);
  //  static CVC3::Proof fromProof(Proof proof);
  //  static Proof toProof(const CVC3::Proof& proof);
  static void deleteExpr(Expr e);
};


CVC3::Type CInterface::fromType(Type t)
{
  return CVC3::Type(fromExpr(t));
}


Type CInterface::toType(const CVC3::Type& t)
{
  return toExpr(t.getExpr());
}


CVC3::Expr CInterface::fromExpr(Expr e)
{
  return CVC3::Expr((CVC3::ExprValue*)e);
}


Expr CInterface::toExpr(const CVC3::Expr& e)
{
  if (!e.d_expr) return NULL;
  e.d_expr->incRefcount();
  return (Expr)e.d_expr;
}


CVC3::Op CInterface::fromOp(Op op)
{
  CVC3::Expr e = fromExpr(op);
  if (e.isApply()) return e.getOp();
  return CVC3::Op(e.getKind());
}


Op CInterface::toOp(VC vc, const CVC3::Op& op)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return (Op)(toExpr(cvc->getEM()->newLeafExpr(op)));
}


// CVC3::Proof CInterface::fromProof(Proof proof)
// {
//   return CVC3::Proof(fromExpr(proof));
// }


// Proof CInterface::toProof(const CVC3::Proof& proof)
// {
//   return toExpr(proof.getExpr());
// }


void CInterface::deleteExpr(Expr e)
{
  if (e) ((CVC3::ExprValue*)e)->decRefcount();
}


static CVC3::Type fromType(Type t) { return CInterface::fromType(t); }
static Type toType(const CVC3::Type& t) { return CInterface::toType(t); }
static CVC3::Expr fromExpr(Expr e) { return CInterface::fromExpr(e); }
static Expr toExpr(const CVC3::Expr& e) { return CInterface::toExpr(e); }
static CVC3::Op fromOp(Op op) { return CInterface::fromOp(op); }
static Op toOp(VC vc, const CVC3::Op& op) { return CInterface::toOp(vc, op); }
// static CVC3::Proof fromProof(Proof proof) { return CInterface::fromProof(proof); }
// static Proof toProof(const CVC3::Proof& proof) { return CInterface::toProof(proof); }



extern "C" VC vc_createValidityChecker(Flags flags) {
  try{
    CVC3::CLFlags f = (flags==NULL)? CVC3::ValidityChecker::createFlags()
      : *((CVC3::CLFlags*)flags);
    return (VC)CVC3::ValidityChecker::create(f);
  } catch (CVC3::Exception ex){
	cerr << ex.toString() << endl;
    signal_error("vc_createValidityChecker",error_int,ex);
    return NULL;
  }
}


extern "C" Flags vc_createFlags() {
  return new CVC3::CLFlags(CVC3::ValidityChecker::createFlags());
}


extern "C" void vc_destroyValidityChecker(VC vc)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  delete cvc;
}


extern "C" void vc_deleteFlags(Flags flags) {
  delete ((CVC3::CLFlags*)flags);
}


extern "C" void vc_deleteExpr(Expr e)
{
  CInterface::deleteExpr(e);
}


extern "C" void vc_deleteType(Type t)
{
  vc_deleteExpr(t);
}


extern "C" void vc_deleteOp(Op op)
{
  vc_deleteExpr(op);
}


extern "C" void vc_deleteProof(Proof proof)
{
  vc_deleteExpr(proof);
}

// Setting the flags
// Set a boolean flag to true or false
extern "C" void vc_setBoolFlag(Flags flags, char* name, int val) {
  CVC3::CLFlags& f = *((CVC3::CLFlags*)flags);
  f.setFlag(name, (val!=0));
}

// Set an integer flag to the given value
extern "C" void vc_setIntFlag(Flags flags, char* name, int val) {
  CVC3::CLFlags& f = *((CVC3::CLFlags*)flags);
  f.setFlag(name, val);
}

// Set a string flag to the given value
extern "C" void vc_setStringFlag(Flags flags, char* name, char* val) {
  CVC3::CLFlags& f = *((CVC3::CLFlags*)flags);
  f.setFlag(name, string(val));
}

// Add a (string, bool) pair to the multy-string flag
extern "C" void vc_setStrSeqFlag(Flags flags, char* name, char* str, int val) {
  CVC3::CLFlags& f = *((CVC3::CLFlags*)flags);
  f.setFlag(name, pair<string,bool>(string(str), val!=0));
}

extern "C" Type vc_boolType(VC vc)
{
  try{
    CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
    return toType(cvc->boolType());
  } catch (CVC3::Exception ex){
    signal_error("vc_boolType",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_realType(VC vc)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->realType());
  }catch (CVC3::Exception ex){
    signal_error("vc_realType",error_int,ex);
    return NULL;
  }
}
  
extern "C" Type vc_subRangeType(VC vc, int lowerEnd, int upperEnd)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->parseType(cvc->listExpr("SUBRANGE", 
					     cvc->ratExpr(lowerEnd), 
					     cvc->ratExpr(upperEnd))));
  }catch (CVC3::Exception &ex){
    signal_error("vc_subRangeType",error_int,ex);
    return NULL;
  }
}

extern "C" Type vc_tupleType2(VC vc, Type type0, Type type1)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->tupleType(fromType(type0), fromType(type1)));
  }catch (CVC3::Exception ex){
    signal_error("vc_tupleType2",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_tupleType3(VC vc, Type type0, Type type1, Type type2)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->tupleType(fromType(type0), fromType(type1),
			       fromType(type2)));
  }catch (CVC3::Exception ex){
    signal_error("vc_tupleType3",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_tupleTypeN(VC vc, Type* types, int numTypes)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Type> cvcTypes;
  for (int i = 0; i < numTypes; ++i) {
    cvcTypes.push_back(fromType(types[i]));
  }
  return toType(cvc->tupleType(cvcTypes));
  }catch(CVC3::Exception ex){
    signal_error("vc_tupleTypeN",error_int,ex);
    return NULL;
  }
}

extern "C" Type vc_forallExpr(VC vc, Expr* Bvars, int numBvars, Expr f)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Expr> cvcBvars;
  for (int i = 0; i < numBvars; ++i) {
    cvcBvars.push_back(fromExpr(Bvars[i]));
  }
  return toExpr(cvc->forallExpr(cvcBvars,fromExpr(f)));
  }catch(CVC3::Exception ex){
    signal_error("vc_forallExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_existsExpr(VC vc, Expr* Bvars, int numBvars, Expr f)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Expr> cvcBvars;
  for (int i = 0; i < numBvars; ++i) {
    cvcBvars.push_back(fromExpr(Bvars[i]));
  }
  return toExpr(cvc->existsExpr(cvcBvars,fromExpr(f)));
  }catch(CVC3::Exception ex){
    signal_error("vc_forallExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_recordType1(VC vc, char* field, Type type)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->recordType(field, fromType(type)));
  }catch(CVC3::Exception ex){
    signal_error("vc_recordType1",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_recordType2(VC vc, char* field0, Type type0,
                                      char* field1, Type type1)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->recordType(field0, fromType(type0),
				field1, fromType(type1)));
  }catch(CVC3::Exception ex){
    signal_error("vc_recordType2",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_recordType3(VC vc, char* field0, Type type0,
			              char* field1, Type type1,
                                      char* field2, Type type2)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->recordType(field0, fromType(type0),
				field1, fromType(type1),
				field2, fromType(type2)));
  }catch(CVC3::Exception ex){
    signal_error("vc_recordType3",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_recordTypeN(VC vc, char** fields, Type* types,
			       int numFields)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<std::string> cvcFields;
  vector<CVC3::Type> cvcTypes;
  for (int i = 0; i < numFields; ++i) {
    cvcFields.push_back(fields[i]);
    cvcTypes.push_back(fromType(types[i]));
  }
  return toType(cvc->recordType(cvcFields, cvcTypes));
  }catch(CVC3::Exception ex){
    signal_error("vc_recordTypeN",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_arrayType(VC vc, Type typeIndex, Type typeData)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->arrayType(fromType(typeIndex), fromType(typeData)));
  }catch(CVC3::Exception ex){
    signal_error("vc_arrayType",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_funType1(VC vc, Type typeDom, Type typeRan)
{
  try{
    CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
    return toType(cvc->funType(fromType(typeDom), fromType(typeRan)));
  }catch(CVC3::Exception ex){
    signal_error("vc_funType1",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_funType2(VC vc, Type a1, Type a2, Type typeRan)
{
  try{
    CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
    vector<CVC3::Type> args;
    args.push_back(fromType(a1));
    args.push_back(fromType(a2));
    return toType(cvc->funType(args, fromType(typeRan)));
  }catch(CVC3::Exception ex){
    signal_error("vc_funType2",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_funType3(VC vc, Type a1, Type a2, Type a3, Type typeRan)
{
  try {
    CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
    vector<CVC3::Type> args;
    args.push_back(fromType(a1));
    args.push_back(fromType(a2));
    args.push_back(fromType(a3));
    return toType(cvc->funType(args, fromType(typeRan)));
  } catch(CVC3::Exception ex){
    signal_error("vc_funType3",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_funTypeN(VC vc, Type* a, Type typeRan, int numArgs)
{
  try{
    CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
    vector<CVC3::Type> args;
    for(int i=0; i<numArgs; ++i)
      args.push_back(fromType(*(a+i)));
    return toType(cvc->funType(args, fromType(typeRan)));
  }catch(CVC3::Exception ex){
    signal_error("vc_funTypeN",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_createType(VC vc, char* typeName)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->createType(typeName));
  }catch(CVC3::Exception ex){
    signal_error("vc_createType",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_lookupType(VC vc, char* typeName)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->lookupType(typeName));
  }catch(CVC3::Exception ex){
    signal_error("vc_lookupType",error_int,ex);
    return NULL;
  }
}


/////////////////////////////////////////////////////////////////////////////
// Expr manipulation methods                                               //
/////////////////////////////////////////////////////////////////////////////


extern "C" ExprManager vc_getEM(VC vc)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return (ExprManager)cvc->getEM();
}

extern "C" int vc_getKindInt(VC vc,char* kind_name)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return (cvc->getEM())->getKind(kind_name);
}

extern "C" const char* vc_getKindString(VC vc,int kind)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  tmpString = (cvc->getEM())->getKindName(kind);
  return tmpString.c_str();
}


extern "C" Expr vc_varExpr(VC vc, char* name, Type type)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->varExpr(name, fromType(type)));
  }catch(CVC3::Exception ex){
    signal_error("vc_getEM",error_int,ex);
    return NULL;
  }
}

extern "C" Expr vc_boundVarExpr(VC vc, char* name, char *uid, Type type)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->boundVarExpr(name, uid, fromType(type)));
  }catch(CVC3::Exception ex){
    signal_error("vc_getEM",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_lookupVar(VC vc, char* name, Type* type)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Type t;
  Expr e = toExpr(cvc->lookupVar(name, &t));
  *type = toType(t);
  return e;
  }catch(CVC3::Exception ex){
    signal_error("vc_lookupVar",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_getType(VC vc, Expr e)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->getType(fromExpr(e)));
  }catch(CVC3::Exception ex){
    signal_error("vc_getType",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_eqExpr(VC vc, Expr child0, Expr child1)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->eqExpr(fromExpr(child0), fromExpr(child1)));
  }catch(CVC3::Exception ex){
    signal_error("vc_eqExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_trueExpr(VC vc)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->trueExpr());
  }catch(CVC3::Exception ex){
    signal_error("vc_trueExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_falseExpr(VC vc)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->falseExpr());
  }catch(CVC3::Exception ex){
    signal_error("vc_falseExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_notExpr(VC vc, Expr child)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->notExpr(fromExpr(child)));
  }catch(CVC3::Exception ex){
    signal_error("vc_notExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_andExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->andExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_andExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_andExprN(VC vc, Expr* children, int numChildren)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Expr> cvcExprs;
  for (int i = 0; i < numChildren; ++i) {
    cvcExprs.push_back(fromExpr(children[i]));
  }
  return toExpr(cvc->andExpr(cvcExprs));
  }catch(CVC3::Exception ex){
    signal_error("vc_andExprN",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_orExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->orExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_orExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_orExprN(VC vc, Expr* children, int numChildren)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Expr> cvcExprs;
  for (int i = 0; i < numChildren; ++i) {
    cvcExprs.push_back(fromExpr(children[i]));
  }
  return toExpr(cvc->orExpr(cvcExprs));
  }catch(CVC3::Exception ex){
    signal_error("vc_orExprN",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_impliesExpr(VC vc, Expr hyp, Expr conc)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->impliesExpr(fromExpr(hyp), fromExpr(conc)));
  }catch(CVC3::Exception ex){
    signal_error("vc_impliesExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_iffExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->iffExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_iffExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_iteExpr(VC vc, Expr ifpart, Expr thenpart, Expr elsepart)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->iteExpr(fromExpr(ifpart), fromExpr(thenpart),
			     fromExpr(elsepart)));
  }catch(CVC3::Exception ex){
    signal_error("vc_iteExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_ratExpr(VC vc, int n, int d)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->ratExpr(n, d));
  }catch(CVC3::Exception ex){
    signal_error("vc_ratExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_ratExprFromStr(VC vc, char* n, char* d, int base)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->ratExpr(n, d, base));
  }catch(CVC3::Exception ex){
    signal_error("vc_ratExprFromStr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_uminusExpr(VC vc, Expr child)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->uminusExpr(fromExpr(child)));
  }catch(CVC3::Exception ex){
    signal_error("vc_uminusExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_plusExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->plusExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_plusExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_minusExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->minusExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_minusExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_multExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->multExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_multExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_ltExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->ltExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_ltExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_leExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->leExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_leExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_gtExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->gtExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_gtExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_geExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->geExpr(fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_geExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_recordExpr1(VC vc, char* field, Expr expr)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->recordExpr(field, fromExpr(expr)));
  }catch(CVC3::Exception ex){
    signal_error("vc_recordExpr1",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_recordExpr2(VC vc, char* field0, Expr expr0,
			              char* field1, Expr expr1)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->recordExpr(field0, fromExpr(expr0),
				field1, fromExpr(expr1)));
  }catch(CVC3::Exception ex){
    signal_error("vc_recordExpr2",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_recordExpr3(VC vc, char* field0, Expr expr0,
			              char* field1, Expr expr1,
			              char* field2, Expr expr2)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->recordExpr(field0, fromExpr(expr0),
				field1, fromExpr(expr1),
				field2, fromExpr(expr2)));
  }catch(CVC3::Exception ex){
    signal_error("vc_recordExpr3",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_recordExprN(VC vc, char** fields, Expr* exprs,
			       int numFields)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<std::string> cvcFields;
  vector<CVC3::Expr> cvcExprs;
  for (int i = 0; i < numFields; ++i) {
    cvcFields.push_back(fields[i]);
    cvcExprs.push_back(fromExpr(exprs[i]));
  }
  return toExpr(cvc->recordExpr(cvcFields, cvcExprs));
  }catch(CVC3::Exception ex){
    signal_error("vc_recordExprN",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_recSelectExpr(VC vc, Expr record, char* field)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->recSelectExpr(fromExpr(record), field));
  }catch(CVC3::Exception ex){
    signal_error("vc_recSelectExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_recUpdateExpr(VC vc, Expr record, char* field,
				 Expr newValue)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->recUpdateExpr(fromExpr(record), field,
				   fromExpr(newValue)));
  }catch(CVC3::Exception ex){
    signal_error("vc_recUpdateExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_readExpr(VC vc, Expr array, Expr index)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->readExpr(fromExpr(array), fromExpr(index)));
  }catch(CVC3::Exception ex){
    signal_error("vc_readExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->writeExpr(fromExpr(array), fromExpr(index),
			       fromExpr(newValue)));
  }catch(CVC3::Exception ex){
    signal_error("vc_writeExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Op vc_createOp(VC vc, char* name, Type type)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toOp(vc, cvc->createOp(name, fromType(type)));
  }catch(CVC3::Exception ex){
    signal_error("vc_createOp",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_funExpr1(VC vc, Op op, Expr child)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->funExpr(fromOp(op), fromExpr(child)));
  }catch(CVC3::Exception ex){
    signal_error("vc_funExpr1",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_funExpr2(VC vc, Op op, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->funExpr(fromOp(op), fromExpr(left), fromExpr(right)));
  }catch(CVC3::Exception ex){
    signal_error("vc_funExpr2",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_funExpr3(VC vc, Op op, Expr child0, Expr child1,
			    Expr child2)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->funExpr(fromOp(op), fromExpr(child0), fromExpr(child1),
			     fromExpr(child2)));
  }catch(CVC3::Exception ex){
    signal_error("vc_funExpr3",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_funExprN(VC vc, Op op, Expr* children, int numChildren)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Expr> cvcExprs;
  for (int i = 0; i < numChildren; ++i) {
    cvcExprs.push_back(fromExpr(children[i]));
  }
  return toExpr(cvc->funExpr(fromOp(op), cvcExprs));
  }catch(CVC3::Exception ex){
    signal_error("vc_funExprN",error_int,ex);
    return NULL;
  }
}

extern "C" Expr vc_tupleExprN(VC vc, Expr* children, int numChildren)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Expr> cvcExprs;
  for (int i = 0; i < numChildren; ++i) {
    cvcExprs.push_back(fromExpr(children[i]));
  }
  return toExpr(cvc->tupleExpr(cvcExprs));
  }catch(CVC3::Exception ex){
    signal_error("vc_tupleExprN",error_int,ex);
    return NULL;
  }
}


extern "C" void vc_printExpr(VC vc, Expr e)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  cvc->printExpr(fromExpr(e));
  }catch(CVC3::Exception ex){
    signal_error("vc_printExpr",error_int,ex);
  }
}


extern "C" void vc_printExprFile(VC vc, Expr e, int fd)
{
  try {
    fdostream os(fd);
    if(!os) throw CVC3::Exception("vc_printExprFile: Bad file descriptor: "
				  +CVC3::int2string(fd));
    CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
    cvc->printExpr(fromExpr(e), os);
    os.flush();
  } catch(CVC3::Exception ex) {
    signal_error("vc_printExpr",error_int,ex);
  }
}


/////////////////////////////////////////////////////////////////////////////
// Context-related methods                                                 //
/////////////////////////////////////////////////////////////////////////////


extern "C" void vc_assertFormula(VC vc, Expr e)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  cvc->assertFormula(fromExpr(e));
  }catch(CVC3::Exception ex){
    signal_error("vc_assertFormula",error_int,ex);
  }
}


extern "C" void vc_registerAtom(VC vc, Expr e)
{
  try{
    CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
    cvc->registerAtom(fromExpr(e));
  }catch(CVC3::Exception ex){
    signal_error("vc_registerAtom",error_int,ex);
  }
}


extern "C" Expr vc_getImpliedLiteral(VC vc)
{
  try {
    CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
    return toExpr(cvc->getImpliedLiteral());
  } catch(CVC3::Exception ex){
    signal_error("vc_getImpliedLiteral",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_simplify(VC vc, Expr e)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->simplify(fromExpr(e)));
  }catch(CVC3::Exception ex){
    signal_error("vc_simplify",error_int,ex);
    return NULL;
  }
}


extern "C" int vc_query(VC vc, Expr e)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return (int)cvc->query(fromExpr(e));
  }catch(CVC3::Exception ex){
    signal_error("vc_query",error_int,ex);
    return error_int;
  }
}


/* Returns a counterexample as a list of assignments.
   Returns NULL on error */
extern "C" Expr* vc_getCounterExample(VC vc, int* size)
{
  int n = 0;
  static Expr* locAssumptions = NULL;
  
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::ExprMap<CVC3::Expr> assertions;
  cvc->getConcreteModel(assertions);
  locAssumptions = new Expr[assertions.size()];
  CVC3::ExprMap<CVC3::Expr>::iterator it = assertions.begin(), end = assertions.end();
  for (; it != end; it++) {    
    locAssumptions[n] = toExpr(cvc->eqExpr(it->first, it->second));
    n++;
  }
  *size = n;
  return locAssumptions;
  }catch(CVC3::Exception ex){
    cout << c_interface_error_message << endl;
    cout << "Exception: " << ex.toString();
    return NULL;
  }
}


extern "C" int vc_inconsistent(VC vc, Expr** assumptions, int* size)
{
  try{
  static Expr* locAssumptions = NULL;
  static int locsize = 0;
  if (locAssumptions) {
    for (int j = 0; j < locsize; ++j) {
      vc_deleteExpr(locAssumptions[j]);
    }
    delete [] locAssumptions;
  }
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Expr> assertions;
  bool ret = cvc->inconsistent(assertions);
  locAssumptions = new Expr[assertions.size()];
  for (unsigned i = 0; i < assertions.size(); ++i) {
    locAssumptions[i] = toExpr(assertions[i]);
  }
  *assumptions = locAssumptions;
  locsize = *size = assertions.size();
  return (int)ret;
  }catch(CVC3::Exception ex){
    signal_error("vc_inconsistent",error_int,ex);
    return 0;
  }
}


extern "C" void vc_setResourceLimit(VC vc, unsigned limit)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  cvc->setResourceLimit(limit);
}


extern "C" Expr vc_getProof(VC vc)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->getProof().getExpr());
  }catch(CVC3::Exception ex){
    signal_error("vc_getProof",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_getProofOfFile(VC vc, char* fileName){

  try{
  cout<<"in getProofOffile\n";
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Parser* parser;
  parser = new CVC3::Parser(cvc,
			cvc->getEM()->getInputLang(),
			0,
                        string(fileName));
  CVC3::VCCmd* cmd = new CVC3::VCCmd(cvc, parser);
  cout<<"\n begin process commands\n";
  cmd->processCommands();
  cout<<"\n end of procsssing commands\n";
  // delete cmd;
  // delete parser;
  cout<<"\n begin to return the proof\n";
  return toExpr(cvc->getProof().getExpr());
  } catch (CVC3::Exception ex){
    signal_error("vc_getProofsOfFile",error_int,ex);
    return NULL;
  }
}
  

extern "C" void vc_push(VC vc)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  cvc->push();
}


extern "C" void vc_pop(VC vc)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  cvc->pop();
}


extern "C" void vc_popto(VC vc, int scopeLevel)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  cvc->popto(scopeLevel);
}


extern "C" int vc_scopeLevel(VC vc)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return cvc->scopeLevel();
}


extern "C" Context vc_getCurrentContext(VC vc)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return (Context)cvc->getCurrentContext();
}


// -------------------------------------------------------------------------
//  Util                                                                    
// -------------------------------------------------------------------------

extern "C" const char* exprString(Expr e){
  try{
    tmpString =(fromExpr(e)).toString();
    return tmpString.c_str();
  } catch (CVC3::Exception ex){
    signal_error("exprString",error_int,ex);
    return "ERROR";
  }
}

extern "C" const char* typeString(Type t){
  try{
    tmpString = (fromExpr(t)).toString();
    return tmpString.c_str();
  } catch (CVC3::Exception ex){
    signal_error("typeString",error_int,ex);
    return "ERROR";
  }
}

extern "C" int arity(Expr e){
  try{
    return (fromExpr(e)).arity();
  } catch (CVC3::Exception ex){
    signal_error("arity",error_int,ex);
    return error_int;
  }
}

extern "C" int getKind(Expr e){
  try{
    return (fromExpr(e)).getKind();
  } catch (CVC3::Exception ex){
    signal_error("getKind",error_int,ex);
    return error_int;
  }
}

extern "C" Expr getChild(Expr e, int i){
  try{
    return toExpr(((fromExpr(e))[i]));
  } catch (CVC3::Exception ex){
    signal_error("getChild",error_int,ex);
    return NULL;
  }
}
  
extern "C" bool isClosure(Expr e){
  try{
    return (fromExpr(e)).isClosure();
  } catch (CVC3::Exception ex){
    signal_error("isClosure",error_int,ex);
    return false;
  }
}

extern "C" bool isQuantifier(Expr e){
  try{
    return (fromExpr(e)).isQuantifier();
  } catch (CVC3::Exception ex){
    signal_error("isQuantifier",error_int,ex);
    return false;
  }
}

extern "C" bool isLambda(Expr e){
  try{
    return (fromExpr(e)).isLambda();
  } catch (CVC3::Exception ex){
    signal_error("isLambda",error_int,ex);
    return false;
  }
}

extern "C" Expr getVar(Expr e, int i){
  try{
    int size = ((fromExpr(e)).getVars()).size();
    if(i < size){ 
      Expr expr = toExpr(((fromExpr(e)).getVars())[i]);
      return expr;
    } else {
      throw CVC3::Exception();
    }
  } catch (CVC3::Exception ex){
    signal_error("getVar",error_int,ex);
    return NULL;
  }
}

extern "C" int getNumVars(Expr e){
  try{
    return (fromExpr(e)).getVars().size();
  } catch (CVC3::Exception ex){
    signal_error("getNumVars",error_int,ex);
    return error_int;
  }
}

extern "C" Expr getBody(Expr e){
  try{
    return toExpr((fromExpr(e)).getBody());
  } catch (CVC3::Exception ex){
    signal_error("getBody",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_getFun(VC vc, Expr e)
{
  try{
    return toExpr((fromExpr(e)).getOp().getExpr());
  }catch(CVC3::Exception ex){
    signal_error("vc_getFun",error_int,ex);
    return NULL;
  }
}


extern "C" Expr toExpr(Type t){
  try{
    return toExpr((fromType(t)).getExpr());
  } catch (CVC3::Exception ex){
    signal_error("toExpr",error_int,ex);
    return NULL;
  }
}

extern "C" bool isVar(Expr e){
  try{
    return (fromExpr(e)).isVar();
  } catch (CVC3::Exception ex){
    signal_error("isVar",error_int,ex);
    return false;
  }
}


extern "C" int getInt(Expr e){
  try{
    return (fromExpr(e)).getRational().getInt();
  } catch (CVC3::Exception ex){
    signal_error("getInt",error_int,ex);
    return error_int;
  }
}

extern "C" int getBVInt(Expr e){
  try{
    return CVC3::computeBVConst(fromExpr(e)).getInt();
  } catch (CVC3::Exception ex){
    signal_error("getBVInt",error_int,ex);
    return 0;
  }
}

extern "C" unsigned int getBVUnsigned(Expr e){
  try{
    return CVC3::computeBVConst(fromExpr(e)).getUnsigned();
  } catch (CVC3::Exception ex){
    signal_error("getBVUnsigned",error_int,ex);
    return 0;
  }
}

extern "C" int compare_exprs(Expr e1,Expr e2){
  try{
    return (compare(fromExpr(e1),fromExpr(e2)));
  } catch (CVC3::Exception ex){
    signal_error("compare",error_int,ex);
    return error_int;
  }
}
  
extern "C" Type vc_intType(VC vc)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->intType());
  }catch (CVC3::Exception ex){
    signal_error("vc_intType",error_int,ex);
    return NULL;
  }
}

extern "C" Expr vc_powExpr(VC vc, Expr pow, Expr base)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->powExpr(fromExpr(pow), fromExpr(base)));
  }catch(CVC3::Exception ex){
    signal_error("vc_powExpr",error_int,ex);
    return NULL;
  }
}

extern "C" Expr vc_divideExpr(VC vc, Expr numerator, Expr denominator)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->divideExpr(fromExpr(numerator), fromExpr(denominator)));
  }catch(CVC3::Exception ex){
    signal_error("vc_divideExpr",error_int,ex);
    return NULL;
  }
}

extern "C" void print_statistics(VC vc)
{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  cvc->printStatistics();
}


/**************************/
/* BIT VECTOR OPERATIONS  */
/**************************/


extern "C" Type vc_bvType(VC vc, int no_bits)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toType(cvc->parseType(cvc->listExpr("BITVECTOR", cvc->ratExpr(no_bits))));
  }catch (CVC3::Exception ex){
    signal_error("vc_bvType",error_int,ex);
    return NULL;
  }
}


extern "C" Type vc_bv32Type(VC vc)
{
  return vc_bvType(vc, 32);
}



extern "C" Expr vc_bvConstExprFromStr(VC vc, char* binary_repr)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  return toExpr(cvc->parseExpr(cvc->listExpr("BVCONST", cvc->stringExpr(binary_repr))));
  }catch(CVC3::Exception ex){
    signal_error("vc_bvConstExpr",error_int, ex);
    return NULL;
  }
}


#include <assert.h>

static char *val_to_binary_str(unsigned nbits, unsigned long long val) {
        char s[65];

	assert(nbits < sizeof s);
        strcpy(s, "");
        while(nbits-- > 0) {
                if((val >> nbits) & 1)
                        strcat(s, "1");
                else
                        strcat(s, "0");
        }
        return strdup(s);
}

extern "C" Expr vc_bvConstExprFromInt(VC vc, int n_bits, unsigned int value)
{
  char* s = val_to_binary_str(n_bits, value);
  return vc_bvConstExprFromStr(vc, s);
}

extern "C" Expr 
vc_bvConstExprFromLL(VC vc, int n_bits, unsigned long long value)
{
  char* s = val_to_binary_str(n_bits, value);
  return vc_bvConstExprFromStr(vc, s);
}


#if 0
extern "C" Expr vc_bvConstExprFromInt(VC vc, int n_bits, unsigned int value)
{
  char* s = (char*) malloc(100);
  char* saux = (char*) malloc(100);
  strcpy(s, "");

  while (value) {
    strcpy(saux, s);
    if (value % 2 == 0)
      strcpy(s, "0");
    else strcpy(s, "1");
    strcat(s, saux);
    value = value / 2;
    n_bits--;
  }
  while (n_bits) {
    strcpy(saux, s);
    strcpy(s, "0");
    strcat(s, saux);
    n_bits--;
  }
  
  free(saux);

  return vc_bvConstExprFromStr(vc, s);
}
#endif


extern "C" Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value)
{
  return vc_bvConstExprFromInt(vc, 32, value);
}

extern "C" Expr vc_bvPlusExpr(VC vc, int n_bits, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVPLUS", cvc->ratExpr(n_bits), fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvPlusExpr",error_int,ex);
    return NULL;
  }
}

extern "C" Expr vc_bvConcatExpr(VC vc,Expr left, Expr right) {
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("CONCAT",fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception &ex){
    signal_error("vc_bvConcatExpr",error_int,ex);
    return NULL;
  }
}

extern "C" Expr vc_bvConcatExprN(VC vc, Expr* children, int numChildren) {
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  vector<CVC3::Expr> cvcExprs;
  for (int i = 0; i < numChildren; ++i) {
    cvcExprs.push_back(fromExpr(children[i]));
  }
  CVC3::Expr lExpr = cvc->listExpr("CONCAT",cvcExprs);
  return toExpr(cvc->parseExpr(lExpr));
  }catch(CVC3::Exception &ex){
    signal_error("vc_concatExprN",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right)
{
  return vc_bvPlusExpr(vc, 32, left, right);
}


extern "C" Expr vc_bvMinusExpr(VC vc, int n_bits, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVSUB", cvc->ratExpr(n_bits), fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvMinusExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right)
{
  return vc_bvMinusExpr(vc, 32, left, right);
}


extern "C" Expr vc_bvMultExpr(VC vc, int n_bits, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVMULT", cvc->ratExpr(n_bits), fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvMultExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bv32MultExpr(VC vc, Expr left, Expr right)
{
  return vc_bvMultExpr(vc, 32, left, right);
}


extern "C" Expr vc_bvLtExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVLT", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvLtExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_sbvLtExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("SBVLT", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_sbvLtExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvLeExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVLE", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvLeExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_sbvLeExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("SBVLE", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_sbvLeExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvGtExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVGT", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvGtExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_sbvGtExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("SBVGT", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_sbvGtExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvGeExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVGE", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvGeExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_sbvGeExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("SBVGE", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_sbvGeExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvUMinusExpr(VC vc, Expr child)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVUMINUS", fromExpr(child));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvUMinusExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvAndExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVAND", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvAndExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvOrExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVOR", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvOrExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvXorExpr(VC vc, Expr left, Expr right)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVXOR", fromExpr(left), fromExpr(right));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvXorExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvNotExpr(VC vc, Expr child)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BVNEG", fromExpr(child));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvNegExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvExtract(VC vc, Expr child, int high_bit_no, int low_bit_no)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("EXTRACT", fromExpr(child), cvc->ratExpr(high_bit_no), cvc->ratExpr(low_bit_no));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvExtract",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvBoolExtract(VC vc, Expr child, int bit_no)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("BOOLEXTRACT", fromExpr(child), cvc->ratExpr(bit_no));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvBoolExtract",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvSignExtend(VC vc, Expr child, int nbits)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("SX", fromExpr(child), cvc->ratExpr(nbits));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvSignExtend",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr child)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("LEFTSHIFT", fromExpr(child), cvc->ratExpr(sh_amt));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvLeftShiftExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr child)
{
  try{
  CVC3::ValidityChecker* cvc = (CVC3::ValidityChecker*) vc;
  CVC3::Expr lExpr = cvc->listExpr("RIGHTSHIFT", fromExpr(child), cvc->ratExpr(sh_amt));
  return toExpr(cvc->parseExpr(lExpr));
  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvRightShiftExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child) {
  try{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  for(int count=32; count >= 0; count--){
    if(count != 32) {
      ifpart = vc_eqExpr(vc, sh_amt, 
			 vc_bvConstExprFromInt(vc, 32, count));
      thenpart = vc_bvExtract(vc,
			      vc_bvLeftShiftExpr(vc, count, child),
			      31, 0);

      ite = vc_iteExpr(vc,ifpart,thenpart,elsepart);
      elsepart = ite;
    } else {
      elsepart = vc_bvConstExprFromInt(vc,32, 0);
    }    
  }  
  return ite;  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvVar32LeftShiftExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs) {
  try{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  for(int count=32; count >= 0; count--){
    if(count != 32) {
      ifpart = vc_eqExpr(vc, rhs, 
			 vc_bvConstExprFromInt(vc, 32, 1 << count));      
      thenpart = vc_bvRightShiftExpr(vc, count, child);      
      ite = vc_iteExpr(vc,ifpart,thenpart,elsepart);
      elsepart = ite;
    } else {
      elsepart = vc_bvConstExprFromInt(vc,32, 0);
    }    
  }  
  return ite;  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvVar32DivByPowOfTwoExpr",error_int,ex);
    return NULL;
  }
}


extern "C" Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child)
{
  try{
  Expr ifpart;
  Expr thenpart;
  Expr elsepart = vc_trueExpr(vc);
  Expr ite = vc_trueExpr(vc);

  for(int count=32; count >= 0; count--){
    if(count != 32) {
      ifpart = vc_eqExpr(vc, sh_amt, 
			 vc_bvConstExprFromInt(vc, 32, count));      
      thenpart = vc_bvRightShiftExpr(vc, count, child);      
      ite = vc_iteExpr(vc,ifpart,thenpart,elsepart);
      elsepart = ite;
    } else {
      elsepart = vc_bvConstExprFromInt(vc,32, 0);
    }    
  }  
  return ite;  
  }catch(CVC3::Exception ex){
    signal_error("vc_bvVar32LeftShiftExpr",error_int,ex);
    return NULL;
  }
}
 

/* Same as vc_bvLeftShift only that the answer in 32 bits long */
extern "C" Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child) {
  return vc_bvExtract(vc, vc_bvLeftShiftExpr(vc, sh_amt, child), 31, 0);
}


/* Same as vc_bvRightShift only that the answer in 32 bits long */
extern "C" Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child) {
  return vc_bvExtract(vc, vc_bvRightShiftExpr(vc, sh_amt, child), 31, 0);
}

/* C pointer support: C interface to support C memory arrays in CVC3 */
extern "C" Expr vc_bvCreateMemoryArray(VC vc, char * arrayName) {
  Type bv8  = vc_bvType(vc,8);
  Type bv32 = vc_bvType(vc,32);
  
  Type malloced_mem0 = vc_arrayType(vc,bv32,bv8);
  return vc_varExpr(vc, arrayName, malloced_mem0);
}

/*OLD VERSIONS C pointer theory functions. DO NOT DELETE */

// //Warning: Type checking needed to ensure that the function is run
// //correctly is not being done. it is assumed that the function
// //recieves inputs of the correct types
// extern "C" Expr vc_bvReadMemoryArray(VC vc, 
// 				     Expr array, 
// 				     Expr byteIndex, int newBitsPerElem) {
//   DebugAssert(newBitsPerElem%8 == 0,
// 	      "new bits per element must be a multiple of 8\n");

//   Expr numerator = vc_bvMultExpr(vc,32,
// 				 vc_bvConstExprFromInt(vc,32,newBitsPerElem),
// 				 byteIndex);
//   int numOfBytes = newBitsPerElem/8;
//   DebugAssert(numOfBytes > 0,
// 	      "numOfBytes must be greater than 0");

//   if(numOfBytes == 1)
//     return vc_readExpr(vc,array,numerator);
//   else {
//     int count = 1;
//     Expr a = vc_readExpr(vc,array,numerator);
//     while(--numOfBytes > 0) {
//       Expr b = vc_readExpr(vc,array,
// 			   vc_bvPlusExpr(vc,32,numerator,vc_bvConstExprFromInt(vc,32,count)));
//       a = vc_bvConcatExpr(vc,a,b);
//       count++;
//     }
//     return a;
//   }    
// }

// extern "C" Expr vc_bvWriteToMemoryArray(VC vc, 
// 					Expr array, Expr byteIndex, 
// 					Expr element, int newBitsPerElem) {
//   DebugAssert(newBitsPerElem%8 == 0,
// 	      "new bits per element must be a multiple of 8\n");

//   Expr numerator = vc_bvMultExpr(vc,32,
// 				 vc_bvConstExprFromInt(vc,32,newBitsPerElem),
// 				 byteIndex);
//   int numOfBytes = newBitsPerElem/8;
//   DebugAssert(numOfBytes > 0,
// 	      "numOfBytes must be greater than 0");

//   if(numOfBytes == 1)
//     return vc_writeExpr(vc,array,numerator, element);
//   else {
//     int count = 1;
//     int hi = newBitsPerElem - 1;
//     int low = newBitsPerElem - 8;
//     Expr c = vc_bvExtract(vc,element,hi,low);
//     Expr newarray = vc_writeExpr(vc,array,numerator,c);
//     while(--numOfBytes > 0) {
//       hi = low-1;
//       low = low-8;      
//       c = vc_bvExtract(vc,element,hi,low);
//       newarray = vc_writeExpr(vc,newarray,numerator,c);
//       count++;
//     }
//     return newarray;
//   }    
// }


extern "C" Expr vc_bvReadMemoryArray(VC vc, 
				     Expr array, 
				     Expr byteIndex, int numOfBytes) {

  DebugAssert(0 < numOfBytes,
	      "number of Bytes must be greater than 0\n");

  if(numOfBytes == 1)
    return vc_readExpr(vc,array,byteIndex);
  else {
    int count = 1;
    Expr a = vc_readExpr(vc,array,byteIndex);
    while(--numOfBytes > 0) {
      Expr b = vc_readExpr(vc,array,
			   /*vc_simplify(vc, */
				       vc_bvPlusExpr(vc, 32, 
						     byteIndex,
						     vc_bvConstExprFromInt(vc,32,count)))/*)*/;
      a = vc_bvConcatExpr(vc,b,a);
      count++;
    }
    return a;
  }    
}

extern "C" Expr vc_bvWriteToMemoryArray(VC vc, 
					Expr array, Expr byteIndex, 
					Expr element, int numOfBytes) {
  DebugAssert(numOfBytes > 0,
	      "numOfBytes must be greater than 0");

  int newBitsPerElem = numOfBytes*8;
  if(numOfBytes == 1)
    return vc_writeExpr(vc, array, byteIndex, element);
  else {
    int count = 1;
    int hi = newBitsPerElem - 1;
    int low = newBitsPerElem - 8;
    int low_elem = 0;
    int hi_elem = low_elem + 7;
    Expr c = vc_bvExtract(vc, element, hi_elem, low_elem);
    Expr newarray = vc_writeExpr(vc, array, byteIndex, c);
    while(--numOfBytes > 0) {
      hi = low-1;
      low = low-8;      

      low_elem = low_elem + 8;
      hi_elem = low_elem + 7;

      c = vc_bvExtract(vc, element, hi_elem, low_elem);
      newarray = 
	vc_writeExpr(vc, newarray,
		     vc_bvPlusExpr(vc, 32, byteIndex, vc_bvConstExprFromInt(vc,32,count)),
		     c);
      count++;
    }
    return newarray;
  }    
}

