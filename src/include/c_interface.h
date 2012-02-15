/*****************************************************************************/
/*!
 * \file c_interface.h
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

#ifndef _cvc3__include__c_interface_h_
#define _cvc3__include__c_interface_h_

#include "c_interface_defs.h"

//! Flags can be NULL
VC vc_createValidityChecker(Flags flags);
//! Create validity checker's flags
Flags vc_createFlags();
//! Destroy the validity checker.
/*! Must be called after all other objects are deleted, except the flags */
void vc_destroyValidityChecker(VC vc);
//! Delete the flags
void vc_deleteFlags(Flags flags);
//! Delete type
void vc_deleteType(Type t);
//! Delete expression
void vc_deleteExpr(Expr e);
//! Delete operator
void vc_deleteOp(Op op);

// Setting the flags
//! Set a boolean flag to true or false
void vc_setBoolFlag(Flags flags, char* name, int val);
//! Set an integer flag to the given value
void vc_setIntFlag(Flags flags, char* name, int val);
//! Set a string flag to the given value
void vc_setStringFlag(Flags flags, char* name, char* val);
//! Add a (string, bool) pair to the multy-string flag
void vc_setStrSeqFlag(Flags flags, char* name, char* str, int val);

// Basic types
Type vc_boolType(VC vc);
Type vc_realType(VC vc);
Type vc_intType(VC vc);

// Tuple types
Type vc_tupleType2(VC vc, Type type0, Type type1);
Type vc_tupleType3(VC vc, Type type0, Type type1, Type type2);
//! Create a tuple type.  'types' is an array of types of length numTypes.
Type vc_tupleTypeN(VC vc, Type* types, int numTypes);

// Record types
Type vc_recordType1(VC vc, char* field, Type type);
Type vc_recordType2(VC vc, char* field0, Type type0,
                           char* field1, Type type1);
Type vc_recordType3(VC vc, char* field0, Type type0,
	                   char* field1, Type type1,
	                   char* field2, Type type2);
//! Create a record type.
/*! 'fields' and 'types' are arrays of length numFields. */
Type vc_recordTypeN(VC vc, char** fields, Type* types, int numFields);

//! Create an array type
Type vc_arrayType(VC vc, Type typeIndex, Type typeData);

//! Create a subrange type
Type vc_subRangeType(VC vc, int lowerEnd, int upperEnd);

//! Create a function type with 1 argument
Type vc_funType1(VC vc, Type a1, Type typeRan);
//! Create a function type with 2 arguments
Type vc_funType2(VC vc, Type a1, Type a2, Type typeRan);
//! Create a function type with 3 arguments
Type vc_funType3(VC vc, Type a1, Type a2, Type a3, Type typeRan);
//! Create a function type with N arguments
Type vc_funTypeN(VC vc, Type* args, Type typeRan, int numArgs);

// User-defined types

//! Create an uninterpreted named type
Type vc_createType(VC vc, char* typeName);
//! Lookup a user-defined (uninterpreted) type by name
Type vc_lookupType(VC vc, char* typeName);

/////////////////////////////////////////////////////////////////////////////
// Expr manipulation methods                                               //
/////////////////////////////////////////////////////////////////////////////

//! Return the ExprManager
ExprManager* vc_getEM(VC vc);

//! Create a variable with a given name and type 
/*! The type cannot be a function type. */
Expr vc_varExpr(VC vc, char* name, Type type);

//! Get the expression and type associated with a name.
/*!  If there is no such Expr, a NULL Expr is returned. */
Expr vc_lookupVar(VC vc, char* name, Type* type);

//! Get the type of the Expr.
Type vc_getType(VC vc, Expr e);

//! Create an equality expression.  The two children must have the same type.
Expr vc_eqExpr(VC vc, Expr child0, Expr child1);

// Boolean expressions

// The following functions create Boolean expressions.  The children provided
// as arguments must be of type Boolean.
Expr vc_trueExpr(VC vc);
Expr vc_falseExpr(VC vc);
Expr vc_notExpr(VC vc, Expr child);
Expr vc_andExpr(VC vc, Expr left, Expr right);
Expr vc_andExprN(VC vc, Expr* children, int numChildren);
Expr vc_orExpr(VC vc, Expr left, Expr right);
Expr vc_orExprN(VC vc, Expr* children, int numChildren);
Expr vc_impliesExpr(VC vc, Expr hyp, Expr conc);
Expr vc_iffExpr(VC vc, Expr left, Expr right);
Expr vc_iteExpr(VC vc, Expr ifpart, Expr thenpart, Expr elsepart);

// Arithmetic

//! Create a rational number with numerator n and denominator d.  
/*! d cannot be 0. */
Expr vc_ratExpr(VC vc, int n, int d);

//! Create a rational number n/d; n and d are given as strings
/*! n and d are converted to arbitrary-precision integers according to
 *  the given base.  d cannot be 0.  */
Expr vc_ratExprFromStr(VC vc, char* n, char* d, int base);

//! Unary minus.  Child must have a numeric type.
Expr vc_uminusExpr(VC vc, Expr child);

// plus, minus, mult.  Children must have numeric types.
Expr vc_plusExpr(VC vc, Expr left, Expr right);
Expr vc_minusExpr(VC vc, Expr left, Expr right);
Expr vc_multExpr(VC vc, Expr left, Expr right);
Expr vc_powExpr(VC vc, Expr pow, Expr base);
Expr vc_divideExpr(VC vc, Expr numerator, Expr denominator);

// The following functions create less-than, less-than or equal,
// greater-than, and greater-than or equal expressions of type Boolean.
// Their arguments must be of numeric types.
Expr vc_ltExpr(VC vc, Expr left, Expr right);
Expr vc_leExpr(VC vc, Expr left, Expr right);
Expr vc_gtExpr(VC vc, Expr left, Expr right);
Expr vc_geExpr(VC vc, Expr left, Expr right);

// Records

// Create record literals;
Expr vc_recordExpr1(VC vc, char* field, Expr expr);
Expr vc_recordExpr2(VC vc, char* field0, Expr expr0,
		                   char* field1, Expr expr1);
Expr vc_recordExpr3(VC vc, char* field0, Expr expr0,
                                   char* field1, Expr expr1,
		                   char* field2, Expr expr2);
Expr vc_recordExprN(VC vc, char** fields, Expr* exprs, int numFields);

//! Create an expression representing the selection of a field from a record.
Expr vc_recSelectExpr(VC vc, Expr record, char* field);

//! Record update; equivalent to "record WITH .field := newValue"
Expr vc_recUpdateExpr(VC vc, Expr record, char* field, Expr newValue);

// Arrays

//! Create an expression for the value of array at the given index
Expr vc_readExpr(VC vc, Expr array, Expr index);

//! Array update; equivalent to "array WITH [index] := newValue"
Expr vc_writeExpr(VC vc, Expr array, Expr index, Expr newValue);

// User-defined (uninterpreted) functions.

//! Create an operator from a function with a given name and type.
/*! Name is given as an ID Expr, and the type must be a function type. */
Op vc_createOp(VC vc, char* name, Type type);

//! Create expressions with a user-defined operator.
/*!  op must have a function type. */
Expr vc_funExpr1(VC vc, Op op, Expr child);
Expr vc_funExpr2(VC vc, Op op, Expr left, Expr right);
Expr vc_funExpr3(VC vc, Op op, Expr child0, Expr child1, Expr child2);
Expr vc_funExprN(VC vc, Op op, Expr* children, int numChildren);

// Tuples

//! Create a tuple expression
/*! 'children' is an array of elements of length numChildren */
Expr vc_tupleExprN(VC vc, Expr* children, int numChildren);

// Quantifiers

//! Create a bound variable.  
/*! \param name
 * \param uid is a fresh unique string to distinguish this variable 
 * from other bound variables with the same name
 * \param type
 */
Expr vc_boundVarExpr(VC vc, char* name, char *uid, Type type);
//! Create a FORALL quantifier.  
/*! Bvars is an array of bound variables of length numBvars. */
Type vc_forallExpr(VC vc, Expr* Bvars, int numBvars, Expr f);
//! Create an EXISTS quantifier.  
/*! Bvars is an array of bound variables of length numBvars. */
Type vc_existsExpr(VC vc, Expr* Bvars, int numBvars, Expr f);

// Expr I/O
//! Expr vc_parseExpr(VC vc, char* s);
void vc_printExpr(VC vc, Expr e);
//! Print 'e' into an open file descriptor
void vc_printExprFile(VC vc, Expr e, int fd);

/////////////////////////////////////////////////////////////////////////////
// Context-related methods                                                 //
/////////////////////////////////////////////////////////////////////////////

//! Assert a new formula in the current context.  
/*! The formula must have Boolean type. */
void vc_assertFormula(VC vc, Expr e);

//! Register an atomic formula of interest.
/*! Registered atoms are tracked by the decision procedures.  If one of them
    is deduced to be true or false, it is added to a list of implied literals.
    Implied literals can be retrieved with the getImpliedLiteral function */
void vc_registerAtom(VC vc, Expr e);

//! Return next literal implied by last assertion.  Null if none.
/*! Returned literals are either registered atomic formulas or their negation
 */
Expr vc_getImpliedLiteral(VC vc);

//! Simplify e with respect to the current context
Expr vc_simplify(VC vc, Expr e);

//! Check validity of e in the current context.
/*!  If the result is true, then the resulting context is the same as
 * the starting context.  If the result is false, then the resulting
 * context is a context in which e is false.  e must have Boolean
 * type. */
int vc_query(VC vc, Expr e);

//! Return the counterexample after a failed query.
/*! This method should only be called after a query which returns
 * false.  It will try to return the simplest possible set of
 * assertions which are sufficient to make the queried expression
 * false.  The caller is responsible for freeing the array when
 * finished with it.
 */
Expr* vc_getCounterExample(VC vc, int* size);

// Returns true if the current context is inconsistent.

/*! Also returns a minimal set of assertions used to determine the
 * inconsistency.  The caller is responsible for freeing the array
 * when finished with it.
 */
int vc_inconsistent(VC vc, Expr** assumptions, int* size);

//! Set the resource limit (0==unlimited, 1==exhausted).
/*! Currently, the limit is the total number of processed facts. */
void vc_setResourceLimit(VC vc, unsigned limit);

//! Returns the proof for the last proven query
Expr vc_getProof(VC vc);

//! Returns the proof of a .cvc file, if it is valid.
Expr vc_getProofOfFile(VC vc, char * filename);

//! Checkpoint the current context and increase the scope level
void vc_push(VC vc);

//! Restore the current context to its state at the last checkpoint
void vc_pop(VC vc);

//! Restore the current context to the given scopeLevel.
/*! scopeLevel must be less than or equal to the current scope level.
 * If scopeLevel is less than 1, then the current context is reset and
 * the scope level is set to 1.
 */
void vc_popto(VC vc, int scopeLevel);

//! Returns the current scope level.  Initially, the scope level is 1.
int vc_scopeLevel(VC vc);

//! Get the current context
Context* vc_getCurrentContext(VC vc);

/* ---------------------------------------------------------------------- */
/*  Util                                                                  */
/* ---------------------------------------------------------------------- */

// Order

//! Compares two expressions
/*! If e1 < e2, e1==e2, and e1 > e2, it returns -1, 0, 1
 * respectively.
 *
 * Can't be 'compare' because already defined in ocaml */
int compare_exprs(Expr e1,Expr e2);

// Printing

//! Convert Expr to string
char* exprString(Expr e);
//! Convert Type to string
char* typeString(Type t);

// What kind of Expr?
int isClosure(Expr e);
int isQuantifier(Expr e);
int isLambda(Expr e);
Expr isVar(Expr e);

int arity(Expr e);
int getKind(Expr e);
Expr getChild(Expr e, int i);
Expr getNumVars(Expr e);
Expr getVar(Expr e, int i);
Expr getBody(Expr e);
Expr vc_getFun(VC vc, Expr e);
Expr toExpr(Type t);

//! Translate a kind int to a string
const char* vc_getKindString(VC vc,int kind);

//! Translate a kind string to an int
int vc_getKindInt(VC vc,char* kind_name);

//! Return an int from a rational expression
int getInt(Expr e);

//! Return an int from a constant bitvector expression
int getBVInt(Expr e);
//! Return an unsigned int from a constant bitvector expression
unsigned int getBVUnsigned(Expr e);

// Debug
int get_error_status();
void reset_error_status();
char* get_error_string();

/////////////////////////////////////////////////////////////////////////////
// Collecting and printing statistics
/////////////////////////////////////////////////////////////////////////////

//! Print statistics
void print_statistics(VC vc);


/**************************/
/* BIT VECTOR OPERATIONS  */
/**************************/


Type vc_bvType(VC vc, int no_bits);
Type vc_bv32Type(VC vc);

Expr vc_bvConstExprFromStr(VC vc, char* binary_repr);
Expr vc_bvConstExprFromInt(VC vc, int n_bits, unsigned int value);
Expr vc_bv32ConstExprFromInt(VC vc, unsigned int value);

Expr vc_bvConcatExpr(VC vc, Expr left, Expr right);
Expr vc_bvConcatExprN(VC vc, Expr* children, int numChildren);
Expr vc_bvPlusExpr(VC vc, int n_bits, Expr left, Expr right);
Expr vc_bv32PlusExpr(VC vc, Expr left, Expr right);
Expr vc_bvMinusExpr(VC vc, int n_bits, Expr left, Expr right);
Expr vc_bv32MinusExpr(VC vc, Expr left, Expr right);
Expr vc_bvMultExpr(VC vc, int n_bits, Expr left, Expr right);
Expr vc_bv32MultExpr(VC vc, Expr left, Expr right);

Expr vc_bvLtExpr(VC vc, Expr left, Expr right);
Expr vc_bvLeExpr(VC vc, Expr left, Expr right);
Expr vc_bvGtExpr(VC vc, Expr left, Expr right);
Expr vc_bvGeExpr(VC vc, Expr left, Expr right);

Expr vc_sbvLtExpr(VC vc, Expr left, Expr right);
Expr vc_sbvLeExpr(VC vc, Expr left, Expr right);
Expr vc_sbvGtExpr(VC vc, Expr left, Expr right);
Expr vc_sbvGeExpr(VC vc, Expr left, Expr right);


Expr vc_bvUMinusExpr(VC vc, Expr child);

Expr vc_bvAndExpr(VC vc, Expr left, Expr right);
Expr vc_bvOrExpr(VC vc, Expr left, Expr right);
Expr vc_bvXorExpr(VC vc, Expr left, Expr right);
Expr vc_bvNotExpr(VC vc, Expr child);

Expr vc_bvLeftShiftExpr(VC vc, int sh_amt, Expr child);
Expr vc_bvRightShiftExpr(VC vc, int sh_amt, Expr child);
Expr vc_bv32LeftShiftExpr(VC vc, int sh_amt, Expr child);
Expr vc_bv32RightShiftExpr(VC vc, int sh_amt, Expr child);
Expr vc_bvVar32LeftShiftExpr(VC vc, Expr sh_amt, Expr child);
Expr vc_bvVar32RightShiftExpr(VC vc, Expr sh_amt, Expr child);
Expr vc_bvVar32DivByPowOfTwoExpr(VC vc, Expr child, Expr rhs);

Expr vc_bvExtract(VC vc, Expr child, int high_bit_no, int low_bit_no);
Expr vc_bvBoolExtract(VC vc, Expr child, int bit_no);

Expr vc_bvSignExtend(VC vc, Expr child, int nbits);

/*C pointer support:  C interface to support C memory arrays in CVC3 */
Expr vc_bvCreateMemoryArray(VC vc, char * arrayName);
Expr vc_bvReadMemoryArray(VC vc, 
			  Expr array, Expr byteIndex, int numOfBytes);
Expr vc_bvWriteToMemoryArray(VC vc, 
			     Expr array, Expr  byteIndex, 
			     Expr element, int numOfBytes);

Expr vc_bvConstExprFromLL(VC vc, int n_bits, unsigned long long value);

#endif


