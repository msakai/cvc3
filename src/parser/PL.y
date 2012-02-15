%{
/*****************************************************************************/
/*!
 * \file PL.y
 * 
 * Author: Sergey Berezin
 * 
 * Created: Feb 06 03:00:43 GMT 2003
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
/* PL.y
   Aaron Stump, 4/14/01

   This file contains the bison code for the parser that reads in CVC
   commands in the presentation language (hence "PL").
*/

#include "vc.h"
#include "parser_exception.h"
#include "parser_temp.h"
#include "rational.h"

// Exported shared data
namespace CVC3 {
  extern ParserTemp* parserTemp;
}
// Define shortcuts for various things
#define TMP CVC3::parserTemp
#define EXPR CVC3::parserTemp->expr
#define VC (CVC3::parserTemp->vc)
#define RAT(args) CVC3::newRational args

// Suppress the bogus warning suppression in bison (it generates
// compile error)
#undef __GNUC_MINOR__

/* stuff that lives in PL.lex */
extern int PLlex(void);

int PLerror(const char *s)
{
  std::ostringstream ss;
  ss << CVC3::parserTemp->fileName << ":" << CVC3::parserTemp->lineNum
     << ": " << s;
  return CVC3::parserTemp->error(ss.str());
}


namespace CVC3 {

// File-static auxiliary funcion to wrap accessors upto the index i
// (not inclusive) around "e".  Used to rebuild the UPDATE expressions.
static Expr wrapAccessors(const Expr& e,
			  const std::vector<Expr>& accessors,
			  const int i) {
  DebugAssert((int)accessors.size() >= i, "wrapAccessors: too few accessors");
  Expr res(e);
  for(int j=0; j<i; j++) {
    const Expr& acc = accessors[j];
    switch(acc.getKind()) {
    case ID: // Datatype: apply the accessor directly to 'res'
      res = VC->listExpr(acc, res);
      break;
    case RAW_LIST:
      DebugAssert(acc.arity() == 2 && acc[0].getKind() == ID,
		  "PL.y: wrong number of arguments in the accessor of WITH: "
		  +acc.toString());
      res = VC->listExpr(acc[0], res, acc[1]);
      break;
    default:
      DebugAssert(false, "PL.y: Bad accessor in WITH: "+acc.toString());
    }
  }
  return res;
}

// Convert a complex WITH statement into a bunch of nested simple UPDATEs

// Updator "e1 WITH accessors := e2" is represented as
// (e1 (accessor1 accessor2 ... ) e2), where the accessors are:
// (READ idx)
// ID (datatype constructor's argument)
// (RECORD_SELECT ID)
// and (TUPLE_SELECT num).
 
// We rebuild this into nested RECORD_UPDATE, WRITE,
// TUPLE_UPDATE, and DATATYPE_UPDATE expressions.  For example:
//
// e WITH [idx] car.f := newVal  is transformed into
// e WITH [idx] := (e[idx] WITH car := (car(e[idx]) WITH .f := newVal))
// which is represented as
// (WRITE e idx
//        (DATATYPE_UPDATE (READ e idx) car
//                         (RECORD_UPDATE (car (READ e idx)) f newVal))).
// Here "car" and "f" are identifiers (ID "car") and (ID "f").

static Expr PLprocessUpdate(const CVC3::Expr& e,
			    const CVC3::Expr& update) {
  TRACE("parser verbose", "PLprocessUpdate(", e, ") {");
  DebugAssert(update.arity() == 2,"PL.y: Bad WITH statement: "
	      +update.toString());
  // Rebuild accessors: resolve ID in (READ (ID "name")) and leave
  // the rest alone
  TRACE("parser verbose", "PLprocessUpdate: update[0] = ", update[0], "");
  std::vector<Expr> acc;
  for(Expr::iterator i=update[0].begin(), iend=update[0].end(); i!=iend; ++i) {
    TRACE("parser verbose", "*i = ", *i, "");
    acc.push_back(*i);
  }
  TRACE("parser verbose", "acc.size() = ", acc.size(), "");
  TRACE("parser verbose", "accessors = ", VC->listExpr(acc), "");
  // 'res' serves as the accumulator of updators; initially it is
  // newVal (which is update[1]).  We run through accessors in reverse
  // order, wrapping this accumulator with the corresponding
  // updators.
  Expr res(update[1]);
  // Rebuilding the original expression "e"
  // The main loop
  for(int i=acc.size()-1; i>=0; i--) {
    Expr ac(acc[i]);  // The current accessor
    TRACE("parser verbose", "ac["+int2string(i)+"] = ", ac, "");
    // "e" with all preceding accessors
    Expr tmp(wrapAccessors(e, acc, i));
    TRACE("parser verbose", "tmp = ", tmp, "");
    switch(ac.getKind()) {
    case ID: // Datatype update
      res = VC->listExpr("_DATATYPE_UPDATE", tmp, ac, res);
      break;
    case RAW_LIST: {
      const std::string& kind = ac[0][0].getString();
      if(kind == "_READ") // Array update
	res = VC->listExpr("_WRITE", tmp, ac[1], res);
      else if(kind == "_RECORD_SELECT") // Record update
	res = VC->listExpr("_RECORD_UPDATE", tmp, ac[1], res);
      else if(kind == "_TUPLE_SELECT") // Tuple element
	res = VC->listExpr("_TUPLE_UPDATE", tmp, ac[1], res);
      else
	DebugAssert(false, "PL.y: Bad accessor in WITH: "+ac.toString());
      break;
    }
    default:
      DebugAssert(false, "PL.y: Bad accessor in WITH: "+ac.toString());
    }
  }
  TRACE("parser verbose", "PLprocessUpdate => ", res, " }");
  return res;
}


// Process a vector of simultaneous updates (from a single WITH)
static Expr PLprocessUpdates(const CVC3::Expr& e,
			     const std::vector<CVC3::Expr>& updates,
			     size_t idx=0) {
  // Processed all the updates
  if(idx >= updates.size()) return e;
  return PLprocessUpdates(PLprocessUpdate(e, updates[idx]), updates, idx+1);
}



} // end of namespace CVC3

#define YYLTYPE_IS_TRIVIAL 1
#define YYMAXDEPTH 10485760
/* Prefer YYERROR_VERBOSE over %error-verbose to avoid errors in older bison */
#define YYERROR_VERBOSE 1
%}

%union {
  std::string *str;
  CVC3::Expr *node;
  std::vector<CVC3::Expr> *vec;
  int kind;
};


%start cmd

/* strings are for better error messages.  
   "_TOK" is so macros don't conflict with kind names */

%token  DISTINCT_TOK    "DISTINCT"
%token	AND_TOK			"AND"
%token	ARRAY_TOK		"ARRAY"
%token	BOOLEAN_TOK		"BOOLEAN"
%token	DATATYPE_TOK		"DATATYPE"
%token	ELSE_TOK		"ELSE"
%token	ELSIF_TOK		"ELSIF"
%token	END_TOK			"END"
%token	ENDIF_TOK		"ENDIF"
%token	EXISTS_TOK		"EXISTS"
%token	FALSELIT_TOK		"FALSE"
%token	FORALL_TOK		"FORALL"
%token	IN_TOK			"IN"
%token	IF_TOK			"IF"
%token	LAMBDA_TOK		"LAMBDA"
%token	SIMULATE_TOK		"SIMULATE"
%token	LET_TOK			"LET"
%token	NOT_TOK			"NOT"
%token	IS_INTEGER_TOK		"IS_INTEGER"
%token	OF_TOK			"OF"
%token	OR_TOK			"OR"
%token	REAL_TOK		"REAL"
%token  INT_TOK                 "INT"
%token  SUBTYPE_TOK             "SUBTYPE"
%token  BITVECTOR_TOK           "BITVECTOR"
%token	THEN_TOK		"THEN"
%token	TRUELIT_TOK		"TRUE"
%token	TYPE_TOK		"TYPE"
%token	WITH_TOK		"WITH"
%token	XOR_TOK			"XOR"
%token	TCC_TOK			"TCC"
%token	PATTERN_TOK		"PATTERN"
%token '_'
%token  DONE_TOK

%token	DOTDOT_TOK		".."
%token	ASSIGN_TOK		":="
%token	NEQ_TOK			"/="
%token	IMPLIES_TOK		"=>"
%token	IFF_TOK			"<=>"
%token	PLUS_TOK		"+"
%token	MINUS_TOK		"-"
%token	MULT_TOK		"*"
%token	POW_TOK			"^"
%token	DIV_TOK			"/"
%token	MOD_TOK			"MOD"
%token	INTDIV_TOK		"DIV"
%token	LT_TOK			"<"
%token	LE_TOK			"<="
%token	GT_TOK			">"
%token	GE_TOK			">="
%token  FLOOR_TOK               "FLOOR"
%token  LEFTSHIFT_TOK            "<<"
%token  RIGHTSHIFT_TOK           ">>"
%token  BVPLUS_TOK              "BVPLUS"
%token  BVSUB_TOK               "BVSUB"
%token  BVUDIV_TOK              "BVUDIV"
%token  BVSDIV_TOK              "BVSDIV"
%token  BVUREM_TOK              "BVUREM"
%token  BVSREM_TOK              "BVSREM"
%token  BVSMOD_TOK              "BVSMOD"
%token  BVSHL_TOK               "BVSHL"
%token  BVASHR_TOK              "BVASHR"
%token  BVLSHR_TOK              "BVLSHR"
%token  BVUMINUS_TOK            "BVUMINUS"
%token  BVMULT_TOK              "BVMULT"
%token	SQHASH_TOK		"[#"
%token	HASHSQ_TOK		"#]"
%token	PARENHASH_TOK		"(#"
%token	HASHPAREN_TOK		"#)"
%token	ARROW_TOK		"->"
%token  BVNEG_TOK               "~"
%token  BVAND_TOK               "&"
%token  MID_TOK                 "|"
%token  BVXOR_TOK               "BVXOR"
%token  BVNAND_TOK              "BVNAND"
%token  BVNOR_TOK               "BVNOR"
%token  BVCOMP_TOK              "BVCOMP"
%token  BVXNOR_TOK              "BVXNOR"
%token  CONCAT_TOK              "@"
%token  BVTOINT_TOK             "BVTOINT"
%token  INTTOBV_TOK             "INTTOBV"
%token  BOOLEXTRACT_TOK         "BOOLEXTRACT"
%token  BVLT_TOK                "BVLT"
%token  BVGT_TOK                "BVGT"
%token  BVLE_TOK                "BVLE"
%token  BVGE_TOK                "BVGE"
%token  SX_TOK                  "SX"
%token  BVZEROEXTEND_TOK        "BVZEROEXTEND"
%token  BVREPEAT_TOK            "BVREPEAT"
%token  BVROTL_TOK              "BVROTL"
%token  BVROTR_TOK              "BVROTR"
%token  BVSLT_TOK               "BVSLT"
%token  BVSGT_TOK               "BVSGT"
%token  BVSLE_TOK               "BVSLE"
%token  BVSGE_TOK               "BVSGE"


/* commands given in prefix syntax */
%token  ARITH_VAR_ORDER_TOK     "ARITH_VAR_ORDER"
%token  ASSERT_TOK              "ASSERT"
%token  QUERY_TOK               "QUERY"
%token  CHECKSAT_TOK            "CHECKSAT"
%token  CONTINUE_TOK            "CONTINUE"
%token  RESTART_TOK             "RESTART"
%token  HELP_TOK                "HELP"
%token  DBG_TOK                 "DBG"
%token  TRACE_TOK               "TRACE"
%token  UNTRACE_TOK             "UNTRACE"
%token  OPTION_TOK              "OPTION"
%token  TRANSFORM_TOK           "TRANSFORM"
%token  PRINT_TOK               "PRINT"
%token  PRINT_TYPE_TOK          "PRINT_TYPE"
%token  CALL_TOK                "CALL"
%token  ECHO_TOK                "ECHO"
%token  INCLUDE_TOK             "INCLUDE"
%token  DUMP_PROOF_TOK          "DUMP_PROOF"
%token  DUMP_ASSUMPTIONS_TOK    "DUMP_ASSUMPTIONS"
%token  DUMP_SIG_TOK            "DUMP_SIG"
%token  DUMP_TCC_TOK            "DUMP_TCC"
%token  DUMP_TCC_ASSUMPTIONS_TOK "DUMP_TCC_ASSUMPTIONS"
%token  DUMP_TCC_PROOF_TOK      "DUMP_TCC_PROOF"
%token  DUMP_CLOSURE_TOK        "DUMP_CLOSURE"
%token  DUMP_CLOSURE_PROOF_TOK  "DUMP_CLOSURE_PROOF"
%token  WHERE_TOK               "WHERE"
%token  ASSERTIONS_TOK          "ASSERTIONS"
%token  ASSUMPTIONS_TOK         "ASSUMPTIONS"
%token  COUNTEREXAMPLE_TOK      "COUNTEREXAMPLE"
%token  COUNTERMODEL_TOK        "COUNTERMODEL"
%token  PUSH_TOK                "PUSH"
%token  POP_TOK                 "POP"
%token  POPTO_TOK               "POPTO"
%token  PUSH_SCOPE_TOK          "PUSH_SCOPE"
%token  POP_SCOPE_TOK           "POP_SCOPE"
%token  POPTO_SCOPE_TOK         "POPTO_SCOPE"
%token  RESET_TOK               "RESET"
%token  CONTEXT_TOK             "CONTEXT"
%token  FORGET_TOK              "FORGET"
%token  GET_TYPE_TOK            "GET_TYPE"
%token  CHECK_TYPE_TOK          "CHECK_TYPE"
%token  GET_CHILD_TOK           "GET_CHILD"
%token  GET_OP_TOK              "GET_OP"
%token  SUBSTITUTE_TOK          "SUBSTITUTE"

%nonassoc ASSIGN_TOK IN_TOK
%nonassoc FORALL_TOK EXISTS_TOK
%left IFF_TOK
%right IMPLIES_TOK
%left OR_TOK XOR_TOK 
%left AND_TOK
%left NOT_TOK

%nonassoc '=' NEQ_TOK
%nonassoc LE_TOK LT_TOK GE_TOK GT_TOK FLOOR_TOK
%left PLUS_TOK MINUS_TOK
%left MULT_TOK INTDIV_TOK DIV_TOK MOD_TOK
%left POW_TOK
%left WITH_TOK
%left UMINUS_TOK
%left CONCAT_TOK
%left MID_TOK
%left BVAND_TOK
%left BVXOR_TOK
%left BVNAND_TOK
%left BVNOR_TOK BVCOMP_TOK
%left BVXNOR_TOK
%left BVNEG_TOK
%left BVUMINUS_TOK BVPLUS_TOK BVSUB_TOK 
%left BVUDIV_TOK BVSDIV_TOK BVUREM_TOK BVSREM_TOK BVSMOD_TOK BVSHL_TOK BVASHR_TOK BVLSHR_TOK
%left SX_TOK BVZEROEXTEND_TOK BVREPEAT_TOK BVROTL_TOK BVROTR_TOK
%left LEFTSHIFT_TOK RIGHTSHIFT_TOK
%nonassoc BVLT_TOK BVLE_TOK BVGT_TOK BVGE_TOK 
%nonassoc BVSLT_TOK BVSLE_TOK BVSGT_TOK BVSGE_TOK 
%right IS_INTEGER_TOK
%left ARROW_TOK

%nonassoc '[' 
%nonassoc '{' '.' '('
%nonassoc BITVECTOR_TOK

%type <vec> FieldDecls TypeList IDs reverseIDs SingleDataTypes Constructors
%type <vec> LetDecls TypeLetDecls BoundVarDecls ElseRest VarDecls 
%type <vec> Exprs AndExpr OrExpr Pattern Patterns
%type <vec> RecordEntries UpdatePosition Updates

%type <node> Type /* IndexType */ TypeNotIdentifier TypeDef
%type <node> DataType SingleDataType Constructor
%type <node> FunctionType RecordType Real Int BitvectorType
%type <node> FieldDecl TupleType
%type <node> ArrayType ScalarType SubType BasicType SubrangeType 
%type <node> LeftBound RightBound
%type <node> Expr Conditional UpdatePositionNode Update Lambda
%type <node> QuantExpr ArrayLiteral RecordLiteral RecordEntry TupleLiteral 
%type <node> LetDecl LetExpr LetDeclsNode 
%type <node> TypeLetDecl TypeLetExpr TypeLetDeclsNode
%type <node> BoundVarDecl BoundVarDeclNode VarDecl
%type <node> ConstDecl TypeDecl 
%type <node> Identifier StringLiteral Numeral Binary Hex

%type <node> Assert Query Help Dbg Trace Option  
%type <node> Transform Print Call Echo DumpCommand
%type <node> Include Where Push Pop PopTo
%type <node> Context Forget Get_Child Get_Op Get_Type Check_Type Substitute
%type <node> other_cmd
%type <node> Arith_Var_Order

%token <str> ID_TOK STRINGLIT_TOK NUMERAL_TOK HEX_TOK BINARY_TOK

%%

cmd             :       TypeDecl ';'
                        {
			  EXPR = *$1;
			  delete $1;
			  YYACCEPT;
			}
                |       ConstDecl ';'
                        {
			  EXPR = *$1;
			  delete $1;
			  YYACCEPT;
			}
                |       other_cmd ';' {
			  EXPR = *$1;
			  delete $1;
			  YYACCEPT;
			}
                |       ';'
                        {
			  EXPR = CVC3::Expr();
			  YYACCEPT;
			}
                |       DONE_TOK 
                        {
			  TMP->done = true;
			  EXPR = CVC3::Expr();
			  YYACCEPT;
			}
                ;

other_cmd       :       Assert { $$ = $1; }
                |       Query { $$ = $1; }
                |       Dbg { $$ = $1; }
                |       Trace { $$ = $1; }
                |       Option { $$ = $1; }
                |       Help { $$ = $1; }
                |       Transform { $$ = $1; }
                |       Print { $$ = $1; }
                |       Call { $$ = $1; }
                |       Echo { $$ = $1; }
                |       Include { $$ = $1; }
                |       DumpCommand { $$ = $1; }
                |       Where { $$ = $1; }
                |       Push { $$ = $1; }
                |       Pop { $$ = $1; }
                |       PopTo { $$ = $1; }
                |       Context { $$ = $1; }
                |       Substitute { $$ = $1; }
                |       Get_Child { $$ = $1; }
                |       Get_Op { $$ = $1; }
                |       Get_Type { $$ = $1; }
                |       Check_Type { $$ = $1; }
                |       Forget { $$ = $1; }
                |       Arith_Var_Order { $$ = $1; }
                ;

Arith_Var_Order :       ARITH_VAR_ORDER_TOK '(' Exprs ')'
                        {
                            $$ = new CVC3::Expr(VC->listExpr("_ARITH_VAR_ORDER", *$3));
                            delete $3;
                        }
                ;

Assert          :       ASSERT_TOK Expr { 

                          $$ = new CVC3::Expr(VC->listExpr("_ASSERT", *$2));
			  delete $2;
                        }
                ;

Query           :       QUERY_TOK Expr { 
                          $$ = new CVC3::Expr(VC->listExpr("_QUERY", *$2));
			  delete $2;
                        }
                |       CHECKSAT_TOK Expr {
                          $$ = new CVC3::Expr(VC->listExpr("_CHECKSAT", *$2));
                          delete $2;
                        }
                |       CHECKSAT_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_CHECKSAT")));
                        }
                |       CONTINUE_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_CONTINUE")));
                        }
                |       RESTART_TOK Expr {
                          $$ = new CVC3::Expr(VC->listExpr("_RESTART", *$2));
                          delete $2;
                        }
                ;
Dbg             :       DBG_TOK StringLiteral { 
                          $$ = new CVC3::Expr(VC->listExpr("_DBG", *$2));
			  delete $2;
                        }
                |       DBG_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DBG")));
		}
                ;
Trace           :       TRACE_TOK StringLiteral { 
                          $$ = new CVC3::Expr(VC->listExpr("_TRACE", *$2));
			  delete $2;
                        }
                |       UNTRACE_TOK StringLiteral { 
                          $$ = new CVC3::Expr(VC->listExpr("_UNTRACE", *$2));
			  delete $2;
                        }
                ;
Option          :       OPTION_TOK StringLiteral Numeral { 
                          $$ = new CVC3::Expr(VC->listExpr("_OPTION",  *$2, *$3));
			  delete $2;
			  delete $3;
                        }
                |       OPTION_TOK StringLiteral MINUS_TOK Numeral {
			  CVC3::Rational value= -$4->getRational();
                          CVC3::Expr e = CVC3::Expr(VC->ratExpr(value.toString()));
                          $$ = new CVC3::Expr(VC->listExpr("_OPTION",  *$2, e));
			  delete $2;
			  delete $4;
                        }
                |       OPTION_TOK StringLiteral StringLiteral { 
                          $$ = new CVC3::Expr(VC->listExpr("_OPTION",  *$2,  *$3));
			  delete $2;
			  delete $3;
                        }
                ;
Help            :       HELP_TOK StringLiteral { 
                          $$ = new CVC3::Expr(VC->listExpr("_HELP", *$2));
			  delete $2;
                        }
                |       HELP_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_HELP")));
		}
                ;

Transform       :       TRANSFORM_TOK Expr { 
                          $$ = new CVC3::Expr(VC->listExpr("_TRANSFORM", *$2));
			  delete $2;
                        }
                ;

Print           :       PRINT_TOK Expr { 
                          $$ = new CVC3::Expr(VC->listExpr("_PRINT", *$2));
			  delete $2;
                        }
                |       PRINT_TYPE_TOK Type { 
                          $$ = new CVC3::Expr(VC->listExpr("_PRINT", *$2));
			  delete $2;
                        }
                ;

Call            :       CALL_TOK Identifier Expr { 
                          $$ = new CVC3::Expr(VC->listExpr("_CALL", *$2, *$3));
			  delete $2;
			  delete $3;
                        }
                ;

Echo            :       ECHO_TOK StringLiteral { 
                          $$ = new CVC3::Expr(VC->listExpr("_ECHO", *$2));
			  delete $2;
                        }
                |       ECHO_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_ECHO")));
                        }
                ;

Include         :       INCLUDE_TOK StringLiteral { 
                          $$ = new CVC3::Expr(VC->listExpr("_INCLUDE",  *$2));
			  delete $2;
                        }
                ;

DumpCommand     :       DUMP_PROOF_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_PROOF")));
                        }
                |       DUMP_ASSUMPTIONS_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_ASSUMPTIONS")));
                        }
                |       DUMP_SIG_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_SIG")));
                        }
                |       DUMP_TCC_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_TCC")));
                        }
                |       DUMP_TCC_ASSUMPTIONS_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_TCC_ASSUMPTIONS")));
                        }
                |       DUMP_TCC_PROOF_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_TCC_PROOF")));
                        }
                |       DUMP_CLOSURE_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_CLOSURE")));
                        }
                |       DUMP_CLOSURE_PROOF_TOK { 
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_DUMP_CLOSURE_PROOF")));
                        }
                ;

Where           :       WHERE_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_WHERE")));
               		}
                |       ASSERTIONS_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_ASSERTIONS")));
               		}
                |       ASSUMPTIONS_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_ASSUMPTIONS")));
               		}
                |       COUNTEREXAMPLE_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_COUNTEREXAMPLE")));
               		}
                |       COUNTERMODEL_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_COUNTERMODEL")));
               		}
                ;
Push            :       PUSH_TOK Numeral { 
                          $$ = new CVC3::Expr(VC->listExpr("_PUSH", *$2));
			  delete $2;
                        }
                |       PUSH_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_PUSH")));
		        }
                |       PUSH_SCOPE_TOK Numeral { 
                          $$ = new CVC3::Expr(VC->listExpr("_PUSH_SCOPE", *$2));
			  delete $2;
                        }
                |       PUSH_SCOPE_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_PUSH_SCOPE")));
		        }
                ;
Pop             :       POP_TOK Numeral { 
                          $$ = new CVC3::Expr(VC->listExpr("_POP", *$2));
			  delete $2;
                        }
                |       POP_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_POP")));
		        }
                |       POP_SCOPE_TOK Numeral { 
                          $$ = new CVC3::Expr(VC->listExpr("_POP_SCOPE", *$2));
			  delete $2;
                        }
                |       POP_SCOPE_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_POP_SCOPE")));
		        }
                ;
PopTo           :       POPTO_TOK Numeral { 
                          $$ = new CVC3::Expr(VC->listExpr("_POPTO", *$2));
			  delete $2;
                        }
                |       POPTO_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_POPTO")));
		        }
                |       POPTO_SCOPE_TOK Numeral {
                          $$ = new CVC3::Expr(VC->listExpr("_POPTO_SCOPE", *$2));
			  delete $2;
                        }
                |       POPTO_SCOPE_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_POPTO_SCOPE")));
		        }
                |       RESET_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_RESET")));
		        }
                ;
Context         :       CONTEXT_TOK StringLiteral { 
                          $$ = new CVC3::Expr(VC->listExpr("_CONTEXT",  *$2));
			  delete $2;
                        }
                |       CONTEXT_TOK {
                          $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_CONTEXT")));
		        }
                ;
Forget          :       FORGET_TOK Identifier { 
                          $$ = new CVC3::Expr(VC->listExpr("_FORGET", *$2));
			  delete $2;
                        }
                ;
Get_Type        :       GET_TYPE_TOK Expr { 
                          $$ = new CVC3::Expr(VC->listExpr("_GET_TYPE", *$2));
			  delete $2;
                        }
                ;
Check_Type      :       CHECK_TYPE_TOK Expr ':' Type { 
                          $$ = new CVC3::Expr(VC->listExpr("_CHECK_TYPE",*$2, *$4));
			  delete $2;
			  delete $4;
                        }
                ;
Get_Child       :       GET_CHILD_TOK Expr Numeral { 
                          $$ = new CVC3::Expr(VC->listExpr("_GET_CHILD", *$2, *$3));
			  delete $2;
			  delete $3;
                        }
                ;
Get_Op          :       GET_OP_TOK Expr { 
                          $$ = new CVC3::Expr(VC->listExpr("_GET_CHILD", *$2));
			  delete $2;
                        }
                ;
Substitute      :       SUBSTITUTE_TOK Identifier ':' Type '=' Expr '[' Identifier ASSIGN_TOK Expr ']' { 
                          std::vector<CVC3::Expr> tmp;
			  tmp.push_back(*$2);
			  tmp.push_back(*$4);
			  tmp.push_back(*$6);
			  tmp.push_back(*$8);
			  tmp.push_back(*$10);
                          $$ = new CVC3::Expr(VC->listExpr("_SUBSTITUTE", tmp));
			  delete $2;
			  delete $4;
			  delete $6;
			  delete $8;
			  delete $10;
                        }
                ;
Identifier      :       ID_TOK
                        {
			  $$ = new CVC3::Expr(VC->idExpr(*$1));
			  delete $1;
			}
                ;
StringLiteral   :       STRINGLIT_TOK
                        {
			  $$ = new CVC3::Expr(VC->stringExpr(*$1));
			  delete $1;
			}
                ;
Numeral         :       NUMERAL_TOK
                        {
  			  $$ = new CVC3::Expr(VC->ratExpr((*$1)));
  			  delete $1;
			}
                ;

Binary          :       BINARY_TOK
                        {
			  $$ = new CVC3::Expr
			    (VC->listExpr("_BVCONST", VC->stringExpr(*$1)));
			  delete $1;
                        }
                ;


Hex             :       HEX_TOK
                        {
			  $$ = new CVC3::Expr
			    (VC->listExpr("_BVCONST", VC->stringExpr(*$1), VC->ratExpr(16)));
			  delete $1;
                        }
                ;


/* Grammar for Types */

Type		:	Identifier { $$ = $1; }
		|	TypeNotIdentifier { $$ = $1; }
		;

TypeNotIdentifier:      ArrayType { $$ = $1; }
		|	FunctionType { $$ = $1; }
                |	BasicType { $$ = $1; }
		|	SubrangeType { $$ = $1; }
		|	TupleType { $$ = $1; }
		|	RecordType { $$ = $1; }
		|	TypeLetExpr { $$ = $1; }
                |       BitvectorType {$$ = $1;}
                |       SubType { $$ = $1; }
                |       '(' Type ')' { $$ = $2; }
		;

TypeDef		:	Type { $$ = $1; }
		|	ScalarType { $$ = $1; }
		;

DataType	:       DATATYPE_TOK SingleDataTypes END_TOK
			{
			  $$ = new CVC3::Expr(
                            VC->listExpr("_TYPEDEF",
                                         VC->listExpr("_DATATYPE", *$2)));
			  delete $2;
			}
		;

SingleDataTypes :       SingleDataType
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
			}
		|	SingleDataTypes ',' SingleDataType
		        { 
			  $1->push_back(*$3); 
                          $$ = $1;
		          delete $3;
			}
		;

SingleDataType  :       Identifier '=' Constructors
                        {
			  $$ = new CVC3::Expr(VC->listExpr(*$1, VC->listExpr(*$3)));
			  delete $1;
			  delete $3;
                        }
                ;

Constructors	:	Constructor 
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1; 
			}
		|	Constructors MID_TOK Constructor 
		        { 
			  $1->push_back(*$3); 
                          $$ = $1; 
		          delete $3; 
			}
		;

Constructor	:	Identifier 
                        {
                          $$ = new CVC3::Expr(VC->listExpr(*$1));
			  delete $1; 
			}
		|	Identifier '(' VarDecls ')'
			{
                          CVC3::Expr tmp = VC->listExpr(*$3);
			  $$ = new CVC3::Expr(VC->listExpr(*$1, tmp));
			  delete $1; delete $3;
			}
		;

VarDecls	:	VarDecl
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
			}
		|	VarDecls ',' VarDecl 
                        {
			  $1->push_back(*$3);
			  $$ = $1; 
			  delete $3;
			}
		;

VarDecl		:	Identifier ':' Type
			{ 
			  $$ = new CVC3::Expr(VC->listExpr(*$1, *$3));
			  delete $1;
			  delete $3;
			}
		;

FunctionType	:	'[' Type ARROW_TOK Type ']'
			{
                          // Old style functions
                          $$ = new CVC3::Expr(VC->listExpr("_OLD_ARROW", *$2, *$4));
                          delete $2; delete $4;
			}
                |       Type ARROW_TOK Type
			{
			  std::vector<CVC3::Expr> temp;
			  temp.push_back(*$1);
			  temp.push_back(*$3);

			  $$ = new CVC3::Expr(VC->listExpr("_ARROW", temp));
			  delete $1; delete $3; 
			}
                |       '(' TypeList ')' ARROW_TOK Type
			{
			  $2->push_back(*$5);
			  $$ = new CVC3::Expr(VC->listExpr("_ARROW", *$2));
			  delete $2; delete $5; 
			}
		;

RecordType	:	SQHASH_TOK FieldDecls HASHSQ_TOK
			{
			  $$ = new CVC3::Expr(VC->listExpr(*$2));
			  delete $2;
			}
		;

FieldDecls	:	FieldDecl 
                        { 
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(VC->idExpr("_RECORD_TYPE"));
			  $$->push_back(*$1); 
			  delete $1; 
                        }
		|	FieldDecls ',' FieldDecl 
                        { 
			  $1->push_back(*$3); 
			  $$ = $1; 
			  delete $3;
			}
		;

FieldDecl	:	Identifier ':' Type 
			{
			  $$ = new CVC3::Expr(VC->listExpr(*$1, *$3));
			  delete $1;
			  delete $3;
			}
		;

TupleType	:	'[' TypeList ']' 
                         {
			   $$ = new CVC3::Expr(VC->listExpr("_TUPLE_TYPE", *$2));
			   delete $2;
			 }
		;

TypeList	:	Type ',' Type
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
                          $$->push_back(*$3);
			  delete $1;
                          delete $3;
			}
		|	TypeList ',' Type 
                        {
			  $1->push_back(*$3);
			  $$ = $1; 
			  delete $3;
			}
		;

/* IndexType       :       SubrangeType { $$ = $1; } */
/*                 |       Real /\* WART: maybe change to INTEGER when we */
/* 				get that working? *\/ */
/*                 |       Int */
/*                         { $$ = $1; } */
/*                 |       Identifier { $$ = $1; } */
/*                 ; */

ArrayType	:	ARRAY_TOK Type OF_TOK Type 
			{
			  $$ = new CVC3::Expr(VC->listExpr("_ARRAY", *$2, *$4));
			  delete $2;
			  delete $4;
			}
		;

ScalarType	:	'{' IDs '}'
			 {
			   std::vector<CVC3::Expr>::iterator theIter = $2->begin();
			   $2->insert(theIter, VC->idExpr("_SCALARTYPE"));
			   $$ = new CVC3::Expr(VC->listExpr(*$2));
			   delete $2;
			 }
		;

SubType         :       SUBTYPE_TOK '(' Expr ')'
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_SUBTYPE", *$3));
			  delete $3;
			}
                |       SUBTYPE_TOK '(' Expr ',' Expr ')'
                        {
                          $$ = new CVC3::Expr(VC->listExpr("_SUBTYPE", *$3, *$5));
                          delete $3;
                          delete $5;
                        }
                ;

BasicType	:       BOOLEAN_TOK 
                        {
			  $$ = new CVC3::Expr(VC->idExpr("_BOOLEAN"));
			}
		|	Real
		|       Int
		;
		
BitvectorType   :       BITVECTOR_TOK '(' Numeral ')'
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_BITVECTOR", *$3));
			  delete $3;
			}
                ;

Real            :       REAL_TOK
                        {
			  $$ = new CVC3::Expr(VC->idExpr("_REAL"));
			}
                ;

Int             :       INT_TOK
                        {
			  $$ = new CVC3::Expr(VC->idExpr("_INT"));
                        }
                ;
SubrangeType	:	'[' LeftBound DOTDOT_TOK RightBound ']'
			{
			  $$ = new CVC3::Expr(VC->listExpr("_SUBRANGE", *$2, *$4));
			  delete $2;
			  delete $4;
			}
		;

LeftBound	:	'_' 
                        {
			  $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_NEGINF")));
			}
		|	Numeral { $$ = $1; }
                |       MINUS_TOK Numeral {
                          CVC3::Rational value= -$2->getRational();
			  $$ = new CVC3::Expr(VC->ratExpr(value.toString()));
			  delete $2;
                        }
		;

RightBound	:	'_' 
                        {
			  $$ = new CVC3::Expr(VC->listExpr(VC->idExpr("_POSINF")));
			}
		|	Numeral { $$ = $1; }
                |       MINUS_TOK Numeral {
                          CVC3::Rational value= -$2->getRational();
			  $$ = new CVC3::Expr(VC->ratExpr(value.toString()));
			  delete $2;
                        }
		;

/* right recursive to eliminate a conflict.  Reverses order? */
reverseIDs	:	Identifier 
                        { 
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
			}
		|	Identifier ',' reverseIDs 
                        {
			  $3->push_back(*$1);
			  $$ = $3; 
			  delete $1;
			}
		;

IDs             :       reverseIDs
                        {
			  $$ = new std::vector<CVC3::Expr>($1->rbegin(),
							   $1->rend());
			  delete $1;
			}
                ;

/* Grammar for exprs */

Expr		:	Identifier { $$ = $1; }
		|	Numeral { $$ = $1; }
	        |       Binary { $$ = $1; }
	        |       Hex { $$ = $1; }
		|	Expr '(' Exprs ')'
			{
			  std::vector<CVC3::Expr> tmp;
			  tmp.push_back(*$1);
			  tmp.insert(tmp.end(), $3->begin(), $3->end());
			  $$ = new CVC3::Expr(VC->listExpr(tmp));
			  delete $1;
			  delete $3;
			}
                |       SIMULATE_TOK '(' Exprs ')'
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_SIMULATE", *$3));
			  delete $3;
			}
		|	Expr '[' Expr ']' 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_READ", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Expr '.' Identifier 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_RECORD_SELECT", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Expr '.' Numeral
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_TUPLE_SELECT", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Expr WITH_TOK Updates
			{
			  $$ = new CVC3::Expr(CVC3::PLprocessUpdates(*$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Lambda { $$ = $1; }
		|	QuantExpr { $$ = $1; }
		|	LetExpr { $$ = $1; }

		|	ArrayLiteral { $$ = $1; }

		|	RecordLiteral { $$ = $1; }
		|	TupleLiteral { $$ = $1; }
		|	Conditional { $$ = $1; }

		|	TRUELIT_TOK 
                        {
			  $$ = new CVC3::Expr(VC->idExpr("_TRUE_EXPR"));
			}
		|	FALSELIT_TOK
                        {
			  $$ = new CVC3::Expr(VC->idExpr("_FALSE_EXPR"));
			}

		|	MINUS_TOK Expr %prec UMINUS_TOK 
			{
			  if ($2->isRational())
			  {
			    CVC3::Rational value= -$2->getRational();
			    $$= new CVC3::Expr(VC->ratExpr(value.toString()));
			  }
			  else
			    $$ = new CVC3::Expr(VC->listExpr("_UMINUS", *$2));
			  delete $2;
			}
		|	NOT_TOK Expr 
			{
			  $$ = new CVC3::Expr(VC->listExpr("_NOT", *$2));
			  delete $2;
			}
		|	IS_INTEGER_TOK Expr 
			{
			  $$ = new CVC3::Expr(VC->listExpr("_IS_INTEGER", *$2));
			  delete $2;
			}
		|	TCC_TOK '(' Expr ')'
			{
			  $$ = new CVC3::Expr(VC->listExpr("_TCC", *$3));
			  delete $3;
			}
		|	Expr '=' Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_EQ", *$1, *$3));
			  delete $1;
			  delete $3;
			} 
		|	Expr NEQ_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_NEQ", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Expr XOR_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_XOR", *$1, *$3));
			  delete $1;
			  delete $3;
			} 
		|	OrExpr %prec OR_TOK
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_OR", *$1));
			  delete $1;
			} 
		|	AndExpr %prec AND_TOK
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_AND", *$1));
			  delete $1;
			}
		|	Expr IMPLIES_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_IMPLIES", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Expr IFF_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_IFF", *$1, *$3));
			  delete $1;
			  delete $3;
			} 
		|	Expr PLUS_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_PLUS", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Expr MINUS_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_MINUS", *$1, *$3));
			  delete $1;
			  delete $3;
			} 
                |       Expr MULT_TOK '(' Expr ',' Expr ')'
                        {
                          $$ = new CVC3::Expr(VC->listExpr("_TRANS_CLOSURE",
							   *$1, *$4, *$6));
			  delete $1;
			  delete $4;
			  delete $6;
			}
		|	Expr MULT_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_MULT", *$1, *$3));
			  delete $1;
			  delete $3;
			} 
		|	Expr POW_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_POW", *$3, *$1));
			  delete $1;
			  delete $3;
			}
		|	Expr DIV_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_DIVIDE", *$1, *$3));
			  delete $1;
			  delete $3;
			} 
// 		|	Expr INTDIV_TOK Expr 
//                         {
// 			  $$ = new CVC3::Expr(VC->listExpr("_INTDIV", *$1, *$3));
// 			  delete $1;
// 			  delete $3;
// 			} 
// 		|	Expr MOD_TOK Expr 
//                         {
// 			  $$ = new CVC3::Expr(VC->listExpr("_MOD", *$1, *$3));
// 			  delete $1;
// 			  delete $3;
// 			}
		|	Expr GT_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_GT", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Expr GE_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_GE", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	FLOOR_TOK '(' Expr ')'
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_FLOOR", *$3));
			  delete $3;
			}
		|	Expr LT_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_LT", *$1, *$3));
			  delete $1;
			  delete $3;
			}
		|	Expr LE_TOK Expr 
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_LE", *$1, *$3));
			  delete $1;
			  delete $3;
			}
                |       '(' Expr ')' 
                         {
			   $$ = $2;
			 }
	        |       BVNEG_TOK Expr
			{
			  $$ = new CVC3::Expr(VC->listExpr("_BVNEG", *$2));
			  delete $2;
			}
	        |       Expr '[' NUMERAL_TOK ':' NUMERAL_TOK ']'
			{
			  $$ = new CVC3::Expr
			    (VC->listExpr("_EXTRACT", VC->ratExpr(*$3),
                                          VC->ratExpr(*$5), *$1));
			  delete $1;
			  delete $3;
  			  delete $5;
			}
	        |       Expr BVAND_TOK Expr
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVAND", *$1, *$3));
			  delete $1;
			  delete $3;
			}
	        |       Expr MID_TOK Expr
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVOR", *$1, *$3)); 
			  delete $1;
			  delete $3;
			}
                |       Expr LEFTSHIFT_TOK NUMERAL_TOK
                        {
			  $$ = new CVC3::Expr
			    (VC->listExpr("_LEFTSHIFT", *$1, VC->ratExpr(*$3)));
			  delete $1;
			  delete $3;
                        }
                |       Expr RIGHTSHIFT_TOK NUMERAL_TOK
                        {
			  $$ = new CVC3::Expr
			    (VC->listExpr("_RIGHTSHIFT", *$1, VC->ratExpr(*$3)));
			  delete $1;
			  delete $3;
                        }
	        |       BVXOR_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVXOR", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       BVNAND_TOK '(' Expr ',' Expr ')' 
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVNAND", *$3, *$5));
			  delete $3;
			  delete $5;
			}
                |       BVNOR_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVNOR", *$3, *$5));
			  delete $3;
			  delete $5;
			}
                |       BVCOMP_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVCOMP", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       BVXNOR_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVXNOR", *$3, *$5));
			  delete $3;
			  delete $5;
			}
                |       SX_TOK '(' Expr ',' NUMERAL_TOK ')'
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_SX",*$3,VC->ratExpr(*$5)));
			  delete $3;
  			  delete $5;
		        }
                |       BVZEROEXTEND_TOK '(' Expr ',' NUMERAL_TOK ')'
                        {
                          $$ = new CVC3::Expr(VC->listExpr("_BVZEROEXTEND",VC->ratExpr(*$5),*$3));
			  delete $3;
  			  delete $5;
                        }
                |       BVREPEAT_TOK '(' Expr ',' NUMERAL_TOK ')'
                        {
                          $$ = new CVC3::Expr(VC->listExpr("_BVREPEAT",VC->ratExpr(*$5),*$3));
			  delete $3;
  			  delete $5;
                        }
                |       BVROTL_TOK '(' Expr ',' NUMERAL_TOK ')'
                        {
                          $$ = new CVC3::Expr(VC->listExpr("_BVROTL",VC->ratExpr(*$5),*$3));
			  delete $3;
  			  delete $5;
                        }
                |       BVROTR_TOK '(' Expr ',' NUMERAL_TOK ')'
                        {
                          $$ = new CVC3::Expr(VC->listExpr("_BVROTR",VC->ratExpr(*$5),*$3));
			  delete $3;
  			  delete $5;
                        }
	        |       BVLT_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVLT", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       BVGT_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVGT", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       BVLE_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVLE", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       BVGE_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVGE", *$3, *$5));
			  delete $3;
			  delete $5;
			}

	        |       BVSLT_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVSLT", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       BVSGT_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVSGT", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       BVSLE_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVSLE", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       BVSGE_TOK '(' Expr ',' Expr ')'
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_BVSGE", *$3, *$5));
			  delete $3;
			  delete $5;
			}
	        |       Expr CONCAT_TOK Expr
	                {
			  $$ = new CVC3::Expr(VC->listExpr("_CONCAT", *$1, *$3));
			  delete $1;
			  delete $3;
			}
                |      INTTOBV_TOK '(' Expr ',' NUMERAL_TOK ',' NUMERAL_TOK ')'
			{
			  $$ = new CVC3::Expr
			    (VC->listExpr("_INTTOBV", *$3, VC->ratExpr(*$5),
					  VC->ratExpr(*$7)));
			  delete $3;
			  delete $5;
			  delete $7;
			}
                |       BVTOINT_TOK '(' Expr ')'
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_BVTOINT", *$3));
			  delete $3;
                        }
                |       BOOLEXTRACT_TOK '(' Expr ',' NUMERAL_TOK ')'
                        {
			  //FIXME: this function is not to be exposed
			  //to the user counterexamples containing
			  //this function can be translated into
			  //BV-EXTRACT and comparison with 0 or 1
			  $$ = new CVC3::Expr(VC->listExpr("_BOOLEXTRACT", *$3,
                                              VC->ratExpr(*$5)));
			  delete $3;
  			  delete $5;
                        }
                |       BVPLUS_TOK '(' NUMERAL_TOK ',' Exprs ')'
                        {
			  std::vector<CVC3::Expr> k;
			  k.push_back(VC->ratExpr(*$3));
			  k.insert(k.end(), $5->begin(), $5->end()); 
			  $$ = new CVC3::Expr(VC->listExpr("_BVPLUS", k));
			  delete $3;
			  delete $5;
                        }
                |       BVSUB_TOK '(' NUMERAL_TOK ',' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVSUB", VC->ratExpr(*$3), *$5, *$7));
			  delete $3;
			  delete $5;
			  delete $7;
                        }
                |       BVUDIV_TOK '(' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVUDIV", *$3, *$5));
			  delete $3;
			  delete $5;
                        }
                |       BVSDIV_TOK '(' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVSDIV", *$3, *$5));
			  delete $3;
			  delete $5;
                        }
                |       BVUREM_TOK '(' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVUREM", *$3, *$5));
			  delete $3;
			  delete $5;
                        }
                |       BVSREM_TOK '(' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVSREM", *$3, *$5));
			  delete $3;
			  delete $5;
                        }
                |       BVSMOD_TOK '(' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVSMOD", *$3, *$5));
			  delete $3;
			  delete $5;
                        }
                |       BVSHL_TOK '(' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVSHL", *$3, *$5));
			  delete $3;
			  delete $5;
                        }
                |       BVASHR_TOK '(' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVASHR", *$3, *$5));
			  delete $3;
			  delete $5;
                        }
                |       BVLSHR_TOK '(' Expr ',' Expr ')'
                        {
			  $$ =  new CVC3::Expr
                           (VC->listExpr("_BVLSHR", *$3, *$5));
			  delete $3;
			  delete $5;
                        }
                |       BVUMINUS_TOK '(' Expr ')'
                        {
			  $$ =  new CVC3::Expr(VC->listExpr("_BVUMINUS", *$3));
			  delete $3;
                        }
                |       BVMULT_TOK '(' NUMERAL_TOK ',' Expr ',' Expr ')'
                        {
			  $$ = new CVC3::Expr
			    (VC->listExpr("_BVMULT", VC->ratExpr(*$3), *$5, *$7));
			  delete $3;
			  delete $5;
			  delete $7;
                        }
                |       DISTINCT_TOK '(' Exprs ')'
                        {
                          $$ = new CVC3::Expr(VC->listExpr("_DISTINCT", *$3));
                          delete $3;
                        }
		;
AndExpr		:      AndExpr AND_TOK Expr
                        {
			  $1->push_back(*$3);
                          $$ = $1;
			  delete $3;
			}

                 |      Expr AND_TOK Expr
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  $$->push_back(*$3);
			  delete $1;
			  delete $3;
                        }
                ;


OrExpr		:       OrExpr OR_TOK Expr
                        {
			  $1->push_back(*$3);
                          $$ = $1;
			  delete $3;
			}

                |	Expr OR_TOK Expr
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  $$->push_back(*$3);
			  delete $1;
			  delete $3;
                        }
                ;
Conditional	:	IF_TOK Expr THEN_TOK Expr ElseRest 
			{
			  $5->push_back(VC->listExpr(*$2, *$4));
			  $5->push_back(VC->idExpr("_COND"));
			  /* at this point, the list for ElseRest is 
			     in reverse order from what it should be. */
			  std::vector<CVC3::Expr> tmp;
			  tmp.insert(tmp.end(), $5->rbegin(), $5->rend());
			  $$ = new CVC3::Expr(VC->listExpr(tmp));
			  delete $2;
			  delete $4;
			  delete $5;
			}
		;

ElseRest	:	ELSE_TOK Expr ENDIF_TOK 
                        {
			  $$ = new std::vector<CVC3::Expr>;
	                  $$->push_back(VC->listExpr("_ELSE",*$2));
			  delete $2;
			}
		|	ELSIF_TOK Expr THEN_TOK Expr ElseRest 
			{
			  /* NOTE that we're getting the list built
			     up in the reverse order here.  We'll fix
			     things when we produce a Conditional. */
			  $5->push_back(VC->listExpr(*$2, *$4));
			  $$ = $5;
			  delete $2;
			  delete $4;
			}
		;

Exprs		:	Expr 
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
			}
		|	Exprs ',' Expr 
                        {
			  $1->push_back(*$3);
			  $$ = $1; 
			  delete $3;
			}
		;


Pattern		:	PATTERN_TOK '(' Exprs ')' ':'
                        {
			  $$ = $3;
			}

Patterns	:	Pattern
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(VC->listExpr(*$1));
			  delete $1;
			}
		|	Patterns Pattern
                        {
			  $1->push_back(VC->listExpr(*$2));
			  $$ = $1; 
			  delete $2;
			}
		;

Update          :       UpdatePositionNode ASSIGN_TOK Expr
                        {
			  $$ = new CVC3::Expr(VC->listExpr(*$1, *$3));
			  delete $1;
			  delete $3;
			}
                ;

Updates         :       Update
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
			}
                |       Updates ',' Update
                        {
			  $$->push_back(*$3);
			  delete $3;
			}
                ;

UpdatePositionNode :    UpdatePosition 
                        {
			  $$ = new CVC3::Expr(VC->listExpr(*$1));
			  delete $1;
			}
                ;

UpdatePosition	:	'[' Expr ']' 
			{
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(VC->listExpr("_READ", *$2));
			  delete $2;
			}
                |       Identifier
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
			}
		|	'.' Identifier 
			{
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(VC->listExpr("_RECORD_SELECT", *$2));
			  delete $2;
			}
		|	'.' Numeral 
			{
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(VC->listExpr("_TUPLE_SELECT", *$2));
			  delete $2;
			}
 		|	UpdatePosition '[' Expr ']' 
                        {
			  $1->push_back(VC->listExpr("_READ", *$3));
			  $$ = $1;
			  delete $3;
			}
		|	UpdatePosition Identifier 
                        {
			  $1->push_back(*$2);
			  $$ = $1;
			  delete $2;
			}
		|	UpdatePosition '.' Identifier 
                        {
			  $1->push_back(VC->listExpr("_RECORD_SELECT",*$3));
			  $$ = $1;
			  delete $3;
			}
		|	UpdatePosition '.' Numeral 
                        {
			  $1->push_back(VC->listExpr("_TUPLE_SELECT", *$3));
			  $$ = $1;
			  delete $3;
			}
		;

Lambda		:	LAMBDA_TOK '(' BoundVarDecls ')' ':' Expr 
                        %prec ASSIGN_TOK
			{
			  $$ = new CVC3::Expr(VC->listExpr("_LAMBDA", 
			                                   VC->listExpr(*$3), (*$6)));
			  delete $3;
			  delete $6;
			}
                ;
QuantExpr	:	FORALL_TOK '(' BoundVarDecls ')' ':'  Expr
		        %prec FORALL_TOK
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_FORALL", 
			                                   VC->listExpr(*$3), *$6));
			  delete $3;
			  delete $6;
			}
                |	FORALL_TOK '(' BoundVarDecls ')' ':' Patterns Expr
		        %prec FORALL_TOK
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_FORALL", 
			                                   VC->listExpr(*$3), *$7,
							   VC->listExpr(*$6)));
			  delete $3;
			  delete $6;
			  delete $7;
			}
		|	EXISTS_TOK '(' BoundVarDecls ')' ':'  Expr
		        %prec EXISTS_TOK
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_EXISTS", 
			                                   VC->listExpr(*$3), (*$6)));
			  delete $3;
			  delete $6;
			}
		;
                |	EXISTS_TOK '(' BoundVarDecls ')' ':' Patterns Expr
		        %prec EXISTS_TOK
                        {
			  $$ = new CVC3::Expr(VC->listExpr("_EXISTS", 
			                                   VC->listExpr(*$3), *$7,
							   VC->listExpr(*$6)));
			  delete $3;
			  delete $6;
			  delete $7;
			}

ArrayLiteral		: ARRAY_TOK '(' BoundVarDecl ')' ':' Expr 
                        %prec ASSIGN_TOK
			{
			  $$ = new CVC3::Expr
			    (VC->listExpr("_ARRAY_LITERAL", *$3, *$6));
			  delete $3;
			  delete $6;
			}
                ;
RecordLiteral	:	PARENHASH_TOK RecordEntries HASHPAREN_TOK 
			{
			  $2->insert($2->begin(), VC->idExpr("_RECORD"));
			  $$ = new CVC3::Expr(VC->listExpr(*$2));
			  delete $2;
			}
		;

RecordEntries	:	RecordEntry 
                        { 
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1); 
			  delete $1;
			}
		|	RecordEntries ',' RecordEntry 
                        { 
			  $1->push_back(*$3);
			  $$ = $1; 
			  delete $3;
			}
		;

RecordEntry	:	Identifier ASSIGN_TOK Expr 
			{
			  $$ = new CVC3::Expr(VC->listExpr(*$1, *$3));
			  delete $1;
			  delete $3;
			}
		;

TupleLiteral	:	'(' Exprs ',' Expr ')' 
                        {
			  $2->push_back(*$4);
			  $2->insert($2->begin(),VC->idExpr("_TUPLE"));
			  $$ = new CVC3::Expr(VC->listExpr(*$2));
			  delete $2;
			  delete $4;
			}
		;

LetDeclsNode    :       LetDecls
                        { 
			  $$ = new CVC3::Expr(VC->listExpr(*$1));
			  delete $1;
			}
                ;
LetDecls	:	LetDecl { 
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
                        }
		|	LetDecls ',' LetDecl 
                        { 
			  $1->push_back(*$3);
			  $$ = $1; 
			  delete $3;
			}
		;

LetDecl		:	Identifier '=' Expr 
			{ 
			  $$ = new CVC3::Expr(VC->listExpr(*$1,*$3));
			  delete $1;
			  delete $3;
			}
                |       Identifier ':' Type '=' Expr
			{ 
			  $$ = new CVC3::Expr(VC->listExpr(*$1,*$5));
			  delete $1;
			  delete $3;
			  delete $5;
			}
		;

LetExpr		:	LET_TOK LetDeclsNode IN_TOK Expr 
			{
			  $$ = new CVC3::Expr(VC->listExpr("_LET", *$2, *$4));
			  delete $2;
			  delete $4;
			}
		;

TypeLetDeclsNode :      TypeLetDecls
                        { 
			  $$ = new CVC3::Expr(VC->listExpr(*$1));
			  delete $1;
			}
                ;
TypeLetDecls	:	TypeLetDecl { 
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
                        }
		|	TypeLetDecls ',' TypeLetDecl 
                        { 
			  $1->push_back(*$3);
			  $$ = $1; 
			  delete $3;
			}
		;

TypeLetDecl	:	Identifier '=' Type 
			{ 
			  $$ = new CVC3::Expr(VC->listExpr(*$1, *$3));
			  delete $1;
			  delete $3;
			}
                |       Identifier ':' TYPE_TOK '=' Type
			{ 
			  $$ = new CVC3::Expr(VC->listExpr(*$1,*$5));
			  delete $1;
			  delete $5;
			}
		;

TypeLetExpr	:	LET_TOK TypeLetDeclsNode IN_TOK Type 
			{
			  $$ = new CVC3::Expr(VC->listExpr("_LET", *$2, *$4));
			  delete $2;
			  delete $4;
			}
		;

BoundVarDecl	:	IDs ':' Type 
			{
			  $1->push_back(*$3);
			  delete $3;
			  $$ = new CVC3::Expr(VC->listExpr(*$1));
			  delete $1;
			
			}
		;

BoundVarDecls	:	BoundVarDecl 
                        {
			  $$ = new std::vector<CVC3::Expr>;
			  $$->push_back(*$1);
			  delete $1;
			}
		|	BoundVarDecls ',' BoundVarDecl 
                        {
			  $1->push_back(*$3);
			  $$ = $1; 
			  delete $3;
			}
		;

BoundVarDeclNode:	BoundVarDecls 
                        { 
			  $$ = new CVC3::Expr(VC->listExpr(*$1));
			  delete $1;
			}
                ;

ConstDecl	:	Identifier ':' Type '=' Expr 
			{
			  $$ = new CVC3::Expr(VC->listExpr("_CONST",
							   *$1, *$3, *$5));
			  delete $1;
			  delete $3;
			  delete $5;
			}
		|	Identifier ':' Type
			{
			  $$ =new CVC3::Expr
			    (VC->listExpr("_CONST", VC->listExpr(*$1), *$3));
			  delete $1;
			  delete $3;
			}
		|	Identifier '(' BoundVarDeclNode ')' ':' Type '=' Expr
			{
			  std::vector<CVC3::Expr> tmp;
			  tmp.push_back(VC->idExpr("_DEFUN"));
			  tmp.push_back(*$1);
			  tmp.push_back(*$3);
			  tmp.push_back(*$6);
			  tmp.push_back(*$8);
			  $$ = new CVC3::Expr(VC->listExpr(tmp));
			  delete $1;
			  delete $3;
			  delete $6;
			  delete $8;
			}
		|	Identifier '(' BoundVarDeclNode ')' ':' Type
			{
			  std::vector<CVC3::Expr> tmp;
			  tmp.push_back(VC->idExpr("_DEFUN"));
			  tmp.push_back(*$1);
			  tmp.push_back(*$3);
			  tmp.push_back(*$6);
			  $$ = new CVC3::Expr(VC->listExpr(tmp));
			  delete $1;
			  delete $3;
			  delete $6;
			}
                |       Identifier ',' IDs ':' Type
                        {
			  $3->insert($3->begin(), *$1);
			  $$ = new CVC3::Expr(VC->listExpr("_CONST", VC->listExpr(*$3), *$5));
			  delete $1;
			  delete $3;
			  delete $5;
			}
		;

TypeDecl        :       DataType { $$ = $1; }
                |       Identifier ':' TYPE_TOK '=' TypeDef 
			{
			  $$ = new CVC3::Expr(VC->listExpr("_TYPEDEF", *$1, *$5));
			  delete $1;
			  delete $5;
			}
                |       Identifier ':' TYPE_TOK
			{
			  $$ =new CVC3::Expr(VC->listExpr("_TYPE", *$1));
			  delete $1;
			}
                |       Identifier ',' IDs ':' TYPE_TOK
                        {
			  std::vector<CVC3::Expr> tmp;
			  tmp.push_back(*$1);
			  tmp.insert(tmp.end(), $3->begin(), $3->end());
			  $$ = new CVC3::Expr(VC->listExpr("_TYPE", tmp));
			  delete $1;
			  delete $3;
			}
		;
%%
