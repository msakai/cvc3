%{
/*****************************************************************************/
/*!
 * \file PL.lex
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

#include <iostream>
#include "parser_temp.h"
#include "expr_manager.h" /* for the benefit of parsePL_defs.h */
#include "parsePL_defs.h"
#include "debug.h"

namespace CVC3 {
  extern ParserTemp* parserTemp;
}

extern int PL_inputLine;
extern char *PLtext;

extern int PLerror (const char *msg);

static int PLinput(std::istream& is, char* buf, int size) {
  int res;
  if(is) {
    // If interactive, read line by line; otherwise read as much as we
    // can gobble
    if(CVC3::parserTemp->interactive) {
      // Print the current prompt
      std::cout << CVC3::parserTemp->getPrompt() << std::flush;
      // Set the prompt to "middle of the command" one
      CVC3::parserTemp->setPrompt2();
      // Read the line
      is.getline(buf, size-1);
    } else // Set the terminator char to 0
      is.getline(buf, size-1, 0);
    // If failbit is set, but eof is not, it means the line simply
    // didn't fit; so we clear the state and keep on reading.
    bool partialStr = is.fail() && !is.eof();
    if(partialStr)
      is.clear();

    for(res = 0; res<size && buf[res] != 0; res++);
    if(res == size) PLerror("Lexer bug: overfilled the buffer");
    if(!partialStr) { // Insert \n into the buffer
      buf[res++] = '\n';
      buf[res] = '\0';
    }
  } else {
    res = YY_NULL;
  }
  return res;
}

// Redefine the input buffer function to read from an istream
#define YY_INPUT(buf,result,max_size) \
  result = PLinput(*CVC3::parserTemp->is, buf, max_size);

int PL_bufSize() { return YY_BUF_SIZE; }
YY_BUFFER_STATE PL_buf_state() { return YY_CURRENT_BUFFER; }

/* some wrappers for methods that need to refer to a struct.
   These are used by CVC3::Parser. */
void *PL_createBuffer(int sz) {
  return (void *)PL_create_buffer(NULL, sz);
}
void PL_deleteBuffer(void *buf_state) {
  PL_delete_buffer((struct yy_buffer_state *)buf_state);
}
void PL_switchToBuffer(void *buf_state) {
  PL_switch_to_buffer((struct yy_buffer_state *)buf_state);
}
void *PL_bufState() {
  return (void *)PL_buf_state();
}

void PL_setInteractive(bool is_interactive) {
  yy_set_interactive(is_interactive);
}

// File-static (local to this file) variables and functions
static std::string _string_lit;

 static char escapeChar(char c) {
   switch(c) {
   case 'n': return '\n';
   case 't': return '\t';
   default: return c;
   }
 }

// for now, we don't have subranges.  
//
// ".."		{ return DOTDOT_TOK; }
/*OPCHAR	(['!#?\_$&\|\\@])*/

%}

%option noyywrap
%option nounput
%option noreject
%option noyymore
%option yylineno

%x	COMMENT
%x	STRING_LITERAL

LETTER	([a-zA-Z])
HEX     ([0-9a-fA-F])
BITS    ([0-1])
DIGIT	([0-9])
OPCHAR	(['?\_$~])
ANYTHING ({LETTER}|{DIGIT}|{OPCHAR})

%%

[\n]            { CVC3::parserTemp->lineNum++; }

[ \t\r\f]	{ /* skip whitespace */ }

0bin{BITS}+	{PLlval.str = new std::string(PLtext+4);return BINARY_TOK; 
		}
0hex{HEX}+      {PLlval.str = new std::string(PLtext+4);return HEX_TOK; 
		}
{DIGIT}+	{PLlval.str = new std::string(PLtext);return NUMERAL_TOK; 
		}

"%"		{ BEGIN COMMENT; }
<COMMENT>"\n"	{ BEGIN INITIAL; /* return to normal mode */ 
                  CVC3::parserTemp->lineNum++; }
<COMMENT>.	{ /* stay in comment mode */ }

<INITIAL>"\""		{ BEGIN STRING_LITERAL; 
                          _string_lit.erase(_string_lit.begin(),
                                            _string_lit.end()); }
<STRING_LITERAL>"\\".	{ /* escape characters (like \n or \") */
                          _string_lit.insert(_string_lit.end(),
                                             escapeChar(PLtext[1])); }
<STRING_LITERAL>"\""	{ BEGIN INITIAL; /* return to normal mode */ 
			  PLlval.str = new std::string(_string_lit);
                          return STRINGLIT_TOK; }
<STRING_LITERAL>.	{ _string_lit.insert(_string_lit.end(),*PLtext); }

[()[\]{},.;:'!#?_=]	{ return PLtext[0]; }

".."            { return DOTDOT_TOK; }
":="		{ return ASSIGN_TOK; }
"/="		{ return NEQ_TOK; }
"=>"		{ return IMPLIES_TOK; }
"<=>"		{ return IFF_TOK; }
"+"		{ return PLUS_TOK; }
"-"		{ return MINUS_TOK; }
"*"		{ return MULT_TOK; }
"^"		{ return POW_TOK; }
"/"		{ return DIV_TOK; }
"MOD"		{ return MOD_TOK; }
"DIV"		{ return INTDIV_TOK; }
"<"		{ return LT_TOK; }
"<="		{ return LE_TOK; }
">"		{ return GT_TOK; }
">="		{ return GE_TOK; }
"FLOOR"         { return FLOOR_TOK; }

"[#"		{ return SQHASH_TOK; }
"#]"		{ return HASHSQ_TOK; }
"(#"		{ return PARENHASH_TOK; }
"#)"		{ return HASHPAREN_TOK; }
"->"		{ return ARROW_TOK; }
"ARROW"		{ return ARROW_TOK; }
"@"             { return CONCAT_TOK;}
"~"             { return BVNEG_TOK;}
"&"             { return BVAND_TOK;}
"|"             { return MID_TOK;}
"BVXOR"         { return BVXOR_TOK;}
"BVNAND"        { return BVNAND_TOK;}
"BVNOR"         { return BVNOR_TOK;}
"BVCOMP"        { return BVCOMP_TOK;}
"BVXNOR"        { return BVXNOR_TOK;}
"<<"            { return LEFTSHIFT_TOK;}
">>"            { return RIGHTSHIFT_TOK;}
"BVSLT"         { return BVSLT_TOK;}
"BVSGT"         { return BVSGT_TOK;}
"BVSLE"         { return BVSLE_TOK;}
"BVSGE"         { return BVSGE_TOK;}
"SX"            { return SX_TOK;} 
"BVZEROEXTEND"  { return BVZEROEXTEND_TOK;} 
"BVREPEAT"      { return BVREPEAT_TOK;} 
"BVROTL"        { return BVROTL_TOK;} 
"BVROTR"        { return BVROTR_TOK;} 
"BVLT"          { return BVLT_TOK;}
"BVGT"          { return BVGT_TOK;}
"BVLE"          { return BVLE_TOK;}
"BVGE"          { return BVGE_TOK;}

"DISTINCT"      { return DISTINCT_TOK; }
"BVTOINT"       { return BVTOINT_TOK;}
"INTTOBV"       { return INTTOBV_TOK;}
"BOOLEXTRACT"   { return BOOLEXTRACT_TOK;}
"BVPLUS"        { return BVPLUS_TOK;}
"BVUDIV"        { return BVUDIV_TOK;}
"BVSDIV"        { return BVSDIV_TOK;}
"BVUREM"        { return BVUREM_TOK;}
"BVSREM"        { return BVSREM_TOK;}
"BVSMOD"        { return BVSMOD_TOK;}
"BVSHL"         { return BVSHL_TOK;}
"BVASHR"        { return BVASHR_TOK;}
"BVLSHR"        { return BVLSHR_TOK;}
"BVSUB"         { return BVSUB_TOK;}
"BVUMINUS"      { return BVUMINUS_TOK;}
"BVMULT"        { return BVMULT_TOK;}
"AND"		{ return AND_TOK; }
"ARRAY"		{ return ARRAY_TOK; }
"BOOLEAN"	{ return BOOLEAN_TOK; }
"DATATYPE"	{ return DATATYPE_TOK; }
"ELSE"		{ return ELSE_TOK; }
"ELSIF"		{ return ELSIF_TOK; }
"END"		{ return END_TOK; }
"ENDIF"		{ return ENDIF_TOK; }
"EXISTS"	{ return EXISTS_TOK; }
"FALSE"		{ return FALSELIT_TOK; }
"FORALL"	{ return FORALL_TOK; }
"IF"		{ return IF_TOK; }
"IN"		{ return IN_TOK; }
"LAMBDA"	{ return LAMBDA_TOK; }
"SIMULATE"	{ return SIMULATE_TOK; }
"LET"		{ return LET_TOK; }
"NOT"		{ return NOT_TOK; }
"IS_INTEGER"	{ return IS_INTEGER_TOK; }
"OF"		{ return OF_TOK; }
"OR"		{ return OR_TOK; }
"REAL"		{ return REAL_TOK; }
"INT"           { return INT_TOK;}
"SUBTYPE"       { return SUBTYPE_TOK;}
"BITVECTOR"     { return BITVECTOR_TOK;}

"THEN"		{ return THEN_TOK; }
"TRUE"		{ return TRUELIT_TOK; }
"TYPE"		{ return TYPE_TOK; }
"WITH"		{ return WITH_TOK; }
"XOR"		{ return XOR_TOK; }
"TCC"		{ return TCC_TOK; }
"PATTERN"       { return PATTERN_TOK; }

"ARITH_VAR_ORDER" { return ARITH_VAR_ORDER_TOK; }
"ASSERT"	{ return ASSERT_TOK; }
"QUERY"	        { return QUERY_TOK; }
"CHECKSAT"      { return CHECKSAT_TOK; }
"CONTINUE"      { return CONTINUE_TOK; }
"RESTART"       { return RESTART_TOK; }
"DBG"	        { return DBG_TOK; }
"TRACE"	        { return TRACE_TOK; }
"UNTRACE"       { return UNTRACE_TOK; }
"OPTION"        { return OPTION_TOK; }
"HELP"	        { return HELP_TOK; }
"TRANSFORM"	{ return TRANSFORM_TOK; }
"PRINT"	        { return PRINT_TOK; }
"PRINT_TYPE"    { return PRINT_TYPE_TOK; }
"CALL"	        { return CALL_TOK; }
"ECHO"	        { return ECHO_TOK; }
"INCLUDE"       { return INCLUDE_TOK; }
"DUMP_ASSUMPTIONS"   { return DUMP_ASSUMPTIONS_TOK; }
"DUMP_PROOF"    { return DUMP_PROOF_TOK; }
"DUMP_SIG"      { return DUMP_SIG_TOK; }
"DUMP_TCC"      { return DUMP_TCC_TOK; }
"DUMP_TCC_ASSUMPTIONS" { return DUMP_TCC_ASSUMPTIONS_TOK; }
"DUMP_TCC_PROOF" { return DUMP_TCC_PROOF_TOK; }
"DUMP_CLOSURE"  { return DUMP_CLOSURE_TOK; }
"DUMP_CLOSURE_PROOF" { return DUMP_CLOSURE_PROOF_TOK; }
"WHERE"         { return WHERE_TOK; }
"ASSERTIONS"    { return ASSERTIONS_TOK; }
"ASSUMPTIONS"   { return ASSUMPTIONS_TOK; }
"COUNTEREXAMPLE" { return COUNTEREXAMPLE_TOK; }
"COUNTERMODEL"  { return COUNTERMODEL_TOK; }
"PUSH"          { return PUSH_TOK; }
"POP"           { return POP_TOK; }
"POPTO"         { return POPTO_TOK; }
"PUSH_SCOPE"    { return PUSH_SCOPE_TOK; }
"POP_SCOPE"     { return POP_SCOPE_TOK; }
"POPTO_SCOPE"   { return POPTO_SCOPE_TOK; }
"RESET"         { return RESET_TOK; }
"CONTEXT"       { return CONTEXT_TOK; }
"FORGET"        { return FORGET_TOK; }
"GET_TYPE"      { return GET_TYPE_TOK; }
"CHECK_TYPE"    { return CHECK_TYPE_TOK; }
"GET_CHILD"     { return GET_CHILD_TOK; }
"GET_OP"        { return GET_OP_TOK; }
"SUBSTITUTE"    { return SUBSTITUTE_TOK; }

(({LETTER})|(_)({ANYTHING}))({ANYTHING})* {  PLlval.str = new std::string(PLtext); return ID_TOK; }

<<EOF>>                                 { return DONE_TOK; }

. { PLerror("Illegal input character."); }
%%

