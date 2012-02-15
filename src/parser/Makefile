MODULE = parser

LIBRARY=libparser.a

# Do not optimize the parser code - it compiles forever in some gcc versions
EXTRAFLAGS = -O0

TRANSIENT_CPP = \
 parsePL.cpp lexPL.cpp \
 parseLisp.cpp lexLisp.cpp \
 parsesmtlib.cpp lexsmtlib.cpp

TRANSIENT = $(TRANSIENT_CPP) \
  parsePL_defs.h \
  parseLisp_defs.h \
  parsesmtlib_defs.h

SRC = $(TRANSIENT_CPP) parser.cpp

HEADERS = parser_temp.h

# The actual source files for the parser that we want to include in a
# distribution
SRC_ORIG = PL.lex PL.y Lisp.lex Lisp.y smtlib.lex smtlib.y parser.cpp

include ../../Makefile.local

##################################################
# Rules for transient files
##################################################
lexPL.cpp:	PL.lex parsePL_defs.h
		$(LEX) $(LFLAGS) -I -PPL PL.lex
		@mv lex.PL.c lexPL.cpp

parsePL_defs.h	\
parsePL.cpp:	PL.y
		$(YACC) $(YFLAGS) -p PL --debug -v PL.y
		@mv y.tab.c parsePL.cpp
		@mv y.tab.h parsePL_defs.h


lexLisp.cpp:	Lisp.lex parseLisp_defs.h
		$(LEX) $(LFLAGS) -I -PLisp Lisp.lex
		@mv lex.Lisp.c lexLisp.cpp

parseLisp_defs.h \
parseLisp.cpp:	Lisp.y
		$(YACC) $(YFLAGS) -p Lisp --debug -v Lisp.y
		@mv y.tab.c parseLisp.cpp
		@mv y.tab.h parseLisp_defs.h


lexsmtlib.cpp:	smtlib.lex parsesmtlib_defs.h
		$(LEX) $(LFLAGS) -I -Psmtlib smtlib.lex
		@mv lex.smtlib.c lexsmtlib.cpp

parsesmtlib_defs.h \
parsesmtlib.cpp:	smtlib.y
		$(YACC) $(YFLAGS) -p smtlib --debug -v smtlib.y
		@mv y.tab.c parsesmtlib.cpp
		@mv y.tab.h parsesmtlib_defs.h


