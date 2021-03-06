MODULE = parser

LIBRARY=libparser.a

# Do not optimize the parser code - it compiles forever in some gcc versions
EXTRAFLAGS = -O0

TRANSIENT_CPP = \
 parsePL.cpp lexPL.cpp \
 parseLisp.cpp lexLisp.cpp \
 parsesmtlib.cpp lexsmtlib.cpp \
 parsesmtlib2.cpp lexsmtlib2.cpp

TRANSIENT = $(TRANSIENT_CPP) \
  parsePL_defs.h parsePL.output \
  parseLisp_defs.h parseLisp.output \
  parsesmtlib_defs.h parsesmtlib.output \
  parsesmtlib2_defs.h parsesmtlib2.output

SRC = $(TRANSIENT_CPP) parser.cpp

HEADERS = parser_temp.h

# The actual source files for the parser that we want to include in a
# distribution
SRC_ORIG = PL.lex PL.y Lisp.lex Lisp.y smtlib.lex smtlib.y smtlib2.lex smtlib2.y parser.cpp

include ../../Makefile.local

##################################################
# Rules for transient files
##################################################
lexPL.cpp:      PL.lex parsePL_defs.h
		$(LEX) $(LFLAGS) -I -PPL -olexPL.cpp PL.lex

parsePL_defs.h: parsePL.cpp

parsePL.cpp:    PL.y
		$(YACC) $(YFLAGS) -o parsePL.cpp -p PL --debug -v PL.y
		@if [ -f parsePL.cpp.h ]; then mv parsePL.cpp.h parsePL.hpp; fi
		@mv parsePL.hpp parsePL_defs.h

lexLisp.cpp:    Lisp.lex parseLisp_defs.h
		$(LEX) $(LFLAGS) -I -PLisp -olexLisp.cpp Lisp.lex

parseLisp_defs.h: parseLisp.cpp

parseLisp.cpp:  Lisp.y
		$(YACC) $(YFLAGS) -o parseLisp.cpp -p Lisp --debug -v Lisp.y
		@if [ -f parseLisp.cpp.h ]; then mv parseLisp.cpp.h parseLisp.hpp; fi
		@mv parseLisp.hpp parseLisp_defs.h

lexsmtlib.cpp:  smtlib.lex parsesmtlib_defs.h
		$(LEX) $(LFLAGS) -I -Psmtlib -olexsmtlib.cpp smtlib.lex

parsesmtlib_defs.h: parsesmtlib.cpp

parsesmtlib.cpp: smtlib.y
		$(YACC) $(YFLAGS) -o parsesmtlib.cpp -p smtlib --debug -v smtlib.y
		@if [ -f parsesmtlib.cpp.h ]; then mv parsesmtlib.cpp.h parsesmtlib.hpp; fi
		@mv parsesmtlib.hpp parsesmtlib_defs.h

lexsmtlib2.cpp:  smtlib2.lex parsesmtlib2_defs.h
		$(LEX) $(LFLAGS) -I -Psmtlib2 -olexsmtlib2.cpp smtlib2.lex

parsesmtlib2_defs.h: parsesmtlib2.cpp

parsesmtlib2.cpp: smtlib2.y
		$(YACC) $(YFLAGS) -o parsesmtlib2.cpp -p smtlib2 --debug -v smtlib2.y
		@if [ -f parsesmtlib2.cpp.h ]; then mv parsesmtlib2.cpp.h parsesmtlib2.hpp; fi
		@mv parsesmtlib2.hpp parsesmtlib2_defs.h
