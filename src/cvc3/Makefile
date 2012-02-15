##################################################
# About this Makefile
#
# This Makefile depends on Makefile.opts
##################################################

MODULE = cvc3

SRC =   main.cpp

EXECUTABLE = $(PROJECTNAME)

EXTRAFLAGS = -DVERSION=\"$(VERSION)\"

LD_LIBS = -l$(PROJECTNAME)

ifneq ($(CYGWIN),)
LIB_BASE_NAME=cyg$(PROJECTNAME)
else
LIB_BASE_NAME=lib$(PROJECTNAME)
endif

OTHER_DEPENDENCIES = $(TOP)/lib/$(PLATFORM_WITH_OPTIONS)/$(LIB_BASE_NAME).$(LIB_SUFFIX)

include ../../Makefile.local

