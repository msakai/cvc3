dnl Process with autoconf to generate configure script   -*- sh -*-

dnl Init with sanity check for source directory
AC_INIT

dnl Set C++ as the default language for all tests
AC_LANG([C++])

AC_SUBST(EXTRA_SAT_HEADERS)
AC_SUBST(EXTRA_SAT_CPP)
AC_SUBST_FILE([LICENSE_INFO])
AC_SUBST(DPLL_BASIC)
EXTRA_SAT_HEADERS=""
EXTRA_SAT_CPP=""
LICENSE_INFO=/dev/null
LICENSE_INFO_FILE=""
DPLL_BASIC=""
#BEGIN zchaff
cvc_use_zchaff="yes"
AC_ARG_ENABLE(zchaff,
[  --enable-zchaff         Include zchaff code (default = yes)
  --disable-zchaff        Remove zchaff code (default = no)],
if test "$enableval" = "no"; then
   cvc_use_zchaff="no"
fi)
if test "$cvc_use_zchaff" = "yes"; then
/bin/sh >.zchaff <<EOF
echo "This copy of CVC3 is also configured to use the SAT solver zchaff whose"
echo "copyright is owned by Princeton University and is more restrictive."
echo ""
echo "Specifically, it may be used for internal, noncommercial, research purposes"
echo "only.  See the copyright notice in the following files for more information."
echo "To build CVC3 without these files, please delete them and then run:"
echo "<pre>"
echo "   ./configure --disable-zchaff"
echo "   make"
echo "</pre>"
echo ""
echo "<pre>"
echo "src/sat/xchaff_base.h"
echo "src/sat/xchaff_dbase.h"
echo "src/sat/xchaff_solver.h"
echo "src/sat/xchaff_utils.h"
echo "src/sat/xchaff_dbase.cpp"
echo "src/sat/xchaff_solver.cpp"
echo "src/sat/xchaff_utils.cpp"
echo "</pre>"
echo ""
EOF
EXTRA_SAT_HEADERS="xchaff.h xchaff_base.h xchaff_dbase.h xchaff_solver.h xchaff_utils.h"
EXTRA_SAT_CPP="xchaff.cpp xchaff_dbase.cpp xchaff_solver.cpp xchaff_utils.cpp "
LICENSE_INFO=.zchaff
LICENSE_INFO_FILE=.zchaff
DPLL_BASIC="-DDPLL_BASIC"
fi
#END zchaff

# Name of the OS
AC_SUBST(OSTYPE)
# Version of CVC
AC_SUBST(VERSION)

AC_SUBST(OPTIMIZED)
OPTIMIZED="0"
AC_SUBST(GCOV)
GCOV="0"
AC_SUBST(GPROF)
GPROF="0"

AC_ARG_WITH(build, 
[  --with-build=optimized  Specify the type of build (default = optimized).
                          Possible values: debug, optimized, gprof, gcov],
if test "$withval" = "optimized"; then
  OPTIMIZED="1"
elif test "$withval" = "gprof"; then
  OPTIMIZED="1"
  GPROF="1"
elif test "$withval" = "gcov"; then
  GCOV="1"
else
  DEBUG_MSG="yes"
fi,
# --with-build is not given, default is "optimized" build
  OPTIMIZED="1"
)

AC_SUBST(CXXFLAGS)
CXXFLAGS="$CXXFLAGS"
AC_ARG_ENABLE(debug-yacc,
[  --enable-debug-yacc     Enable debugging of yacc (default = no).],
if test "$enableval" = "yes"; then
  CXXFLAGS="$CXXFLAGS -DYYDEBUG"
fi)

dnl Some extra features
AC_SUBST(LD)
LD='$(CXX)'
AC_ARG_WITH(ld,
[  --with-ld               Use a specific program for linking.],
if test ! "x$withval" = "xno" && test ! "x$withval" = "x"; then
  LD="$withval"
fi)

AC_SUBST(LDFLAGS)
LDFLAGS="$LDFLAGS"
AC_ARG_WITH(extra-libs,
[  --with-extra-libs       List of paths to additional static libraries
                          separated with ":".],
if test ! "x$withval" = "xno" && test ! "x$withval" = "x"; then
  LDFLAGS="$LDFLAGS -L"`echo "$withval" | sed -e 's/:/ -L/g'`
fi)

AC_SUBST(CPPFLAGS)
CPPFLAGS="$CPPFLAGS"
AC_ARG_WITH(extra-includes,
[  --with-extra-includes   List of paths to additional include files
                          separated with ":".],
if test ! "x$withval" = "xno" && test ! "x$withval" = "x"; then
  CPPFLAGS="$CPPFLAGS -I"`echo "$withval" | sed -e 's/:/ -I/g'`
fi)

AC_ARG_WITH(version, 
[  --with-version=<version string>
                          The version string to report on cvc3 -version],
# If option is given
VERSION="$withval",
# If not given
VERSION=`cat VERSION`)

dnl Override check for "broken" compilers
AC_ARG_ENABLE(broken-cxx,
[  --enable-broken-cxx[=no]  Force configure to accept the compiler,
                          even if it thinks that it is broken.],
# If option is given
if test "x$enableval" = "xyes"; then
  enable_broken_cxx="yes"
else
  enable_broken_cxx="no"
fi,
# If option is not given
enable_broken_cxx="no")

dnl Find out what OS-specific subdirectory name to use

OSTYPE=`uname -s`-`uname -m`
OSTYPE=`echo "$OSTYPE" | sed 'y%ABCDEFGHIJKLMNOPQRSTUVWXYZ %abcdefghijklmnopqrstuvwxyz_%'`

if test `uname -s` = "Darwin"; then
 MAC_OSX=1
else
 MAC_OSX=""
fi

# The standard macro does something stupid.  Check it explicitly.
# AC_PROG_INSTALL

AC_SUBST(INSTALL)
AC_SUBST(INSTALL_FLAGS)
AC_PATH_PROG(INSTALL, install, cp)

if test "$INSTALL" = "cp"; then
  INSTALL_FLAGS=""
else
#  INSTALL_FLAGS="-C --owner=root --group=root"
#  INSTALL_FLAGS="-C"
# Seems like the arguments to 'install' are changing wildly with platform...
  INSTALL_FLAGS=""
fi

AC_SUBST(TIME)
if test -n "$MAC_OSX"; then
AC_PATH_PROG(TIME, gtime, [not found])
else
AC_PATH_PROG(TIME, time, [not found])
fi

if test "$TIME" = "not found"; then
  AC_MSG_WARN(Regression tests depend upon GNU time.)
if test -n "$MAC_OSX"; then
  AC_MSG_WARN(Please install GNU time; we suggest using MacPorts or DarwinPorts.)
fi
fi

AC_SUBST(PERL)
AC_PATH_PROG(PERL, perl, [not found])

if test "$PERL" = "not found"; then
  perl_found=0
  AC_MSG_WARN(Perl not found.  Static build will probably fail.)
  # Set default path for perl, just in case
  PERL=/usr/bin/perl
else
  perl_found=1
fi

dnl These checks rely on the behavior of autoconf and *require* bison and flex, rather than yacc or lex.

AC_PROG_YACC

if test "$YACC" != "bison -y"; then
  AC_MSG_ERROR([bison  not found])
fi

AC_PROG_LEX

if test "$LEX" != "flex"; then
  AC_MSG_ERROR([flex not found])
fi

dnl Check compiler version (we know that 3.0 does not compile)
AC_CACHE_CHECK(for compiler version ($CXX --version), cvc_cv_cxx_version,
cvc_cv_cxx_version=`$CXX --version | grep "[[[0-9]]][[[0-9]]]*[[[.]]][[[0-9]]]*" | sed -e 's/^[[[^0-9]]]*\([[[0-9.]]]*\).*$/\1/'`)

cxx_major_version=`echo $cvc_cv_cxx_version | sed -e 's/^\([[0-9]]*\).*/\1/'`
cxx_minor_version=`echo $cvc_cv_cxx_version | sed -e 's/^[[0-9]]*[[.]]\([[0-9]]*\).*/\1/'`

if test "$cxx_major_version.$cxx_minor_version" = "3.0"; then
    if test "$enable_broken_cxx" = "no"; then
      AC_MSG_ERROR(

[Compiler version $cvc_cv_cxx_version is known to generate bad executables.
If you still want to compile with it, configure with option
--enable-broken-cxx, but then do not ask for help unless you know how
to fix it.])

   else
# The user asked for bad compiler.  Warn him/her at the end.
    cxx_bad_version_warning="yes"
  fi
fi

AC_SUBST(STATIC)
STATIC="1"

AC_SUBST(STATIC_FLAG)
AC_SUBST(DYNAMIC_FLAG)
AC_SUBST(SHARED)
AC_SUBST(LD_SWITCHES_PRE)
AC_SUBST(LD_SWITCHES_POST)
AC_SUBST(LD_LIB_DIR)

if test -n "$MAC_OSX"; then
  DYNAMIC_FLAG="-dynamic"
  STATIC_FLAG=""
  SHARED="-dynamiclib -undefined dynamic_lookup"
  LD_SWITCHES_PRE=""
  LD_SWITCHES_POST=""
else
  DYNAMIC_FLAG=""
  STATIC_FLAG="-static"
  SHARED="-shared"
  LD_SWITCHES_PRE="-Wl,-static -Wl,--whole-archive"
  LD_SWITCHES_POST="-Wl,--no-whole-archive -Wl,-call_shared"
fi

AC_ARG_ENABLE(static,
[  --enable-static
  --disable-dynamic       Enable static build of cvc3 (default=yes).
                          Disable for faster link times.],
# If options is given
if test "$enableval" = "no"; then
  STATIC="0"
fi)

AC_ARG_ENABLE(dynamic,
[  --enable-dynamic
  --disable-static        Enable shared library build of cvc3 (default = no).],
# If option is given
if test "$enableval" = "yes"; then
  STATIC="0"
fi)

AC_SUBST(STATIC_LIB_SUFFIX)
STATIC_LIB_SUFFIX="a"

AC_SUBST(SHARED_LIB_SUFFIX)
if test -n "$MAC_OSX"; then
  SHARED_LIB_SUFFIX="dylib"
else
  SHARED_LIB_SUFFIX="so"
fi

AC_SUBST(RATIONAL_IMPL)
AC_ARG_WITH(arith,
[  --with-arith=gmp        Specify the arithmetic option to use:
                          gmp: C-only GMP package (default)
                          gmpxx: GMP package with C++ extensions (deprecated)
                          native: native computer arithmetic (finite precision)],
if test "$withval" = gmpxx; then
  RATIONAL_IMPL="-DRATIONAL_GMPXX"
elif test "$withval" = gmp; then
  RATIONAL_IMPL="-DRATIONAL_GMP"
elif test "$withval" = native; then
  RATIONAL_IMPL="-DRATIONAL_NATIVE"
else
  RATIONAL_IMPL=""
fi,
# if option is not given
RATIONAL_IMPL="-DRATIONAL_GMP"
)


dnl Checks for libraries.  Adds -lfoo to LIBS for each found library 'foo'
dnl and defines HAVE_LIBfoo, unless 3rd and 4th args are specified.

# Make sure we check the appropriate static / shared library

if test "$RATIONAL_IMPL" = "-DRATIONAL_GMP"; then
  AC_MSG_CHECKING(for gmp)
  LIBS="-lgmp $LIBS"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([[
#include <gmp.h>
#include <iostream>
]], [[  mpq_t x;
   mpq_init(x);
]])],[cvc_gmp_works="yes"],[cvc_gmp_works="no"])
if test "$cvc_gmp_works" = "no"; then
if test -n "$MAC_OSX"; then
  AC_MSG_RESULT(no)
  AC_MSG_CHECKING(for gmp in /opt/local)
  CPPFLAGS="-I/opt/local/include $CPPFLAGS"
  LDFLAGS="-L/opt/local/lib $LDFLAGS"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([[
#include <gmp.h>
#include <iostream>
]], [[  mpq_t x;
   mpq_init(x);
]])],[cvc_gmp_works="yes"],[cvc_gmp_works="no"])
fi
fi
if test "$cvc_gmp_works" = "no"; then
     AC_MSG_ERROR([[libgmp.a is not found.  
You can still compile CVC3 with native computer arithmetic:

   ./configure --with-arith=native

WARNING: native arithmetic may cause overflows and assertion failures.

If CVC3 fails due to an overflow in native arithmetic, do NOT
report a bug; it is an intended feature to prevent soundness errors.

For these reasons, we STRONGLY recommend installing GMP.]])
else
AC_MSG_RESULT(yes)
fi
elif test "$RATIONAL_IMPL" = "-DRATIONAL_GMPXX"; then
 AC_CHECK_LIB(gmp,   main, , AC_MSG_ERROR(libgmp.a is not found))
 AC_CHECK_LIB(gmpxx, main, , AC_MSG_ERROR(libgmpxx.a is not found))
elif test -z "$RATIONAL_IMPL"; then
 AC_MSG_ERROR("Unknown argument to with-arith")
fi

if test "$RATIONAL_IMPL" = "-DRATIONAL_GMPXX"; then
# Do some more extensive check of gmpxx, since it may be compiled with
# a wrong compiler.
AC_CACHE_CHECK(whether gmpxx library works, cvc_cv_gmpxx_works,
  cvc_cv_gmpxx_works="no"
  AC_LINK_IFELSE([AC_LANG_PROGRAM([[
#include <gmpxx.h>
#include <iostream>
]], [[  mpz_class x;
   std::cout << x;
]])],[cvc_cv_gmpxx_works="yes"],[]))

if test "$cvc_cv_gmpxx_works" = "no"; then
  AC_MSG_ERROR([libgmpxx.a did not link.
You may have to recompile GMP with the current compiler: $CXX.])
fi
fi

dnl Checks for header files.  
dnl Defines HAVE_headerFile for each headerFile found

AC_CHECK_HEADERS([vector list deque set string cstdlib cstdio \
 functional algorithm], , 
 AC_MSG_ERROR(header is not found))

dnl Checks for typedefs, structures, and compiler characteristics.

dnl Checks for library functions.

dnl Other tests

dnl Define the build and source directories for all sub-projects and
dnl flags for optional packages if we want them to be built

dnl CVC

dnl Top-level directory for CVC
AC_SUBST(TOP)
TOP=`pwd`

# Checking for documentation related programs
AC_SUBST(DOXYGEN)
AC_CHECK_PROG(DOXYGEN, doxygen, doxygen)
AC_SUBST(DOXYTAG)
AC_CHECK_PROG(DOXYTAG, doxytag, doxytag)
AC_SUBST(FIG2DEV)
AC_CHECK_PROG(FIG2DEV, fig2dev, fig2dev)
AC_SUBST(HAVE_DOT)
AC_CHECK_PROG(HAVE_DOT, dot, "YES", "NO")
AC_SUBST(ETAGS)
AC_CHECK_PROG(ETAGS, etags, "etags")
AC_SUBST(EBROWSE)
AC_CHECK_PROG(EBROWSE, ebrowse, "ebrowse")

CVC_OUTPUT_FILES="Makefile.local \
LICENSE"

OTHER_OUTPUT_FILES="bin/unpack \
bin/run_tests \
bin/cvc2smt \
doc/Doxyfile \
doc/Makefile"


AC_CONFIG_FILES([$CVC_OUTPUT_FILES \
$OTHER_OUTPUT_FILES
])
AC_OUTPUT

chmod a+x bin/run_tests
chmod a+x bin/cvc2smt
chmod a+x bin/unpack

opt_arith="$RAITONAL_IMPL"

if test "$RATIONAL_IMPL" = "-DRATIONAL_NATIVE"; then
  opt_arith="native"
elif test "$RATIONAL_IMPL" = "-DRATIONAL_GMP"; then
  opt_arith="GMP"
elif test "$RATIONAL_IMPL" = "-DRATIONAL_GMPXX"; then
  opt_arith="GMP with C++ extensions"
fi

cat <<EOF

CVC3 is configured successfully.
Platform: $OSTYPE
Version: $VERSION
Computer arithmetic: $opt_arith

Run ./configure --help for additional configuration options.

Type 'make' to compile CVC3.
EOF

if test $RATIONAL_IMPL = "-DRATIONAL_NATIVE"; then
echo ""
echo "*** You have chosen to compile CVC3 with native arithmetic support."
echo "*** If an arithmetic overflow occurs, you will get an assertion failure."
echo "*** To avoid overflow issues, install the GMP library."
fi

if test -n "$DEBUG_MSG"; then
echo ""
echo "*** CVC3 is configured to compile in debugging mode.  You can increase"
echo "*** the performance significantly by compiling an optimized executable:"
echo "***     ./configure --with-build=optimized"
fi

if test "$STATIC" = "0"; then
echo ""
echo "*** CVC3 is configured to compile using shared libraries."
echo '*** Type "make ld_sh" for bash shells or "make ld_csh" for csh shells'
echo "*** to see how to set LD_LIBRARY_PATH appropriately.  To use static"
echo "*** libraries and executables instead, run:"
echo "***     ./configure --enable-static"
fi

if test "$cxx_bad_version_warning" = "yes"; then
echo ""
echo "*** Warning: Compiler version $cvc_cv_cxx_version is known to generate bad"
echo "*** executables."
fi

