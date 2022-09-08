dnl Process this file with autoconf to produce a configure script.
dnl

AC_INIT(3-cps,0.1,)

AC_PREREQ(2.60)
AC_COPYRIGHT([[COPYRIGHT (c) 2019 The University of Chicago]])
AC_CONFIG_SRCDIR(src/compiler/common/ctl.sml)
AC_CONFIG_AUX_DIR(config)
AC_CONFIG_MACRO_DIR(config)

dnl
dnl include additional macros
dnl
sinclude(config/check_smlnj.m4)

dnl
dnl get host information
dnl
AC_CANONICAL_HOST

ROOTDIR=`pwd`
SRCDIR=$ROOTDIR/src
BINDIR=$ROOTDIR/bin
MKDIR=$ROOTDIR/mk

AC_SUBST(ROOTDIR)
AC_SUBST(SRCDIR)
AC_SUBST(BINDIR)
AC_SUBST(MKDIR)

AC_PROG_INSTALL
AC_PROG_MAKE_SET

#################### SML configuration ####################

dnl
dnl We support building with both SML/NJ (the default) or MLton.
dnl

dnl first check for --with-mlton=path flag
dnl
AC_ARG_WITH([mlton],
  [AS_HELP_STRING([--with-mlton=<path-to-mlton>],
    [use the MLton Standard ML compiler to build the compiler])],
  [with_mlton=yes],[with_mlton=no])
if test x"$with_mlton" = xyes ; then
  if test x"$ac_cv_path_with_mlton" = x ; then
    # look for mlton in the PATH
    AC_PATH_PROGS(with_mlton, mlton, no)
    if test x"$MLTON" = xno ; then
      AC_MSG_ERROR([unable to find mlton executable; please specify the path])
    fi
  else
    with_mlton=$ac_cv_path_with_mlton
    case $with_mlton in
      /*) ;;
      *) AC_MSG_ERROR([please specify absolute path for mlton executable]) ;;
    esac
    if test ! -x $with_mlton ; then
      AC_MSG_ERROR([invalid path for mlton; $with_mlton is not executable])
    fi
  fi
fi

if test x"$with_mlton" = xno ; then
  # we are using SML/NJ
  #

  dnl check that we have a compatible version of SML/NJ
  dnl
  CHECK_SMLNJ([AC_MSG_ERROR([unable to find SML/NJ installation; please add it to your PATH or set SML_CMD])])
  if test $SMLNJ_MAJOR_VERSION -lt 110 \
    -o \( $SMLNJ_MAJOR_VERSION -eq 110 -a $SMLNJ_MINOR_VERSION -lt 99 \)
  then
    AC_MSG_ERROR([installation requires SML/NJ version 110.99+ (available from smlnj.org)])
  fi

  dnl if the SMLNJ_PATH (and SMLNJ_CMD) variables are relative paths, then we add the
  dnl $ROOTDIR as a prefix so that scripts work correctly.
  dnl
  case $SMLNJ_PATH in
    /*) ;; # already absolute
    *)  SMLNJ_PATH="$ROOTDIR/$SMLNJ_PATH"
        sml=`basename "$SMLNJ_CMD"`
        SMLNJ_CMD="$SMLNJ_PATH"/"$sml"
        AC_MSG_NOTICE([using SMLNJ_PATH=$SMLNJ_PATH])
  esac

  dnl look for ml-makedepend
  dnl
  tmpPATH="$SMLNJ_PATH:$PATH"
  AC_PATH_PROG(ML_MAKEDEPEND, ml-makedepend, ":", $tmpPATH)
  AC_SUBST(ML_MAKEDEPEND)

  dnl
  dnl look for ml-build
  dnl
  tmpPATH="$SMLNJ_PATH:$PATH"
  AC_PATH_PROG(ML_BUILD, ml-build, none, $tmpPATH)
  if test $ML_BUILD = none ; then
    AC_MSG_ERROR([ml-build not found])
  fi
  AC_SUBST(ML_BUILD)
  SML=smlnj

  HEAP_IMAGE_DIR=$BINDIR/.heap
  INSTALL_SMLNJ_WRAPPER=$BINDIR/install-sml-wrapper.sh
  AC_SUBST(HEAP_IMAGE_DIR)
  AC_SUBST(INSTALL_SMLNJ_WRAPPER)

else

  # we are using MLton
  MLTON=$with_mlton
  AC_SUBST(MLTON)
  SML=mlton

fi
AC_SUBST(SML)

#################### end SML configuration ####################

#################### write output ####################

dnl The Makefile for the compiler depends on which SML system we are
dnl using.
if test x"$SML" = xmlton ; then
  COMPILER_MAKEFILE_IN=":src/compiler/Makefile_mlton.in"
  FRAG_GEN_MAKEFILE="src/compiler/gen/fragments/Makefile"
else
  COMPILER_MAKEFILE_IN=""
  FRAG_GEN_MAKEFILE=
fi

AC_CONFIG_FILES(
dnl
dnl ***** Makefiles *****
  src/compiler/Makefile"$COMPILER_MAKEFILE_IN"
)

dnl
dnl shell scripts
dnl
AC_CONFIG_FILES([
  bin/install-sml-wrapper.sh:config/install-sml-wrapper_sh.in
], [chmod +x bin/install-sml-wrapper.sh])

AC_OUTPUT

#################### end write output ####################
