# Makefile
#
# A Makefile for when we are using SML/NJ to build the 3-CPS compiler
#
# src/compiler/Makefile.  Generated from Makefile.in by configure.
#

#### Start of system configuration section. ####

#
# directories for the install target
#
PREFIX =		/usr/local
INSTALL_BINDIR =	$(PREFIX)/bin
INSTALL_LIBDIR =	$(PREFIX)/lib
INSTALL_INCDIR =	$(PREFIX)/include

#
# directories for the local-install target
#
SRCDIR =	/home/benjamin/projects/3cps-papers/drafts/artifacts/compiler/3cps/src
LIBDIR =	@LIBDIR@
BINDIR =	/home/benjamin/projects/3cps-papers/drafts/artifacts/compiler/3cps/bin

#
# configuration support
#
CONFIGDIR =	/home/benjamin/projects/3cps-papers/drafts/artifacts/compiler/3cps/config

INSTALL =	/usr/bin/install -c
SHELL =		/bin/bash


#
# SML/NJ build tools
#
INSTALL_SMLNJ_WRAPPER = /home/benjamin/projects/3cps-papers/drafts/artifacts/compiler/3cps/bin/install-sml-wrapper.sh
ML_BUILD =		/home/benjamin/lib/smlnj-110.99/bin/ml-build
ML_BUILD_FLAGS =
ML_TRACE_FLAGS =	-DBACK_TRACE -Ctdp.instrument=true -S \$$smlnj-tdp/back-trace.cm
ML_MAKEDEPEND =		/home/benjamin/lib/smlnj-110.99/bin/ml-makedepend
ML_MAKEDEPEND_FLAGS =

BACK_TRACE =		no
ifneq ($(BACK_TRACE),no)
  ML_BUILD_FLAGS =	$(ML_TRACE_FLAGS)
endif

#### End of system configuration section. ####

PROGRAM =		smlc
HEAP_IMAGE =		$(PROGRAM).amd64-linux
ROOT_CM =		driver/sources.cm
CM_FILES =		cps/sources.cm \
			driver/sources.cm \
			common/sources.cm \
			front-end/sources.cm \
			mlb/sources.cm \
			back-end/llvm/sources.cm


#
# generated parser files
#
PARSER_FILES =		front-end/parser/minml.grm.sml \
			front-end/parser/minml.lex.sml \
			mlb/mlb.grm.sml \
			mlb/mlb.lex.sml

.PHONY:		local-install
local-install:	$(HEAP_IMAGE)
	$(INSTALL_SMLNJ_WRAPPER) $(PROGRAM) $(BINDIR)

.PHONY:		install
install:	$(HEAP_IMAGE)
	$(INSTALL_SMLNJ_WRAPPER) $(PROGRAM) $(INSTALL_BINDIR)

.PHONY:		build
build:		$(HEAP_IMAGE)

$(HEAP_IMAGE):	.depend $(CODE_FRAG_MKFILES)
	$(ML_BUILD) $(ML_BUILD_FLAGS) $(ROOT_CM) Main.main $(PROGRAM)
	touch $(HEAP_IMAGE)

#
# Dependency file rules
#
.depend:	$(CM_FILES)
	touch .depend
	$(ML_MAKEDEPEND) $(ML_MAKEDEPEND_FLAGS) -n -f .depend $(ROOT_CM) $(HEAP_IMAGE) || rm -f .depend

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(MAKECMDGOALS),devclean)
ifneq ($(MAKECMDGOALS),distclean)
sinclude .depend
endif
endif
endif

#################### Cleanup ####################

CLEAN_SUBDIRS =

CLEAN_FILES +=		$(HEAP_IMAGE) \
			$(PARSER_FILES) \
			.depend

DISTCLEAN_FILES +=	Makefile

DEVCLEAN_FILES =

include /home/benjamin/projects/3cps-papers/drafts/artifacts/compiler/3cps/mk/clean-rules.gmk
