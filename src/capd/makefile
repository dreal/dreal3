# Compile and link the entire library and the bundled software.
# The target system can be specified in the command line,
# e.g., make target=win.
# Use "make library" to compile the library only, not the bundled software.
# This makefile was prepared by Pawel Pilarczyk.

TARGET = ${target}

default:

filedeps = $(wildcard utils/filedeps/*)
ifneq ($(filedeps),)
all: filedeps
.PHONY: filedeps
filedeps:
	-mkdir bin
	${MAKE} -C utils/filedeps
endif

.PHONY: default
default: 
	${MAKE} -C make 
  
  
RULES = library docs capdlib mpcapdlib purge clean help examples programs tests private all

.PHONY: ${RULES}
${RULES}: 
	${MAKE} -C make $@
	


#.PHONY: CAPD
#
#all: CAPD
#
#CAPD:
#ifeq (${TARGET},)
#	${MAKE} -C make
#else#
#	${MAKE} -C make target=${TARGET}
#endif
#
#
#.PHONY: library
#library:
#ifeq (${TARGET},)
#	${MAKE} -C make library
#else
#	${MAKE} -C make target=${TARGET} library
#endif

#.PHONY: purge
#purge:
#ifeq (${TARGET},)
#	${MAKE} -C make purge
#else
#	${MAKE} -C make target=${TARGET} purge
#endif

#.PHONY: clean
#clean:
#ifeq (${TARGET},)
#	${MAKE} -C make clean
#else
#	${MAKE} -C make target=${TARGET} clean
#endif

#.PHONY: help
#help:
#	${MAKE} -C make help
#	

