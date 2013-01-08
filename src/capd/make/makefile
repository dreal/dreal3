# This is a makefile for the entire library.
# Copyright (C) 2004-2010 by the CAPD Group.
# This is free software. No warranty. Consult 'license.txt' for details.
# Initial version created on October 26, 2004 by Pawel Pilarczyk.


# ===========================================================================
# Settings.
# ===========================================================================

# Set up the home directory.
HOME = ../

# Determine the target configuration (see the file 'makecfg' for details).
include makecfg

# Include the compiler-dependent definitions.
include config/${TARGET}

# Determine the paths to files.
include makedirs

# ===========================================================================
# A list of libraries that are part of the library.
# ===========================================================================

LIBRARIES = ${wildcard ${HOME}src/*}
LIBRARIES := ${LIBRARIES:${HOME}src/%=%}
LIBRARIES := ${filter-out CVS, ${LIBRARIES}}
	  
# ===========================================================================
# A list of modules that are part of the current library.
# ===========================================================================

MODULES = ${wildcard ${SRC}*}
MODULES := ${MODULES:${SRC}%=%}
MODULES := ${filter-out CVS,${MODULES}}
ifeq (0, ${GUI})
MODULES := ${filter-out krak,${MODULES}}
endif

# ===========================================================================
# A list of source .cpp files in all the modules of the library.
# ===========================================================================

# full path to each .cpp file in each module
FILES = ${foreach MODULE,${MODULES},${wildcard ${SRC}${MODULE}/*.cpp}}
#FILES := ${notdir ${FILES}}

# it removes extensions (i.e. .cpp)   
FILES := ${basename ${FILES}}


# ===========================================================================
# A list of all the programs compiled with the library.
# ===========================================================================

# examples
PROGDEMO = ${wildcard ${EXAMPLES}*/makefile}
PROGDEMO := ${notdir ${PROGDEMO:%/makefile=%}}
PROGDEMO := ${PROGDEMO:%=${EXAMPLESDIR}%}
PROGDEMO := ${filter-out ${EXAMPLESDIR}/CVS,${PROGDEMO}}

# tests
PROGTEST = ${wildcard ${TESTS}*/makefile}
PROGTEST := ${notdir ${PROGTEST:%/makefile=%}}
PROGTEST := ${filter-out CVS,${PROGTEST}}
PROGTEST := ${PROGTEST:%=${TESTSDIR}%}

# programs
PROGS = ${wildcard ${PROGRAMS}*/makefile}
PROGS := ${notdir ${PROGS:%/makefile=%}}
PROGS := ${filter-out CVS,${PROGS}}
PROGS := ${PROGS:%=${PROGRAMSDIR}%}

# private
PROGPRIV = ${wildcard ${PRIVATE}*/makefile}
PROGPRIV := ${notdir ${PROGPRIV:%/makefile=%}}
PROGPRIV := ${filter-out CVS,${PROGPRIV}}
PROGPRIV := ${PROGPRIV:%=${PRIVATEDIR}%}

ALLPROGS = ${PROGDEMO} ${PROGTEST} ${PROGS} ${PROGPRIV}

# ===========================================================================
# Targets.
# ===========================================================================

#default target to be build if 'make' with no target is called
.DEFAULT_GOAL = default

.PHONY: default
default: directories filedeps library

# The main target: everything.
.PHONY: all
all: directories filedeps objects capdlib programs tests examples private

# Set the current library file name.
LIBRARY = ${LIB}lib${LIBNAME}${LIBEXT}

# ===========================================================================
# Create directories for obj files, libraries, executables
# ===========================================================================
.PHONY: directories
directories: bindir objdir libobjdir libdir 

define createdir
$(if $(wildcard $(1)),,-${MKDIR} $(1))
endef
 
.PHONY: bindir
bindir:
	$(call createdir,${BIN})

# The object directory.
.PHONY: objdir
objdir:
	$(call createdir,${OBJBASE})

# The library object directory.
.PHONY: libobjdir
libobjdir:
	$(call createdir,${OBJ})

# The library directory.
.PHONY: libdir
libdir:
	$(call createdir,${LIB})

# ===========================================================================
# Make the filedeps program for dependancy generation.
# ===========================================================================
.PHONY: filedeps
filedeps: bindir
	${MAKE} -C ../utils/filedeps


# ===========================================================================
# Make the object files.
# ===========================================================================


# Make the object files.
.PHONY: objects
objects: ${MODULES}

.PHONY: ${MODULES}
${MODULES}: %:
	${MAKE} -f makemain target=${TARGET} module=$@


# ===========================================================================
# Make the libraries
# ===========================================================================

# targets for all libraries
.PHONY: ${LIBRARIES:%=%lib}
${LIBRARIES:%=%lib}: %:
	${MAKE} target=${TARGET} libname=${@:%lib=%}

# Determine the list of all the object files in the project.
OBJFILES = ${FILES:${SRC}%=${OBJ}%${OBJEXT}}

# Current library (determined by parameter libname)
.PHONY: library
library: objects ${LIBRARY} 

# Make the current library.
${LIBRARY}: ${OBJFILES}
	${MAKELIB} ${LIBRARY} ${OBJFILES}
	${IDXLIB} ${LIBRARY}

# Make other libraries 
OTHERLIBRARIES = ${filter-out ${LIBNAME}, ${LIBRARIES}}
${OTHERLIBRARIES:%=${LIB}lib%${LIBEXT}}: %:
	${MAKE} target=${TARGET} libname=${@:${LIB}lib%${LIBEXT}=%}
# ===========================================================================
# Make all the example, test and other programs.
# ===========================================================================

.PHONY: examples
examples: objects library ${PROGDEMO}

.PHONY: tests
tests: objects library ${PROGTEST}

.PHONY: programs
programs: objects library ${PROGS}

.PHONY: private
private: objects library ${PROGPRIV}

.PHONY: ${ALLPROGS}
${ALLPROGS}: %:
	${MAKE} -C ${HOME}$@

# ===========================================================================
# Clean all the object files, libraries, executables and dependencies.
# ===========================================================================

# delete all the object files
.PHONY: cleanobj
cleanobj: cleanlibobj cleanprogsobj  

# delete all the library object files 	
.PHONY: cleanlibobj
cleanlibobj:
	-${REMOVE} ${OBJFILES}

# delete all programs object files	
.PHONY: cleanprogsobj
cleanprogsobj: ${ALLPROGS:%=CLEANOBJ_%}

.PHONY: ${ALLPROGS:%=CLEANOBJ_%}
${ALLPROGS:%=CLEANOBJ_%}: %:
	${MAKE} -C ${HOME}${@:CLEANOBJ_%=%} cleanobj

# delete all the executables
.PHONY: cleanexe
cleanexe: ${ALLPROGS:%=CLEANEXE_%} 

.PHONY: ${ALLPROGS:%=CLEANEXE_%}
${ALLPROGS:%=CLEANEXE_%}: %:
	${MAKE} -C ${HOME}${@:CLEANEXE_%=%} cleanexe

# delete all the library files
.PHONY: cleanlib
cleanlib:
	-${REMOVE} ${MODULES:%=${LIB}lib${LIBNAME}%${LIBEXT}} ${LIBRARY}
ifeq (${target},bcc)
	-${REMOVE} ${LIB}lib${LIBNAME}*.BAK
endif

# delete all the dependency files (generated with "filedeps")
.PHONY: cleandeps
cleandeps:
	-${REMOVE} ${MODULES:%=auto_deps/${LIBNAME}/%} \
	${ALLPROGS:%=${HOME}%/makedeps} 

.PHONY: purge
.PHONY: clean
# for capd library we clean also all programs objects files. 
ifeq (${LIBNAME},${CAPDLIBNAME})
purge: cleanobj cleanlib cleanexe
clean: cleanobj cleanlib
else
purge: cleanlibobj cleanlib cleanexe
clean: cleanlibobj cleanlib
endif


#============================================================================
# Install CAPD library 
# It copies header files and libraries to ${INSTALLDIR}
# One can change this by invoking 
#    make install prefix=/path/where/to/install/ 
#============================================================================ 
.PHONY: install
prefix = $(INSTALLDIR)
INCINSTALLDIR = $(prefix)include
LIBINSTALLDIR = $(prefix)lib
install: installlibdir library 
	@echo =================================================================== 
	@echo Installing CAPD library. 
	@echo On some systems you need run installation with administator rights.
	@echo =================================================================== 
	cp -r $(INC)capd $(INCINSTALLDIR)
	cp $(LIB)* $(LIBINSTALLDIR)

.PHONY: installlibdir 
installlibdirfile = $(wildcard ${LIBINSTALLDIR})
installlibdir:
ifeq (${installlibdirfile},)
	-${MKDIR} ${LIBINSTALLDIR}
else
endif

# ===========================================================================
# Make documentation
# ===========================================================================

MODULE = ${module}
doc: 
ifeq (${MODULE},)
	${MAKE} -C ../doc
else
	${MAKE} -C ../doc ${MODULE}
endif


# ===========================================================================
# Show help information (requested by M. Mrozek).
# ===========================================================================

CONFIGS = $(wildcard config/*)
CONFIGS := $(CONFIGS:config/%=%)
CONFIGS := $(filter-out CVS,$(CONFIGS))

.PHONY: help
help:
	
	@-$(REMOVE) makehelp
	@echo . > makehelp
	@echo . >> makehelp
	@echo . >> makehelp
	@echo BRIEF HELP INFORMATION ON MAKE ARGUMENTS: >> makehelp
	@echo . >> makehelp
	@echo Call: make target=... what_to_make. >> makehelp
	@echo . >> makehelp
	@echo Possible target system configurations: >> makehelp
	@echo $(CONFIGS) >> makehelp
	@echo . >> makehelp
	@echo Library modules to make: >> makehelp
	@echo $(MODULES) >> makehelp
	@echo . >> makehelp
	@echo Program groups to make [examples, tests, programs, private]: >> makehelp
	@echo $(PROGDEMO) $(PROGTEST) $(PROGS) $(PROGPRIV) >> makehelp
	@echo . >> makehelp
	@echo Other targets: >> makehelp
	@echo cleanexe cleanlib cleanobj cleandep clean purge >> makehelp
	@echo . >> makehelp
	@-cat makehelp
	@-$(REMOVE) makehelp

# That's all, folks!

# ===========================================================================
# Debug makefile
# ===========================================================================

.PHONY: debug
debug:
	@echo "TEST"
	@echo LIBNAME = ${LIBNAME}
	@echo SRC = ${SRC}
	@echo OBJ = ${OBJ}
	@echo FILES = ${FILES}
	@echo MODULES = ${MODULES}
	@echo LIBARIES = ${LIBRARIES}
	@echo COMPILE = ${COMPILE}
	@echo COSTAM = ${COSTAM}
	@echo  MAKEFLAGS = ${MAKEFLAGS}
	@echo MAKEOVERRIDES = ${MAKEOVERRIDES}
	@echo -----------------------------
	${MAKE} -f makemain debug
