# This is a makefile for compiling programs that use the CAPD library.
# Copyright (C) 2004 by the CAPD group.
# This is free software. No warranty. Consult 'license.txt' for details.
# Created on October 26, 2004. Last revision: October 4, 2005.

# Note: Put this makefile in the directory containing your own source code
# which uses the CAPD library. Then list your source files accordingly.

# Use "make" on its own to make all of your programs or "make spec" to make
# a specific program or sub-package only.
# Note: The CAPD library must already exist and be up-to-date.


# ===========================================================================
# Programs which can be compiled using this makefile.
# ===========================================================================

# a list of all the programs in your package
PROGS = argtest bit2pset bmp2pset cell2cub chkmvmap chkperf chmap cleanlog \
	cnvchmap cnvmvmap cub2cell cub2map cubchain cubdiff cubiproj \
	cubslice hitenter hombin homchain homcub2l homcubes homsimpl \
	indxpair map2cub maprestr pgm2pset pset2bmp psetcomm psetconn \
	psetglue simchain

# a list of all your units to be linked with your programs
OTHERS = cells

# the CAPD libraries to use (if different from the global one)
LIBRARY = capdhomology

# define "GUI = 0" for console applications, otherwise GUI is assumed
GUI = 0

# a subdirectory for storing the object files of this program group
SUBDIR = homprogs


# ===========================================================================
# Include the generic makefile for this project.
# ===========================================================================

include ../../make/makeprog


# That's all, folks!

