# MakeFile for the "filedeps" utility program by Pawel Pilarczyk.

# some definitions
CC = g++ -Wall -ansi -pedantic -O2 -s
CCI = ${CC}
OBJ = ../obj/
BIN = ../../bin/
SRC =
SRCLIB =
CCLIB =

# the default target
filedeps:

# the right extension of an executable file for Windows
windows_detect = $(wildcard /AUTOEXEC.BAT)
ifeq ($(windows_detect),)
	EXE =
else
	EXE = .exe
endif

# the target program
.PHONY: filedeps
filedeps: ${BIN}filedeps${EXE}

include makefile.dep

