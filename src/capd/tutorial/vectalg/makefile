CC = g++
OPTS = -I../../include -L../../lib
LIBS = -lcapd
PROGS = vectorExample matrixExample normExample

all: ${PROGS}

vectorExample: vectorExample.cpp
	${CC} ${OPTS} vectorExample.cpp -o vectorExample ${LIBS}

matrixExample: matrixExample.cpp
	${CC} ${OPTS} matrixExample.cpp -o matrixExample ${LIBS}

normExample: normExample.cpp
	${CC} ${OPTS} normExample.cpp -o normExample ${LIBS}

