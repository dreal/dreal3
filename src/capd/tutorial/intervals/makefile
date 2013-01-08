CC = g++
OPTS = -O2 -I../../include -L../../lib
LIBS = -lcapd

all: intervalExample

intervalExample: intervalExample.cpp
	${CC} ${OPTS} intervalExample.cpp -o intervalExample ${LIBS}

clean:
	rm intervalExample
