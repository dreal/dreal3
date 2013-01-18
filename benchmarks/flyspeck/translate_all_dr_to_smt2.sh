#!/bin/bash
TRANSLATOR=../../tools/dr2smt2/dr2smt2.native
TRANSLATOR_OPT=-f

for DR in `ls -1 *.dr`
do
	SMT=${DR//dr/smt2}
	echo converting $DR to $SMT
	time $TRANSLATOR $TRANSLATOR_OPT $DR > $SMT
done
