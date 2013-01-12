#!/bin/bash
TRANSLATOR=../../tools/dr2smt2/dr2smt2.native

for DR in `ls -1 *.dr`
do
	SMT=${DR//dr/smt2}
	echo converting $DR to $SMT
	time $TRANSLATOR $DR > $SMT
done
