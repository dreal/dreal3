#!/bin/bash
UNSAT_DIR=result/unsat
TOUT=~/work/dreal2/tools/kepler/script/timeout3

for SMT in `cat unsat_list.txt`
do
	BASE=${SMT//.smt2/}

	# create dir
	echo $SMT
	mkdir $BASE
	cp -v ${UNSAT_DIR}/${BASE}.smt2 $BASE/

	cd $BASE
	$TOUT -t 1800 ../loop.sh
	cd ..
done
