#!/bin/bash

for DRFILE in `ls -1 *.dr`
do
	EQID=`grep "ineq.*ID" $DRFILE | cut -d "[" -f 2 | cut -d "]" -f 1`;
	IDFILE=${DRFILE//.dr/.id}
	echo $EQID > $IDFILE
done
