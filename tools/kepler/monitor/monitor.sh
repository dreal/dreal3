#!/bin/bash
FORMULA_FILE=$1
RANGE_DIR=$2
MAX_PROC=1
STAGE=1
echo $FORMULA_FILE $RANGE_DIR
# We keep doing this until there is no file in the range directory
while [ "$(ls -A $RANGE_DIR)" ]
do
	NUM_OF_RANGE=`ls -1 $RANGE_DIR | wc -l`
	echo "STAGE = $STAGE, NUM_OF_RANGE = $NUM_OF_RANGE"
	find $RANGE_DIR -type f | \
	    parallel --max-procs=$MAX_PROC "./run_single.sh {} $FORMULA_FILE"
	STAGE=$(($STAGE + 1))
done
