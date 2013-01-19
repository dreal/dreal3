#!/bin/bash
FILE=$1
BASE=${FILE//.trace/}
PATTERN="Precision:"
cat $1 | \
awk -v RS="$PATTERN" 'NR > 1 { print RS $0 > "temp-" (NR-1) ".trace"; close( "temp-" (NR-1) ".trace") }'
for TEMP in `find . -name "temp-*"`
do
	mv -v $TEMP ${TEMP//temp/$BASE}
done
