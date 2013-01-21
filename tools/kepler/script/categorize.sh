#!/bin/bash
for RESULT in `ls *.result`
do
	CAT=`cat $RESULT`
	echo $RESULT - $CAT

	mkdir $CAT 2> /dev/null
	mv -v ${RESULT//.result/}.* $CAT/
done
 
