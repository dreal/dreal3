#!/bin/bash

for smt in `find . -name "*.smt2" | grep -v "minismt"`
do
	LASTLINE=`tail -n 1 $smt`
	if [ $LASTLINE != "(exit)" ]
	then
		echo Current last line of $smt is $LASTLINE.
		echo Append "(exit)" at the end of $smt
		echo "(exit)" >> $smt
	else 
		echo $smt is "OK"
	fi
done
