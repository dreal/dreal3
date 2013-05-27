#!/bin/bash
if [ $# != 1 ]
then
	echo "Usage: $0 <.c file>"
	exit 1
fi

if [ -e $1 ]
then
	gcc -E $1 > ${1%\.c}.i
else
	echo "The input file $1 does not exist."
fi
