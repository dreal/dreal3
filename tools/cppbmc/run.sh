#!/bin/bash
CFILE=$1
BASE=${CFILE%%.c}
IFILE=${BASE}.i
GM/make_i.sh $1
./pass1.native $IFILE
