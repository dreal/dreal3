#!/bin/bash

#################################################################
# PLEASE EDIT THE FOLLOWING LINE
DREAL=~/work/dreal/bin/dReal  #Absolute path of dReal binary
TIMEOUT3=`dirname $0`/timeout3
SPLIT=`dirname $0`/split.py
MAX=30  #Number of CPUS to use
#################################################################

if [[ ! -f $DREAL ]]
then
	echo "Please edit $0 file to specify the absolute path of dReal binary."
	exit 1
fi

#################################################################
# USAGE
#################################################################
usage()
{
cat << EOF
usage: $0 options <*.smt.proof>

Checks the given proof.

OPTIONS:
   -h      Show this message
   -t      timeout in second (required)
   -v      Verbose
EOF
}

#################################################################
# Parse Option
#################################################################
TIMEOUT=
VERBOSE=
while getopts "ht:v" OPTION
do
     case $OPTION in
         h)
             usage
             exit 1
             ;;
         t)
             TIMEOUT=$OPTARG
             ;;
         v)
             VERBOSE=1
             ;;
         \?)
             usage
             exit
             ;;
     esac
done

shift $(($OPTIND - 1))

if [[ -z $TIMEOUT ]] 
then
     usage
     exit 1
fi

PROOF=$1
BASENAME=`basename ${PROOF//.smt2.proof}`
LOOP=`dirname $0`/loop.sh
TRACE=${BASENAME}.trace
RESULTDIR=${PROOF}.extra

function log_msg {
	echo -n "`date`: "
	printf "[%-30s]: " `basename $1`
	echo $2
}

#################################################################
# Check the proof file
#################################################################
if [[ ! -f $PROOF ]]
then
	echo Error: file $PROOF does not exist.
	exit 1
fi

#################################################################
# Prepare RESULTDIR
#################################################################
[[ ! -d $RESULTDIR ]] && mkdir $RESULTDIR 2> /dev/null
if [[ ! -d $RESULTDIR ]] 
then
	echo Error: cannot create ${RESULTDIR}.
	exit 1
fi

#################################################################
# Copy trace into the result dir
#################################################################
if [[ ! -f $RESULTDIR/$TRACE ]]
then
	cp $PROOF $RESULTDIR/$TRACE
fi

#################################################################
# Run Split
#################################################################
if [[ -f $RESULTDIR/$TRACE ]]
then
	$SPLIT $RESULTDIR/$TRACE
fi

#################################################################
# Start Loop
#################################################################
${TIMEOUT3} -t $TIMEOUT $LOOP $TIMEOUT $DREAL $MAX $RESULTDIR

if [[ -f $RESULTDIR/PROVED ]]
then
	log_msg $1 "proof verified"
else
	log_msg $1 "timeout"
fi
