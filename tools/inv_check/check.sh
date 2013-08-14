#!/bin/bash

case "$OSTYPE" in
  darwin*)
	SCRIPTPATH=`dirname $(readlink $0)`;;
  linux*)  
	SCRIPTPATH=`dirname $(readlink -f $0)`;;
  *)    
	SCRIPTPATH=`dirname $(readlink -f $0)`;;
esac

BMC=${SCRIPTPATH}/main.native

#################################################################
# USAGE
#################################################################
usage()
{
    cat << EOF
usage: $0 options <*.drh>

bmc: Bounded Model Checking for for Nonlinear Hybrid Systems

OPTIONS:
   -k      unrolling steps  (default: 3)
   -i      use infix parser (default: prefix parser)
   -p      specify a path to focus (default: X)
EOF
}

#################################################################
# Parse Option
#################################################################
K=3
PATH_OPT=
PARSER=
while getopts "hk:p:i" OPTION
do
    case $OPTION in
        h)
            usage
            exit 1
            ;;
        k)
            K=$OPTARG
            ;;
        i)
            PARSER="--infix"
            ;;
        p)
            PATH_OPT="$OPTARG"
            ;;
        \?)
            usage
            exit
            ;;
    esac
done

#################################################################
# Check main.native
#################################################################
if [ ! -e $BMC ]
then
    echo "BMC(main.native) is not found at $BMC"
    echo "Please edit $0 to specify the correct location of BMC tool"
    exit 1
fi

shift $(($OPTIND - 1))
if [[ ! -e $1 || ! ${1: -4} == ".drh" ]]
then
    usage
    exit 1
fi

function log_output {
    echo `date`: "$1"
}

BASE=${1%.drh}
DRH=$BASE.drh
PDRH=$BASE.preprocessed.drh
SMT=${BASE}_$K.smt2
sed "s/\/\/.*//g" $DRH | cpp -P -w > $PDRH
echo "$BMC -k $K $PARSER $PATH_OPT $PDRH > $SMT"
if [[ "$PATH_OPT" == "" ]]
then
	$BMC -k $K $PARSER $PDRH > $SMT
else
	$BMC -k $K $PARSER --path "$PATH_OPT" $PDRH > $SMT
fi
