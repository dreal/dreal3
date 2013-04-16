#!/bin/bash
SCRIPTPATH=`dirname $(readlink -f $0)`
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
EOF
}

#################################################################
# Parse Option
#################################################################
K=3
PARSER=
while getopts "hk:i" OPTION
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
cpp -P -traditional-cpp $DRH > $PDRH
$BMC -k $K $PARSER $PDRH > $SMT
