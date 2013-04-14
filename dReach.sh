#!/bin/bash

pushd `dirname $0` > /dev/null
SCRIPTPATH=`pwd`
popd > /dev/null

BMC=${SCRIPTPATH}/tools/bmc/main.native
DREAL=${SCRIPTPATH}/dReal
PRECISION=0.1
DREAL_OPTION="--visualize"

TIMEOUT_UTIL=${SCRIPTPATH}/timeout3

#################################################################
# USAGE
#################################################################
usage()
{
cat << EOF
usage: $0 options <*.drh>

dReach: Reachability Analysis for Nonlinear Hybrid Systems

OPTIONS:
   -p      precision (\delta) value for dReal (default: 0.001)
   -l      lower bound for the unrolling (default: 0)
   -u      upper bound for the unrolling (required)
   -t      timeout in second (required)
   -h      Show this message
   -v      Verbose
EOF
}

#################################################################
# Parse Option
#################################################################
TIMEOUT=
PRECISION=0.001
LB=0
UB=
VERBOSE=
while getopts "hl:u:p:t:v" OPTION
do
     case $OPTION in
         h)
             usage
             exit 1
             ;;
         t)
             TIMEOUT=$OPTARG
             ;;
         l)
             LB=$OPTARG
             ;;
         u)
             UB=$OPTARG
             ;;
         p)
             PRECISION=$OPTARG
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

#################################################################
# Check BMC & DREAL
#################################################################
if [ ! -e $BMC ]
then
        echo "BMC is not found at $BMC"
        echo "Please edit $0 to specify the correct location of BMC tool"
        exit 1
fi

if [ ! -e $DREAL ]
then
        echo "dReal is not found at $DREAL"
        echo "Please edit $0 to specify the correct location of dReal tool"
        exit 1
fi

$TIMEOUT_UTIL > /dev/null 2>&1
if [ $? -eq 127 ]
then
        echo "timeout is not found"
        echo "Please install one (such as timeout, gtimeout, or timeout3)."
        exit 1
fi

shift $(($OPTIND - 1))
if [[ -z $TIMEOUT || -z $UB || -z $1 || ! -e $1 || ! ${1: -4} == ".drh" ]]
then
     usage
     exit 1
fi

function log_output {
    echo `date`: "$1"
}

BASE=${1%.drh}
DRH=$BASE.drh
echo "PRECISION=$PRECISION"
echo "LB=$LB UB=$UB TIMEOUT=$TIMEOUT"
echo "DRH=$DRH"

for (( K=$LB; K<=$UB; K++ ))
do
    echo "=================================== K = $K ==========================================================================="
    SMT2=${BASE}_$K.smt2
    RESULT=${BASE}_$K.smt2.result
    log_output "Unroll $DRH => $SMT2:"
    $BMC -k $K $DRH > $SMT2 || { log_output "BMC T/O"; exit 77; }
    log_output "Run dReal --precision $PRECISION $DREAL_OPTION $SMT2"
    $TIMEOUT_UTIL -t ${TIMEOUT} $DREAL --precision=$PRECISION $DREAL_OPTION $SMT2 > $RESULT || { log_output "dReal T/O"; exit 77; }
    if [[ "`cat $RESULT`" == "sat" ]]
    then
        log_output "Result: sat"
    fi
    if [[ "`cat $RESULT`" == "unsat" ]]
    then
        log_output "Result: unsat"
    fi
    if [[ "`cat $RESULT`" == "unknown" ]]
    then
        log_output "Timed-out"
        exit 77
    fi
done
