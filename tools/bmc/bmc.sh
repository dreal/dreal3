#!/bin/bash

SCRIPTPATH="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

BMC=${SCRIPTPATH}/../bmc_main.native

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
EOF
}

#################################################################
# Parse Option
#################################################################
K=3
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
SMT=${BASE}_$K
sed "s/\/\/.*//g" $DRH | cpp -P -w > $PDRH

PATH_NUM=0
for PATH in `$BMC -k $K --pathgen $PDRH`
do
    echo "PATH :" $PATH
    $BMC -k $K --path "$PATH" $PDRH > ${SMT}_${PATH_NUM}.smt2
    PATH_NUM=$(($PATH_NUM + 1))
done
