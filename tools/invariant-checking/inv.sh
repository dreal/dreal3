#!/bin/bash

SCRIPTPATH="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"

INV=${SCRIPTPATH}/main.native

#################################################################
# USAGE
#################################################################
usage()
{
    cat << EOF
usage: $0 options <*.drh>

inv: Inductive Invariant Checking for Nonlinear Hybrid Systems

OPTIONS:
EOF
}

#################################################################
# Parse Option
#################################################################
while getopts "h" OPTION
do
    case $OPTION in
        h)
            usage
            exit 1
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
if [ ! -e $INV ]
then
    echo "INV(main.native) is not found at $INV"
    echo "Please edit $0 to specify the correct location of INV tool"
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
SMT=${BASE}_ind.smt2
sed "s/\/\/.*//g" $DRH | cpp -P -w > $PDRH
$INV $PDRH > ${SMT}
