#!/bin/bash

OUTDIR="sim_oo_outputs"
BMDIR="sim_oo_bm_outputs"
WRKLD_PATH=${1:-na}

if [ ! -f "$WRKLD_PATH" ]
then
    echo "usage ./run_sim_outorder <path/to/executable>"
    exit 1
fi 

if [ ! -d "$OUTDIR" ]
then
    mkdir $OUTDIR
fi

if [ ! -d "$OUTDIR" ]
then
    mkdir $OUTDIR
fi

WRKLD_FNAME="$(basename $WRKLD_PATH)"
OUT_PATH="${OUTDIR}/${WRKLD_FNAME}_out.txt"
#run simulator on inputted workload
./sim-outorder $WRKLD_PATH >& $OUT_PATH





