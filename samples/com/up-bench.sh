#!/bin/bash

if [ "$#" -ne 1 ]; then
	echo "usage: $0 <dir>"
	exit 1
fi

BENCHDIR=$1

for i in `ls ${BENCHDIR}/*.smt`
do
	echo "**** Testing file \"${i}\""
	FILE=`basename ${i} .smt`
 	SPNFILE="smtcomp14/log/${FILE}.smt2.spn"
 	SMTFILE="smtcomp14/log/${FILE}.smt2"
	echo ",,,, move ${SPNFILE}"
	mv ${SPNFILE} ${BENCHDIR}/${FILE}.smt
	ERES=$(grep :status ${SMTFILE} | grep -c \ unsat\))
	echo ",,,, ${ERES}"
	if [ "${ERES}" -eq "0" ] ; then
		echo "sat" &>  ${BENCHDIR}/${FILE}.smt.exp
        else
		echo "unsat" &>  ${BENCHDIR}/${FILE}.smt.exp
        fi
done

