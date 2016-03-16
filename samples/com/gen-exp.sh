#!/bin/bash

for i in `ls *.smt2`
do
        BNAME=`basename -s .smt2 ${i}`
	echo "======${BNAME}======"
 	if (test -f ${BNAME}.smt)
	then
		echo "${BNAME}.smt exists"
        else
		cp ${i} ${BNAME}.smt
		to-slrdi.sh ${BNAME}.smt
	fi
done

for i in `ls *.smt`
do
	EXPECTED_FILE="${i}.exp"
 	if (test -f ${EXPECTED_FILE})
	then
		echo "${EXPECTED_FILE} exists"
        else
		cp exp.exp ${EXPECTED_FILE}
	fi
done
