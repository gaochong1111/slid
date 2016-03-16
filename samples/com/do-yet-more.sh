#!/bin/sh
for i in ls lss nll nlcl skl2 skl3 dll
do
echo "${i}"
	./doall.sh ${i}
done
