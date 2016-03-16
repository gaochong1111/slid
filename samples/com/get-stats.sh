#!/bin/bash

## Generate the data for the tables included in the paper

## parameter $1 = predicate, 
## parameter $2 = function
do_pred_fun() {
	echo "==== $1-$2 ====="
# first call the solver in verbose mode
	./do-syn.sh $1 -$2 &> $1/$1-$2.slog
# generate the statistics about lemmas
	./com/get-lemma.sh $1 -$2 &> $1/$1-$2.stat
	tail -8 $1/$1-$2.stat
# generate the number of data queries
	echo "   - queries to data solver"
	ls -l z3/$1-$2-*-df-*.txt | wc -l
# generate the execution time
	echo "   - full execution time"
	(time ./do-syn-time.sh $1 -$2) &> $1/$1-$2.time
	tail -4 $1/$1-$2.time
}

## parameter $1 = predicate, 
do_pred() {
	echo "==== $1 ====="
# first call the solver in verbose mode
	./do-syn.sh $1 &> $1/$1.slog
# generate the statistics about lemmas
	./com/get-lemma.sh $1 &> $1/$1.stat
	tail -8 $1/$1.stat
# generate the number of data queries
	echo "    - queries to data solver"
	ls -l z3/$1-*-df-*.txt | wc -l
# generate the execution time
	echo "    - full execution time"
	(time ./do-syn-time.sh $1) &> $1/$1.time
	tail -4 $1/$1.time
}



## create the environment for launching the benchmark
ln -s com/do-syn.sh .
ln -s com/do-syn-time.sh .

## enumerate all examples

## sls
do_pred_fun sls search 
do_pred_fun sls insert
do_pred_fun sls delete

## bst
do_pred_fun bst search 
do_pred_fun bst insert
do_pred_fun bst delete

## avl
do_pred_fun avl insert

## rbt
do_pred_fun rbt insert

## nll
do_pred nll

## skl2
do_pred skl2

## skl3
do_pred skl3


