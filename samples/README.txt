This directory conatins the benchmarks of spen

Files:

com		shell scripts used to execute the benchmarks

  do-syn.sh     execute the benchmark for a predicate set and a function
                in order to do regresion testing

                (once) ln -s com/do-syn.sh .
                ./do-syn.sh sls -delete

  do-syn-time.sh execute the benchmark for a predicate set and a function
                 in order to obtain execution time (less msg than do-syn.sh)

                (once) ln -s com/do-syn-time.sh .
                ./do-syn-time.sh sls -delete
                
  get-lemma.sh  generate stats about the lemma use based on */*.slog files
                output by the do-syn.sh call
                
		./com/get-lemma.sh sls -delete

  get-stats.sh  generate the data needed for the experiments in the paper

		./com/get-stats.sh

Makefile	call spen and common tasks for one file

slrd*-logic.smt	definition of the logics used as SMTLIB theory
slrd*-theory.smt

avl		benchmarks for AVL
		for spen -syn

bench		benchmark from SLCOMP'14

bst		benchmark for Binary Search Trees 
		for spen -syn

dll		benchmark for doubly linked lists
		for spen -ta

gen		general recursive definitions
		for spen -ta

ls		benchmark for acyclic singly linked lists

lss		benchmark for acyclic linked lists with two next fields

nlcl 		acyclic lists of circular lists
		for spen -ta

nll 		acyclic lists of acyclic singly linked lists

rbt		red black trees
		for spen -syn

skl2		acyclic skip lists with 2 levels

skl3		acyclic skip lists with 3 levels

sls		sorted, acyclic, singly linked lists

smt-PLDI2011	acyclic sinly linked lists taken from Perez-Rybalchenko 2011

z3		samples of entailments problems for z3

