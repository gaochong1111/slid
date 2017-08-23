COMPSPEN: ENtailment of COMPositional SeParation Logic with inductive definitions

About
=====
This is a decision procedure for the satisfiability and entailment problem of the formulae in the Linearly Compositional Separation Logic with Recursive Definitions (SLRD_{LC}) 
defined in the paper “A complete decision procedure for linearly compositional separation logic with data constraints” (http://lcs.ios.ac.cn/~wuzl/pub/gcw-ijcar16.pdf). 

The tool can be seen as an adaption and extension of the tool SPEN (https://www.irif.univ-paris-diderot.fr/~sighirea/spen/index.html). The input format of the tool is defined in the file /samples/slrdi-theory.smt

Requires
========
To compile:

- a C99 compiler (tested under gcc)

- GNU flex >= 2.5.33

- GNU bison (tested under bison 2.4.1 (better))

- SMTLIB2 parser of Alberto Griggio available at 
  https://es.fbk.eu/people/griggio/misc/smtlib2parser.html

- Z3 SMT solver (tested under z3 4.4.2)
  https://github.com/Z3Prover/z3
  Linux Commands: 
  -- aptitude search z3
  -- sudo apt-get install libz3-dev

- boost package (tested under boost 1.58.0)
  http://www.boost.org/
  Linux Commands: 
  -- aptitude search boost
  -- sudo apt-get install libboost-dev

Auxiliary Tools:
- graphviz (More infomation at http://www.graphviz.org/)
  -- sudo apt-get install graphviz
  -- sudo apt-get install xdot (only in linux)

Installation
============
1) Compiling:
   - modify Makefile
     LIB_DIR=/usr/local/lib your # libz3.so directory
     Z3LIB_PATH=/usr/local/lib/libz3.so # your libz3.so path
   - do 'make' in the directory


2) Install:
   - move the 'compspen' binary to a known executable path

Run
===
1) do 'compspen inputfile'
   - the output includes some *.dot files, xdot can open *.dot as a picture.
   




