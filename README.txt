COMPSPEN: ENtailment of COMPositional SeParation Logic with inductive definitions

About
=====
This is a decision procedure for the satisfiability and entailment problem between formulas in the Linearly Compositional Separation Logic with Recursive Definitions (SLRD_{LC}) 
defined in the paper “A complete decision procedure for linearly compositional separation logic with data constraints” (http://lcs.ios.ac.cn/~wuzl/pub/gcw-ijcar16.pdf).

The input format of the tool is defined in the file /samples/slrdi-theory.smt

Requires
========
To compile:

- a C99 compiler (tested under gcc)

- GNU flex >= 2.5.33

- GNU bison (tested under bison 2.4.1)

- SMTLIB2 parser of Alberto Griggio available at 
  https://es.fbk.eu/people/griggio/misc/smtlib2parser.html

- Z3 SMT solver (tested under z3 4.4.2)
  https://github.com/Z3Prover/z3
  Linux Commands: 
  -- aptitude search z3
  -- sudo apt-get install z3

- boost package (tested under boost 1.58.0)
  http://www.boost.org/
  Linux Commands: 
  -- aptitude search boost
  -- sudo apt-get install libboost-dev

Installation
============
1) Configuring: 
   - change the SMTLIB2_PREFIX variable in the Makefile.config file
     with the directory where can be found the libsmtlib2parser.so

   - (optional)
     change the compiler name or the compilation flags for the C compiler


2) Compiling:
   - do 'make' in src directory


3) Install:
   - move the 'compspen' binary to a known executable path



