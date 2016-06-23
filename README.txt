About
=====
This is a decision procedure for the satisfiability and entailment problem between formulas in the fragment of Separation Logic with Recursive Definitions (SLRD) 
defined in the paper “A complete decision procedure for linearly compositional separation logic with data constraints” (http://lcs.ios.ac.cn/~wuzl/pub/gcw-ijcar16.pdf).


Requires
========
To compile:

- a C99 compiler (tested under gcc)

- GNU flex >= 2.5.33

- GNU bison (tested under bison 2.7.0)

- SMTLIB2 parser of Alberto Griggio available at 
  https://es.fbk.eu/people/griggio/misc/smtlib2parser.html

- Z3 SMT solver
  https://github.com/Z3Prover/z3

- boost (http://www.boost.org/)


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
   - put the 'minisat' tool in the PATH
   - move the 'spen' binary to a known executable path



