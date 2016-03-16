# Makefile
#

TOOL=../../src/spen
# for ta
OPTIONTA=
# for syn-dp
OPTIONSY=-v -d -syn
#OPTIONSY=-syn

.PHONY: clean purge

clean:
	rm -f *out.txt result.txt graph-*.txt form-*.txt *.dot gmon.out df-*.txt

purge: clean
	rm -f *.log

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .smt .log .slog


%.smt.log: %.smt
	$(TOOL) $(OPTIONTA) $< > $@ 2>&1

%.smt.slog: %.smt
	$(TOOL) $(OPTIONSY) $< > $@ 2>&1

