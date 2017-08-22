
all:
	$(MAKE) -C smtlib2parser-1.4
	$(MAKE) -C src
install:
	mv src/compspen $(HOME)/bin

clean:
	rm -f smtlib2parser-1.4/*.o smtlib2parser-1.4/libsmtlib2parser.a smtlib2parser-1.4/smtlib2yices smtlib2parser-1.4/smtlib2bisonparser.c smtlib2parser-1.4/smtlib2bisonparser.h smtlib2parser-1.4/smtlib2flexlexer.c smtlib2parser-1.4/smtlib2flexlexer.h

	rm -f src/*.o src/compspen *.dot
