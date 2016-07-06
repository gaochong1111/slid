DIRS=smtlib2parser-1.4 src

all:
	$(MAKE) -C smtlib2parser-1.4
	$(MAKE) -C src
install:
	mv src/compspen $(HOME)/bin

clean:
	rm smtlib2parser-1.4/*.o
	rm src/*.o
