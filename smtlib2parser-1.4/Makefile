YICES_DIR = /usr/local/yices-1.0.40

CC = gcc
FLEX = flex
BISON = bison
CFLAGS = -static -std=c99 -pedantic -g -Wno-unused-function -Wno-incompatible-pointer-types -Wno-implicit-function-declaration -Wall
LDFLAGS = -g -lgmp -lgmpxx -lstdc++ 
SHARED = $(CC) -shared

OBJECTS = smtlib2bisonparser.o \
	  smtlib2flexlexer.o \
	  smtlib2hashtable.o \
	  smtlib2abstractparser.o \
	  smtlib2termparser.o \
	  smtlib2utils.o \
	  smtlib2vector.o \
	  smtlib2charbuf.o \
	  smtlib2stream.o \
	  smtlib2scanner.o

YICES_OBJECTS = smtlib2yices.o \
	        yicesmain.o

GCCVERSIONGTEQ46 := $(shell expr `gcc -dumpversion | cut -f2 -d.` \>= 6)

ifeq "$(GCCVERSIONGTEQ46)" "0"
BISON_SRC = smtlib2bisonparser.orig.y 
else
BISON_SRC = smtlib2bisonparser.y 
endif

all: libsmtlib2parser.a

clean:
	rm -f $(OBJECTS) $(YICES_OBJECTS) libsmtlib2parser.a smtlib2yices smtlib2bisonparser.c smtlib2bisonparser.h smtlib2flexlexer.c smtlib2flexlexer.h


smtlib2yices: libsmtlib2parser.a $(YICES_OBJECTS)
	$(CC) $(YICES_OBJECTS) libsmtlib2parser.a $(YICES_DIR)/lib/libyices.a $(LDFLAGS) -o $@

smtlib2yices.o: smtlib2yices.c
	$(CC) $(CFLAGS) -I$(YICES_DIR)/include -c -o $@ $<
yicesmain.o: yicesmain.c
	$(CC) $(CFLAGS) -I$(YICES_DIR)/include -c -o $@ $<

libsmtlib2parser.a: $(OBJECTS)
	ar rc $@ $(OBJECTS)
	ranlib $@

libsmtlib2parser.so: $(OBJECTS)
	$(SHARED) $(LDFLAGS) $(SHARED_LIBS) -o $@ $^


%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<


smtlib2bisonparser.c: $(BISON_SRC) smtlib2flexlexer.c
	$(BISON) -o $@ $<

smtlib2flexlexer.c: smtlib2flexlexer.l
	$(FLEX) --header-file="smtlib2flexlexer.h" -o $@ $<
