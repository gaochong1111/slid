# Makefile
#


include ../Makefile.config

#---------------------------------------
# Flags
#---------------------------------------

# Use ICFLAGS to specify machine-independent compilation flags.
ICFLAGS = -I. \
-I${Z3_INCLUDE} \
-I$(SMTLIB2_PREFIX)
 
# Use -DSPENEXT to compile the spen analyser
#ICFLAGS = -I. \
#-DSPENEXT \
#-I$(SMTLIB2_PREFIX)

ICXXFLAGS = \
-I$(LIBVATA_INCLUDE)

LDFLAGS = \
-L$(SMTLIB2_PREFIX) \
-L$(LIBVATA_LIB) \
-L$(LIBZ3_LIB)

#DEBUG=_debug

#---------------------------------------
# Files
#---------------------------------------

CCINC = noll_vector.h \
        noll_option.h \
	noll_types.h noll_vars.h noll_preds.h noll_form.h noll_graph.h \
	noll2bool.h noll2sat.h noll_norm.h noll_sat.h \
        noll2graph.h \
	libvata_noll_iface.h \
	noll_ta_symbols.h \
	noll_tree.h \
	noll_graph2ta.h noll_pred2ta.h \
        noll_lemma.h \
	noll_hom.h noll_entl.h \
	noll.h smtlib2noll.h 

CCSRC = noll_types.c \
	noll_vars.c \
	noll_preds.c noll_form.c \
	noll_graph.c \
        noll_option.c \
	noll2bool.c noll2sat.c noll_norm.c noll_sat.c \
        noll2graph.c \
	noll_ta_symbols.c \
	noll_tree.c \
	noll_graph2ta.c noll_pred2ta_gen.c noll_pred2ta.c \
	noll_lemma.c \
	noll_hom.c noll_entl.c \
	noll.c smtlib2noll.c \
	printdterm.c \
	slid_sat.c \
	noll-dp.c 

CXXSRC = libvata_noll_iface.cc

#---------------------------------------
# Rules
#---------------------------------------

SHARED_LIBS = -lsmtlib2parser \
	-lm \
	-lvata -lz3

all: spen


spen: $(subst .c,$(DEBUG).o,$(CCSRC)) $(subst .cc,$(DEBUG).o,$(CXXSRC)) 
	$(CXX) $(CXXFLAGS_DEBUG) -o $@ $^ $(LDFLAGS) $(SHARED_LIBS)

clean:
	rm -f *.o *~ *-out.txt *.dot result.txt
	
distclean: clean
	rm spen

install: spen
	mv spen $(HOME)/bin

indent: $(CCINC) $(CCSRC) 
	indent -nut $^

subsystem:
	cd ../smtlib2parser-1.4 && make
	

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .c .h .a .o .so .cc 
slid_sat.o:slid_sat.c
	$(CC) $(CFLAGS) $(ICFLAGS) -c -o $@ $< 

libvata_noll_iface.o: libvata_noll_iface.cc $(CCINC) $(DEPS)
	$(CXX) $(CXXFLAGS) $(ICXXFLAGS) -c -o $@ $<

libvata_noll_iface_debug.o: libvata_noll_iface.cc $(CCINC) $(DEPS)
	$(CXX) $(CXXFLAGS_DEBUG) $(ICXXFLAGS) -c -o $@ $<

%.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS) $(ICFLAGS) -c -o $@ $<

%_debug.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS_DEBUG) $(ICFLAGS) -c -o $@ $<


