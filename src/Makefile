# Makefile
#


include ./Makefile.config

#---------------------------------------
# Flags
#---------------------------------------

# Use ICFLAGS to specify machine-independent compilation flags.
ICFLAGS = -I. \
-I$(SMTLIB2_PREFIX)
 
# Use -DSPENEXT to compile the spen analyser
#ICFLAGS = -I. \
#-DSPENEXT \
#-I$(SMTLIB2_PREFIX)

#ICXXFLAGS = \
-I$(LIBVATA_INCLUDE)\
-I../z3/src/api\
-I../z3/src/api/c++

LDFLAGS = \
-L$(SMTLIB2_PREFIX) \
#-L$(LIBVATA_LIB)

#DEBUG=_debug

#---------------------------------------
# Files
#---------------------------------------

CCINC = noll_vector.h \
        noll_option.h \
	noll_types.h noll_vars.h noll_preds.h noll_form.h noll_graph.h \
	noll2bool.h noll2sat.h noll_norm.h noll_sat.h \
        noll2graph.h \
	noll_ta_symbols.h \
        noll_lemma.h \
	noll_entl.h \
	noll.h smtlib2noll.h\
	sl_entail.h\
	sl_formula.h\
	sl_abstr.h\
	sl_for.h\
	sl_var.h\
	sl_context.h\
	graph.h\
	sl_sat.h\
	sl_entl.h

CCSRC = noll_types.c \
	noll_vars.c \
	noll_preds.c noll_form.c \
	noll_graph.c \
        noll_option.c \
	noll2bool.c noll2sat.c noll_norm.c noll_sat.c \
        noll2graph.c \
	noll_ta_symbols.c \
	noll_lemma.c \
	noll_entl.c \
	noll.c smtlib2noll.c \
	noll-dp.c\
	slid_sat.c\
	ptool.c

CXXSRC = sl_entail.cc\
	 sl_formula.cc\
	 sl_abstr.cc\
	 sl_for.cc\
	 sl_context.cc\
	 graph.cc\
	 sl_sat.cc\
	 sl_entl.cc\
	 sl_var.cc


#---------------------------------------
# Rules
#---------------------------------------

SHARED_LIBS = -lsmtlib2parser \
	-lm \
	-lz3

all: compspen


compspen: $(subst .c,$(DEBUG).o,$(CCSRC)) $(subst .cc,$(DEBUG).o,$(CXXSRC))
	$(CXX) $(CXXFLAGS_DEBUG) -o $@ $^ \
	$(LDFLAGS) \
	$(SHARED_LIBS)

clean:
	rm -f *.o *~ *-out.txt *.dot result.txt
	
distclean: clean
	rm compspen

install: compspen
	mv compspen $(HOME)/bin

indent: $(CCINC) $(CCSRC) 
	indent -nut $^

#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------

.SUFFIXES: .c .h .a .o .so .cc


#libvata_noll_iface.o: libvata_noll_iface.cc $(CCINC) $(DEPS)
#	$(CXX) $(CXXFLAGS) $(ICXXFLAGS) -c -o $@ $<

#libvata_noll_iface_debug.o: libvata_noll_iface.cc $(CCINC) $(DEPS)
#	$(CXX) $(CXXFLAGS_DEBUG) $(ICXXFLAGS) -c -o $@ $<

%.o: %.cc $(CCINC) $(DEPS)
	$(CXX) $(CXXFLAGS) $(ICXXFLAGS) -c -o $@ $<

%.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS) $(ICFLAGS) -c -o $@ $<

%_debug.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS_DEBUG) $(ICFLAGS) -c -o $@ $<


