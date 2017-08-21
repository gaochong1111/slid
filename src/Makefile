# Makefile
#


include ./Makefile.config

#---------------------------------------
# Flags
#---------------------------------------

# Use ICFLAGS to specify machine-independent compilation flags.
ICFLAGS = -I. \
-I$(SMTLIB2_PREFIX)

LIB_DIR=/usr/local/lib
Z3LIB_PATH=/usr/local/lib/libz3.so

SHARED_LIBS = -lsmtlib2parser -lm

DYN_LINK_LIB_FLAG = -rdynamic $(Z3LIB_PATH)
DYN_RUN_LIB_FLAG = -Wl,-R$(LIB_DIR)

LDFLAGS = \
-L$(SMTLIB2_PREFIX) \

#DEBUG=_debug

#---------------------------------------
# Files
#---------------------------------------

CCINC = noll_vector.h \
        noll_option.h \
	noll_types.h noll_vars.h noll_preds.h noll_form.h \
	noll.h smtlib2noll.h   noll_entl.h\
	csltp_order_graph.h csltp_sat.h\


# slid_files
#	sl_entail.h\
sl_formula.h\
sl_abstr.h\
sl_for.h\
sl_var.h\
graph.h\
sl_sat.h\
sl_context.h\
sl_entl.h

# noll_graph.h  noll2sat.h noll_sat.h\
	noll2bool.h noll_norm.h  \
        noll2graph.h \
		 \


CCSRC = noll_types.c \
	noll_vars.c \
	noll_preds.c noll_form.c \
    noll_option.c \
	noll.c smtlib2noll.c \
	noll_dp.c

# noll_sat.c noll_graph.c noll2bool.c  noll_norm.c  noll2graph.c 	noll2sat.c	\
# slid_files: slid_sat.c

CXXSRC =noll_entl.c csltp_order_graph.cc csltp_sat.cc\

# slid_files:
# sl_entail.cc\
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



all: compspen


compspen: $(subst .c,$(DEBUG).o,$(CCSRC)) $(subst .cc,$(DEBUG).o,$(CXXSRC))
	$(CXX) $(CXXFLAGS_DEBUG) -o $@ $^ \
	$(LDFLAGS) \
	$(DYN_LINK_LIB_FLAG) \
	$(DYN_RUN_LIB_FLAG) \
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



%.o: %.cc $(CCINC) $(DEPS)
	$(CXX) $(CXXFLAGS) $(ICXXFLAGS) -c -o $@ $<

%.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS) $(ICFLAGS) -c -o $@ $<

%_debug.o: %.c $(CCINC) $(DEPS)
	$(CC) $(CFLAGS_DEBUG) $(ICFLAGS) -c -o $@ $<


