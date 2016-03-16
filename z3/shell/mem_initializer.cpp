// Automatically generated file.
#include"rational.h"
#include"symbol.h"
#include"gparams.h"
#include"trace.h"
#include"prime_generator.h"
#include"debug.h"
void mem_initialize() {
rational::initialize();
initialize_symbols();
gparams::init();
}
void mem_finalize() {
rational::finalize();
finalize_symbols();
gparams::finalize();
finalize_trace();
prime_iterator::finalize();
finalize_debug();
}
