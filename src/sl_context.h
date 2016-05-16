#ifndef SL_CONTEXT_H
#define SL_CONTEXT_H

#include <vector>
#include <z3.h>

#include "sl_var.h"

class sl_context {
public:
	sl_context(): z3_ctx(nullptr), isort(nullptr), bsort(nullptr) {}
	void init();
	size_t get_var_size();
	Z3_context get_z3_context();
	Z3_sort get_isort();
	Z3_sort get_bsort();
	Z3_ast get_var_ast(size_t);
	void push_var(sl_var&);

	Z3_context z3_ctx;
	Z3_sort isort;
	Z3_sort bsort;
	std::vector<sl_var> var;
};
#endif // sl_context.h
