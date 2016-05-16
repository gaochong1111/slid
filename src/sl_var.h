#ifndef SL_VAR_H
#define SL_VAR_H

#include <z3.h>

class sl_var {
public:
	sl_var(): sid(-1), type(nullptr), symbol(nullptr), node(nullptr) {}
	sl_var(size_t, Z3_sort, Z3_symbol, Z3_ast);
	sl_var(const sl_var&);
	sl_var(sl_var&&) noexcept;
	sl_var& operator=(sl_var&&) noexcept;
	sl_var& operator=(const sl_var&);

	size_t sid;
	Z3_sort type;
	Z3_symbol symbol;
	Z3_ast node;
};

#endif //sl_var.h
