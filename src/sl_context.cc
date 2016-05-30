#include "sl_context.h"
#include "noll_form.h"
#include "noll_entl.h"

using namespace std;

extern noll_entl_t* noll_prob;

void sl_context::init()
{
	Z3_config cfg;

	cfg = Z3_mk_config();
	z3_ctx = Z3_mk_context(cfg);
	Z3_del_config(cfg);

	isort = Z3_mk_int_sort(z3_ctx);
	bsort = Z3_mk_bool_sort(z3_ctx);

	noll_form_t* form = noll_prob->pform;
	for (size_t i = 0; i < noll_vector_size(form->lvars); ++i) {
		noll_var_t* v = noll_vector_at(form->lvars, i);
		Z3_symbol symbol = Z3_mk_string_symbol(z3_ctx, v->vname);
		Z3_ast node = Z3_mk_const(z3_ctx, symbol, isort);
		var.push_back(sl_var(i, node));
	}
}
/*
 *sl_context::sl_context(sl_context& c)
 *{
 *        z3_ctx = c.z3_ctx;
 *        isort = c.isort;
 *        bsort = c.bsort;
 *        var = c.var;
 *}
 *
 *sl_context& sl_context::operator=(sl_context& c)
 *{
 *        z3_ctx = c.z3_ctx;
 *        isort = c.isort;
 *        bsort = c.bsort;
 *        var = c.var;
 *        return *this;	
 *}
 */
size_t sl_context::get_var_size()
{
	return var.size();
}

Z3_context sl_context::get_z3_context()
{
	return z3_ctx;
}
Z3_sort sl_context::get_isort()
{
	return isort;
}

Z3_sort sl_context::get_bsort()
{
	return bsort;
}
Z3_ast sl_context::get_var_ast(size_t i)
{
	return var[i].node;
}
void sl_context::push_var(sl_var& v)
{
	var.push_back(v);
}
