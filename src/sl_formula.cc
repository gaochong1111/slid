#include <vector>

#include <z3.h>

#include "sl_formula.h"

#include "noll_form.h"
#include "slid_sat.h"

using namespace std;

/*
 *void test_check_sat(noll_form_t* form)
 *{
 *        int i;
 *        Z3_config cfg;
 *        Z3_context z3_ctx;
 *        Z3_sort int_sort, bool_sort;
 *        noll_var_t* v;
 *        Z3_ast tmp;
 *        vector<Z3_ast> var;
 *
 *        cfg = Z3_mk_config();
 *        z3_ctx = Z3_mk_context(cfg);
 *        Z3_del_config(cfg);
 *        int_sort = Z3_mk_int_sort(z3_ctx);
 *        bool_sort = Z3_mk_bool_sort(z3_ctx);
 *
 *        for(i = 0; i < noll_vector_size(form->lvars); i++){
 *                v = noll_vector_at(form->lvars, i);
 *                tmp = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, v->vname), int_sort);
 *                var.push_back(tmp);
 *        }
 *
 *        SLFormula slf(form, z3_ctx, int_sort, bool_sort, var);
 *        if (slf.issat())
 *                form->kind = NOLL_FORM_SAT;
 *        else
 *                form->kind = NOLL_FORM_UNSAT;
 *}
 */

SLFormula::SLFormula(noll_form_t* f, Z3_context ctx, Z3_sort is, Z3_sort bs, vector<Z3_ast>& v)
	: form(f), z3_ctx(ctx), isort(is), bsort(bs), var(v)
{
}

SLFormula::sl_sat_t SLFormula::issat()
{
	if (sat_tag == SL_SAT_UNKNOWN)
		check_sat();
	return kind;
}
SLFormula::sl_sat_t SLFormula::check_sat(Z3_ast z3_formula)
{
	Z3_solver s;
	s = Z3_mk_solver(z3_ctx);
	Z3_solver_inc_ref(z3_ctx, s);

	Z3_solver_assert(z3_ctx, s, z3_formula);
	
	switch(Z3_solver_check(z3_ctx, s)){
	case Z3_L_FALSE:
		return SL_SAT_UNSAT;
	case Z3_L_TRUE:
		return SL_SAT_SAT;
	case Z3_L_UNDEF:
		return SL_SAT_UNKNOWN;
	}
}
void SLFormula::check_sat()
{
	if (abstr == NULL) mk_abstr();
	if (kind != SL_SAT_UNKNOWN) return kind;

	switch(check_sat(abstr)){
	case SL_SAT_UNSAT:
		kind = SL_SAT_UNSAT;
		break;
	case SL_SAT_SAT:
		kind = SL_SAT_SAT;
		break;
	}
}

void SLFormula::mk_abstr()
{
	slid_context slid_ctx;
	slid_ctx = mk_slid_context();
	slid_mk_abstr(z3_ctx, slid_ctx, formula);
	mk_context(slid_ctx);
	abstr = slid_ctx->abstr;
}


void SLFormula::mk_context(slid_context slid_ctx)
{
	int i, j;
	slid_in_alloc_loc_array* s;
	shared_ptr<vector<IALoc> > t;
	for (i = 0; i < noll_vector_size(slid_ctx->k); ++i) {
		k.push_back(noll_vector_at(slid_ctx->k, i));
	}
	for (i = 0; i < noll_vector_size(slid_ctx->space); ++i) {
		space.push_back(noll_vector_at(slid_ctx->space, i));
	}
	for (i = 0; i < noll_vector_size(slid_ctx->m); ++i) {
		s = noll_vector_at(slid_ctx->m, i);
		t = make_shared<vector<IALoc> >();
		for (j = 0; j < noll_vector_size(s); ++j) {
			t->push_back(noll_vector_at(s, j));
		}
		m.push_back(t);
	}
	if (slid_ctx->sat_type == SLID_UNSAT)
		kind = SL_SAT_UNSAT;
}

slid_context SLFormula::mk_slid_context()
{
	unsigned int i, j;
	char *str;
	noll_var_t *v;
	Z3_ast tmp;
	noll_space_t *noll_space;

	if((form->lvars == NULL) || (noll_vector_empty(form->lvars))) return NULL;

	slid_context ret;

	ret = slid_init_context(z3_ctx);

	ret->int_sort = isort;
	ret->bool_sort = bsort;

	ret->var = z3_ast_array_new();
	for(i = 1; i < noll_vector_size(form->lvars); i++){
		v = noll_vector_at(form->lvars, i);
		if(v->vty->kind == NOLL_TYP_RECORD) ret->nLoc++;
	}

	for (auto it = begin(var); it != end(var); ++it) {
		z3_ast_array_push(ret->var, *it);
	}

	ret->space = NULL;
	if(form->space != NULL)
		slid_mk_space_array(&ret->space, form->space);
	if((ret->space != NULL) && (!noll_vector_empty(ret->space))){	
		ret->m = slid_mk_in_alloc_loc_arrays(z3_ctx, ret->bool_sort, form->lvars, ret->space);

		ret->k = z3_ast_array_new();

		for(i = 0; i < noll_vector_size(ret->space); i++){
			noll_space = noll_vector_at(ret->space, i);
			str = (char *)malloc(sizeof(char) * (strlen("slid_k_")+3));
			assert(str != NULL);
			sprintf(str, "slid_k_%d", i);
			z3_ast_array_push(ret->k, Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, str), ret->int_sort));
			
		}
	}

	return ret;
}

bool SLFormula::check_equal(size_t u, size_t v)
{
	Z3_ast eq, f;
	eq = Z3_mk_eq(z3_ctx, var[u], var[v]);
	f = Z3_mk_and(z3_ctx, abstr, Z3_mk_not(z3_ctx, eq));
	if (check_sat(f) == SL_SAT_UNSAT)
		return true;
	else
		return false;
}
bool SLFormula::check_unequal(size_t u, size_t v)
{
	Z3_ast eq, f;
	eq = Z3_mk_eq(z3_ctx, var[u], var[v]);
	f = Z3_mk_and(z3_ctx, abstr, eq);
	if (check_sat(f) == SL_SAT_UNSAT)
		return true;
	else
		return false;
}

int SLFormula::check_alloc(size_t i)
{
	Z3_ast zero, f, g;
	zero = Z3_mk_int(z3_ctx, 0);
	f = Z3_mk_and(z3_ctx, abstr, Z3_mk_eq(z3_ctx, k[i], zero));
	g = Z3_mk_and(z3_ctx, abstr, Z3_mk_gt(z3_ctx, k[i], zero));
	if (check_sat(f) == SL_SAT_UNSAT)
		return 1;
	if (check_sat(g) == SL_SAT_UNSAT)
		return -1;
	return 0;
}
