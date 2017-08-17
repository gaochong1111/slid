#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>

#include "slid_sat.h"
#include "noll_vector.h"
#include "noll_form.h"
#include "noll_preds.h"

#define slid_ctx_var_at(i) (noll_vector_at(slid_ctx->var, (i)))

NOLL_VECTOR_DEFINE(slid_data_constr_array, slid_data_constr *);
NOLL_VECTOR_DEFINE(z3_ast_array, Z3_ast);
NOLL_VECTOR_DEFINE(slid_in_alloc_loc_array, slid_in_alloc_loc *);
NOLL_VECTOR_DEFINE(slid_in_alloc_loc_arrays, slid_in_alloc_loc_array *);


extern noll_pred_array *preds_array;

/* --------------------------------------------------------------------------*/
/**
 * @synopsis  slid_sat_check
 *
 * @param form
 */
/* --------------------------------------------------------------------------*/
//check the formula sat or not
/**
 *@return 1, if sat
 0, if unsat
 3,if undef
*/
int slid_sat_check(noll_form_t *form)
{
	if (form == NULL || form->kind == NOLL_FORM_UNSAT)
	{
		return 0;
	}

	int ret;
	Z3_solver s;
	Z3_config cfg;
	Z3_context z3_ctx;
	Z3_model m = 0;
	slid_context slid_ctx;

	//init Z3 context
	cfg = Z3_mk_config();
	z3_ctx = Z3_mk_context(cfg);
	Z3_del_config(cfg);

	//init slid context
	slid_ctx = slid_mk_context(z3_ctx, form);

	//init Z3 solver
	s = Z3_mk_solver(z3_ctx);
	Z3_solver_inc_ref(z3_ctx, s);

	slid_mk_abstr(z3_ctx, slid_ctx, form);
	// print the abstr of phi
	// Z3_string abs_str = Z3_ast_to_string (z3_ctx, slid_ctx->abstr);

	// fprintf(stdout,"%s\n",abs_str);

	if(slid_ctx->sat_type == SLID_UNSAT) {
		// special case
		ret = SLID_UNSAT;
		form->kind = NOLL_FORM_UNSAT;
	} else {
//init assertion
		Z3_solver_assert(z3_ctx, s, slid_ctx->abstr);

		//check
		switch(Z3_solver_check(z3_ctx, s)){
		case Z3_L_FALSE:
			ret = SLID_UNSAT;
			form->kind = NOLL_FORM_UNSAT;
			break;
		case Z3_L_UNDEF:
			ret = SLID_UNDEF;
			form->kind = NOLL_FORM_OTHER;
			break;
		case Z3_L_TRUE:
			ret = SLID_SAT;
			form->kind = NOLL_FORM_SAT;
			m = Z3_solver_get_model(z3_ctx, s);
			if(m != 0){
				Z3_model_inc_ref(z3_ctx, m);
				printf("example:\n%s\n", Z3_model_to_string(z3_ctx, m));
			}
		}
	}

	Z3_del_context(z3_ctx);
	slid_del_context(slid_ctx);
	return ret;
}

void slid_mk_space_array(noll_space_array **space_arr, noll_space_t *space)
{
	if(space == NULL) return;

	unsigned int i;
	if(*space_arr == NULL)
		*space_arr = noll_space_array_new();

	switch(space->kind){
	case NOLL_SPACE_PTO:
		noll_space_array_push(*space_arr, space);
		break;
	case NOLL_SPACE_LS:
		noll_space_array_push(*space_arr, space);
		break;
	case NOLL_SPACE_SSEP:
		for(i = 0; i < noll_vector_size(space->m.sep); i++)
			slid_mk_space_array(space_arr, noll_vector_at(space->m.sep, i));
		break;
	}
}

void slid_del_context(slid_context slid_ctx)
{
	unsigned int i;
	for(i = 0; i < noll_vector_size(slid_ctx->m); i++)
		slid_in_alloc_loc_array_delete(noll_vector_at(slid_ctx->m, i));

	slid_in_alloc_loc_arrays_delete(slid_ctx->m);

	z3_ast_array_delete(slid_ctx->var);
	noll_space_array_delete(slid_ctx->space);
}

slid_context slid_init_context(Z3_context z3_ctx)
{
	slid_context ret;

	ret = (slid_context)malloc(sizeof(_slid_context));
	assert(ret != NULL);

	ret->nLoc = 0;
	ret->var = NULL;
	ret->k = NULL;
	ret->space = NULL;
	ret->m = NULL;
	ret->sat_type = SLID_SAT;
	ret->abstr = Z3_mk_true(z3_ctx);

	return ret;
}

slid_context slid_mk_context(Z3_context z3_ctx, noll_form_t *form)
{
	unsigned int i, j;
	char *str;
	noll_var_t *v;
	Z3_ast tmp;
	noll_space_t *space;

	if((form->lvars == NULL) || (noll_vector_empty(form->lvars))) return NULL;

	slid_context ret;

	ret = slid_init_context(z3_ctx);

	ret->int_sort = Z3_mk_int_sort(z3_ctx);
	ret->bool_sort = Z3_mk_bool_sort(z3_ctx);

	ret->var = z3_ast_array_new();
	v = noll_vector_at(form->lvars, 0);
	tmp = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, v->vname), ret->int_sort);
	z3_ast_array_push(ret->var, tmp);
	for(i = 1; i < noll_vector_size(form->lvars); i++){
		v = noll_vector_at(form->lvars, i);
		tmp = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, v->vname), ret->int_sort);
		z3_ast_array_push(ret->var, tmp);
		if(v->vty->kind == NOLL_TYP_RECORD) ret->nLoc++;
	}

	ret->space = NULL;
	if(form->space != NULL)
		slid_mk_space_array(&ret->space, form->space);
	if((ret->space != NULL) && (!noll_vector_empty(ret->space))){
		ret->m = slid_mk_in_alloc_loc_arrays(z3_ctx, ret->bool_sort, form->lvars, ret->space);

		ret->k = z3_ast_array_new();

		for(i = 0; i < noll_vector_size(ret->space); i++){
			space = noll_vector_at(ret->space, i);
			str = (char *)malloc(sizeof(char) * (strlen("slid_k_")+3));
			assert(str != NULL);
			sprintf(str, "slid_k_%d", i);
			z3_ast_array_push(ret->k, Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, str), ret->int_sort));

		}
	}

	return ret;
}

slid_in_alloc_loc_arrays* slid_mk_in_alloc_loc_arrays(Z3_context z3_ctx, Z3_sort bsort,\
													  noll_var_array* vars, noll_space_array* sa)
{
	unsigned int i;
	noll_space_t *space;
	slid_in_alloc_loc_arrays* ret = NULL;
	slid_in_alloc_loc_array* t;
	ret = slid_in_alloc_loc_arrays_new();
	for(i = 0; i < noll_vector_size(sa); i++){
		space = noll_vector_at(sa, i);
		switch(space->kind){
		case NOLL_SPACE_PTO:
			t = slid_mk_in_alloc_loc_array_pto(z3_ctx, bsort, vars, space->m.pto.sid, i);
			slid_in_alloc_loc_arrays_push(ret, t);
			break;
		case NOLL_SPACE_LS:
			t = slid_mk_in_alloc_loc_array_ls(z3_ctx, bsort, vars, &space->m.ls, i);
			slid_in_alloc_loc_arrays_push(ret, t);
			break;
		}
	}

	return ret;
}
slid_in_alloc_loc_array* slid_mk_in_alloc_loc_array_pto(Z3_context z3_ctx, Z3_sort bsort,\
														noll_var_array* vars,\
														unsigned int sid, unsigned int i)
{
	slid_in_alloc_loc_array* ret = NULL;
	ret = slid_in_alloc_loc_array_new();
	slid_in_alloc_loc *t;
	t = slid_mk_in_alloc_loc(z3_ctx, bsort, vars, sid, i);
	slid_in_alloc_loc_array_push(ret, t);
	return ret;
}
slid_in_alloc_loc* slid_mk_in_alloc_loc(Z3_context z3_ctx, Z3_sort bsort,\
										noll_var_array* vars,\
										unsigned int sid, unsigned int i)
{
	char *str;
	noll_var_t *var;
	slid_in_alloc_loc *t;
	t = (slid_in_alloc_loc *)malloc(sizeof(slid_in_alloc_loc));
	assert(t != NULL);

	var = noll_vector_at(vars, sid);
	str = (char *)malloc(sizeof(char)*(strlen(var->vname)+strlen("[,]")+3));
	assert(str != NULL);
	sprintf(str, "[%s, %d]", var->vname, i);
	t->sid = sid;
	t->bvar = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, str), bsort);
	return t;
}
void slid_get_in_alloc_loc_index(noll_uid_array *a, noll_ls_t *ls)
{
	int i, j, k;
	noll_pred_t * pred;
	noll_pred_rule_t *r;

	noll_uid_array_push(a, noll_vector_at(ls->args, 0));

	pred = noll_vector_at(preds_array, ls->pid);
	r = noll_vector_at(pred->def->rec_rules, 0);
	while((i = slid_get_trans_loc(r, 1)) > 0){
		j = slid_get_hole(pred) + i;
		k = noll_vector_at(ls->args, j);
		noll_uid_array_push(a, k);
	}
}
slid_in_alloc_loc_array* slid_mk_in_alloc_loc_array_ls(Z3_context z3_ctx, Z3_sort bsort,\
													   noll_var_array *vars, noll_ls_t* ls,\
													   unsigned int i)
{
	unsigned int k;
	noll_uid_array *t;
	slid_in_alloc_loc *t1;
	slid_in_alloc_loc_array *t2;
	t = noll_uid_array_new();
	t2 = slid_in_alloc_loc_array_new();
	slid_get_in_alloc_loc_index(t, ls);
	for(k = 0; k < noll_vector_size(t); k++){
		t1 = slid_mk_in_alloc_loc(z3_ctx, bsort, vars, noll_vector_at(t, k), i);
		slid_in_alloc_loc_array_push(t2, t1);
	}
	noll_uid_array_delete(t);
	return t2;
}

slid_in_alloc_loc *slid_in_alloc_loc_locate(slid_in_alloc_loc_arrays *m, unsigned int k, unsigned int i)
{
	slid_in_alloc_loc_array *t1;
	slid_in_alloc_loc *t2;
	t1 = noll_vector_at(m, k);
	t2 = noll_vector_at(t1, i);
	return t2;
}

Z3_ast slid_in_alloc_loc_find(slid_in_alloc_loc_arrays *m, unsigned int k, unsigned int sid)
{
	unsigned int i;
	slid_in_alloc_loc_array *t;
	slid_in_alloc_loc *t1;
	t = noll_vector_at(m, k);
	for(i = 0; i < noll_vector_size(t); i++){
		t1 = noll_vector_at(t, i);
		if(t1->sid == sid)
			return t1->bvar;
	}
	return NULL;
}

void slid_mk_abstr(Z3_context z3_ctx, slid_context slid_ctx, noll_form_t *f)
{
	assert(f != NULL);

	Z3_solver s;

	s = Z3_mk_solver(z3_ctx);
	Z3_solver_inc_ref(z3_ctx, s);

	if(f->pure != NULL)
		slid_mk_pure_abstr(z3_ctx, slid_ctx, f->pure);

	Z3_solver_assert(z3_ctx, s, slid_ctx->abstr);
	if(Z3_solver_check(z3_ctx, s) == Z3_L_FALSE){
		slid_ctx->sat_type = SLID_UNSAT;
		f->kind = NOLL_FORM_UNSAT;
		return;
	}

	if((slid_ctx->space != NULL) && (!noll_vector_empty(slid_ctx->space)))
		slid_mk_space_abstr(z3_ctx, slid_ctx);
}


void slid_mk_pure_abstr(Z3_context z3_ctx, slid_context slid_ctx, noll_pure_t *pure)
{
	assert(pure != NULL);

	unsigned int i, j, k;
	Z3_ast t1, t2, t3;
	noll_dform_t *t4;
	z3_ast_array *t;

	t = z3_ast_array_new();
	z3_ast_array_push(t, slid_ctx->abstr);
	if((pure->m != NULL) && (pure->size > 0)){
		for(i = 0; i < pure->size-1; i++){
			for(j = 1; j < pure->size-i; j++){
				t1 = noll_vector_at(slid_ctx->var, i);
				t2 = noll_vector_at(slid_ctx->var, i+j);
				if(pure->m[i][j] == NOLL_PURE_EQ){
					t3 = Z3_mk_eq(z3_ctx, t1, t2);
					z3_ast_array_push(t, t3);
				}
				if(pure->m[i][j] == NOLL_PURE_NEQ){
					t3 = Z3_mk_eq(z3_ctx, t1, t2);
					z3_ast_array_push(t, Z3_mk_not(z3_ctx, t3));
				}
			}
		}
	}

	if((pure->data != NULL) && (!noll_vector_empty(pure->data))){
		for(k = 0; k < noll_vector_size(pure->data); k++){
			t4 = noll_vector_at(pure->data, k);
			t1 = slid_mk_pure_data_constr(z3_ctx, slid_ctx, t4);
			if(t1 != NULL) z3_ast_array_push(t, t1);
		}
	}

	slid_ctx->abstr = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);
}

Z3_ast slid_mk_pure_data_constr(Z3_context z3_ctx, slid_context slid_ctx, noll_dform_t *data)
{
	assert(data != NULL);

	Z3_ast (*fun_arr1[])(Z3_context, Z3_ast, Z3_ast)\
		= {Z3_mk_eq, Z3_mk_lt, Z3_mk_gt, Z3_mk_le, Z3_mk_ge};
	Z3_ast (*fun_arr2[])(Z3_context, unsigned int, Z3_ast const[])\
		= {Z3_mk_distinct, Z3_mk_add, Z3_mk_sub};

	switch(data->kind){
	case NOLL_DATA_EQ:
	case NOLL_DATA_LT:
	case NOLL_DATA_GT:
	case NOLL_DATA_LE:
	case NOLL_DATA_GE:
		return _slid_mk_pure_data_constr1(z3_ctx, slid_ctx, data->p.targs, fun_arr1[data->kind]);
	case NOLL_DATA_NEQ:
	case NOLL_DATA_PLUS:
	case NOLL_DATA_MINUS:
		return _slid_mk_pure_data_constr2(z3_ctx, slid_ctx, data->p.targs, fun_arr2[data->kind-5]);
	case NOLL_DATA_IMPLIES:
		return slid_mk_implies(z3_ctx, slid_ctx, data->p.bargs);
	default:
		printf("Unsurport operator!\n");
		exit(1);
	}
}

Z3_ast _slid_mk_pure_data_constr1(Z3_context z3_ctx, slid_context slid_ctx,\
								  noll_dterm_array * terms, Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast))
{
	assert(terms != NULL);
	assert(noll_vector_size(terms) > 1);

	unsigned int i;
	Z3_ast a1, a2, ret = NULL;
	z3_ast_array *t;

	t = z3_ast_array_new();
	for(i = 0; i < noll_vector_size(terms)-1; i++){
		a1 = slid_mk_term(z3_ctx, slid_ctx, noll_vector_at(terms, i));
		a2 = slid_mk_term(z3_ctx, slid_ctx, noll_vector_at(terms, i+1));
		z3_ast_array_push(t, f(z3_ctx, a1, a2));
	}
	if(!noll_vector_empty(t))
		ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}


Z3_ast _slid_mk_pure_data_constr2(Z3_context z3_ctx, slid_context slid_ctx,\
								  noll_dterm_array *terms, Z3_ast (*f)(Z3_context, unsigned int, Z3_ast const[]))
{
	assert(terms != NULL);
	assert(noll_vector_size(terms) > 1);

	unsigned int i;
	z3_ast_array *t;
	Z3_ast t1, ret = NULL;

	t = z3_ast_array_new();
	for(i = 0; i < noll_vector_size(terms); i++){
		t1 = slid_mk_term(z3_ctx, slid_ctx, noll_vector_at(terms, i));
		if(t1 != NULL) z3_ast_array_push(t, t1);
	}

	if(!noll_vector_empty(t))
		ret = f(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

Z3_ast slid_mk_ite(Z3_context z3_ctx, slid_context slid_ctx, noll_dterm_t *term)
{
	assert(term != NULL);
	assert(term->args != NULL);
	assert(noll_vector_size(term->args) == 2);

	Z3_ast cond, s, t;


	cond = slid_mk_pure_data_constr(z3_ctx, slid_ctx, term->p.cond);
	s = slid_mk_term(z3_ctx, slid_ctx, noll_vector_at(term->args, 0));
	t = slid_mk_term(z3_ctx, slid_ctx, noll_vector_at(term->args, 1));


	return Z3_mk_ite(z3_ctx, cond, s, t);
}


Z3_ast slid_mk_implies(Z3_context z3_ctx, slid_context slid_ctx, noll_dform_array *forms)
{
	assert(forms != NULL);
	assert(noll_vector_size(forms) > 1);

	int i;
	noll_dform_t *df;
	Z3_ast t, ret = NULL;


	df = noll_vector_at(forms, noll_vector_size(forms)-1);
	ret = slid_mk_pure_data_constr(z3_ctx, slid_ctx, df);
	for(i = noll_vector_size(forms)-2; i >= 0; i--){
		df = noll_vector_at(forms, i);
		t = slid_mk_pure_data_constr(z3_ctx, slid_ctx, df);
		ret = Z3_mk_implies(z3_ctx, t, ret);
	}

	return ret;
}

Z3_ast slid_mk_term(Z3_context z3_ctx, slid_context slid_ctx, noll_dterm_t *term)
{
	assert(term != NULL);

	Z3_ast (*fun_arr1[])(Z3_context, Z3_ast, Z3_ast)\
		= {Z3_mk_eq, Z3_mk_lt, Z3_mk_gt, Z3_mk_le, Z3_mk_ge};
	Z3_ast (*fun_arr2[])(Z3_context, unsigned int, Z3_ast const[])\
		= {Z3_mk_distinct, Z3_mk_add, Z3_mk_sub};

	switch(term->kind){
	case NOLL_DATA_EQ:
	case NOLL_DATA_LT:
	case NOLL_DATA_GT:
	case NOLL_DATA_LE:
	case NOLL_DATA_GE:
		return _slid_mk_pure_data_constr1(z3_ctx, slid_ctx, term->args, fun_arr1[term->kind]);
	case NOLL_DATA_NEQ:
	case NOLL_DATA_PLUS:
	case NOLL_DATA_MINUS:
		return _slid_mk_pure_data_constr2(z3_ctx, slid_ctx, term->args, fun_arr2[term->kind-5]);
	case NOLL_DATA_INT:
		return Z3_mk_int(z3_ctx, term->p.value, slid_ctx->int_sort);
	case NOLL_DATA_VAR:
		return noll_vector_at(slid_ctx->var,term->p.sid);
	case NOLL_DATA_ITE:
		return slid_mk_ite(z3_ctx, slid_ctx, term);
	default:
		printf("Unsurport operator of data constraints!\n");
		exit(1);
	}
}


void slid_mk_space_abstr(Z3_context z3_ctx, slid_context slid_ctx)
{
	unsigned int i;
	z3_ast_array *t;
	noll_space_t *t1;
	Z3_ast t2, t3;

	t = z3_ast_array_new();
	z3_ast_array_push(t, slid_ctx->abstr);
	for(i = 0; i < noll_vector_size(slid_ctx->space); i++){
		t1 = noll_vector_at(slid_ctx->space, i);
		switch(t1->kind){
		case NOLL_SPACE_PTO:
			t2 = slid_mk_pto(z3_ctx, slid_ctx, &(t1->m.pto), i);
			if(t2 != NULL) z3_ast_array_push(t, t2);
			break;
		case NOLL_SPACE_LS:
			t2 = slid_mk_pred(z3_ctx, slid_ctx, &(t1->m.ls), i);
			if(t2 != NULL) z3_ast_array_push(t, t2);
			break;
		}
	}

	t3 = slid_mk_sep_constr(z3_ctx, slid_ctx);
	if(t3 != NULL) z3_ast_array_push(t, t3);

	slid_ctx->abstr = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);
}

Z3_ast slid_mk_pto(Z3_context z3_ctx, slid_context slid_ctx, noll_pto_t *pto, int k)
{
	assert(pto != NULL);

	Z3_ast r[2], t1, t2;
	Z3_ast ki, one;
	one = Z3_mk_int(z3_ctx, 1, slid_ctx->int_sort);
	ki = noll_vector_at(slid_ctx->k, k);
	r[0] = Z3_mk_eq(z3_ctx, ki, one);

	t1 = slid_in_alloc_loc_find(slid_ctx->m, k, pto->sid);
	assert(t1 != NULL);
	t2 = Z3_mk_true(z3_ctx);
	r[1] = Z3_mk_eq(z3_ctx, t1, t2);

	return Z3_mk_and(z3_ctx, 2, r);
}

Z3_ast slid_mk_pred(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int k)
{
	assert(pred != NULL);

	int n1, n2, n3;
	z3_ast_array *t, *t1;
	Z3_ast t2 = NULL, t3 = NULL, t4 = NULL,\
		t5 = NULL, t6 = NULL, t7 = NULL,\
		t8 = NULL, t9 = NULL, t10 = NULL, t11 = NULL, ret = NULL;
	noll_pred_t *ppred;
	noll_pred_rule_t *rr;

	ppred = noll_vector_at(preds_array, pred->pid);
	rr = noll_vector_at(ppred->def->rec_rules, 0);

	t = z3_ast_array_new();
	t1 = z3_ast_array_new();
	t10 = slid_in_alloc_loc_find(slid_ctx->m, k, noll_vector_at(pred->args, 0));
	assert(t10 != NULL);
	t11 = Z3_mk_false(z3_ctx);
	z3_ast_array_push(t, Z3_mk_eq(z3_ctx, t10, t11));

	if(ppred->typ->nDir >= 2){
		while((n1 = slid_get_trans_loc(rr, 1)) > 0){
			n2 = slid_get_hole(ppred) + n1;
			n3 = noll_vector_at(pred->args, n2);
			t8 = slid_in_alloc_loc_find(slid_ctx->m, k, n3);
			assert(t8 != NULL);
			t9 = Z3_mk_false(z3_ctx);
			z3_ast_array_push(t, Z3_mk_eq(z3_ctx, t8, t9));
		}
	}


	t2 = slid_mk_unfold(z3_ctx, slid_ctx, pred, k);
	if(t2 != NULL) z3_ast_array_push(t, t2);

	t2 = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_clear(t);
	z3_ast_array_push(t, t2);

	t3 = slid_mk_fir_unfold(z3_ctx, slid_ctx, pred, k);
	if(t3 != NULL) z3_ast_array_push(t1, t3);

	t4 = slid_mk_sec_unfold(z3_ctx, slid_ctx, pred, k);
	if(t4 != NULL) z3_ast_array_push(t1, t4);

	t5 = Z3_mk_or(z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
	z3_ast_array_clear(t1);
	if(t5 != NULL) z3_ast_array_push(t1, t5);
	t6 = slid_in_alloc_loc_find(slid_ctx->m, k, noll_vector_at(pred->args, 0));
	assert(t6 != NULL);
	t3 = Z3_mk_true(z3_ctx);
	z3_ast_array_push(t1, Z3_mk_eq(z3_ctx, t6, t3));
	t7 = slid_mk_closures(z3_ctx, slid_ctx, pred, k);
	if(t7 != NULL) z3_ast_array_push(t1, t7);
	t3 = Z3_mk_and(z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
	if(t3 != NULL) z3_ast_array_push(t, t3);

	ret = Z3_mk_or(z3_ctx, noll_vector_size(t), noll_vector_array(t));

	z3_ast_array_delete(t);
	z3_ast_array_delete(t1);

	return ret;
}


Z3_ast slid_mk_unfold(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int ki)
{
	unsigned int i, j, k;
	z3_ast_array * t, *t1;
	Z3_ast t2, t3, t4, t5, ret = NULL;
	noll_pred_t *ppred;
	noll_pred_rule_t *br;

	t = z3_ast_array_new();
	ppred = noll_vector_at(preds_array, pred->pid);

	for(k = 0; k < noll_vector_size(ppred->def->base_rules); k++){
		t1 = z3_ast_array_new();
		br = noll_vector_at(ppred->def->base_rules, k);



		assert(br->pure->m != NULL);
		assert(br->pure->size > 0);
		for(i = 0; i < br->pure->size-1; i++){
			for(j = 1; j < br->pure->size-i; j++){
				if(i == 0)
					t2 = noll_vector_at(slid_ctx->var, 0);
				else
					t2 = slid_ctx_var_at(noll_vector_at(pred->args, i-1));
				t3 = slid_ctx_var_at(noll_vector_at(pred->args, i+j-1));
				if(br->pure->m[i][j] == NOLL_PURE_EQ){
					t4 = Z3_mk_eq(z3_ctx, t2, t3);
					z3_ast_array_push(t1, Z3_mk_eq(z3_ctx, t2, t3));
				}
				if(br->pure->m[i][j] == NOLL_PURE_NEQ){
					t4 = Z3_mk_eq(z3_ctx, t2, t3);
					z3_ast_array_push(t1, Z3_mk_not(z3_ctx, t4));
				}
			}
		}
		t5 = Z3_mk_and(z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
		z3_ast_array_push(t, t5);
		z3_ast_array_delete(t1);

	}
	t4 = Z3_mk_or(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_clear(t);
	z3_ast_array_push(t, t4);

	t2 = noll_vector_at(slid_ctx->k, ki);
	t3 = Z3_mk_int(z3_ctx, 0, slid_ctx->int_sort);
	z3_ast_array_push(t, Z3_mk_eq(z3_ctx, t2, t3));

	ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}
Z3_ast slid_mk_fir_unfold(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int k)
{
	assert(pred->pid >= 0);
	assert(pred->pid < noll_vector_size(preds_array));

	int i, n1, n2;
	noll_pred_t *ppred;
	z3_ast_array *t;
	noll_pred_rule_t *r;
	Z3_ast t1, t2, t3, ret = NULL;

	t = z3_ast_array_new();

	ppred = noll_vector_at(preds_array, pred->pid);

	r = noll_vector_at(ppred->def->rec_rules, 0);

	if(ppred->typ->nDir >= 2){
		while((n1 = slid_get_trans_loc(r, 1)) > 0){
			n2 = slid_get_hole(ppred) + n1;
			t1 = slid_ctx_var_at(noll_vector_at(pred->args, 0));
			t2 = slid_ctx_var_at(noll_vector_at(pred->args, n2));
			z3_ast_array_push(t, Z3_mk_eq(z3_ctx, t1, t2));

			i = noll_vector_at(pred->args, n2);

			t1 = slid_in_alloc_loc_find(slid_ctx->m, k, i);
			assert(t1 != NULL);
			t2 = Z3_mk_true(z3_ctx);
			z3_ast_array_push(t, Z3_mk_eq(z3_ctx, t1, t2));
		}
	}

	t1 = noll_vector_at(slid_ctx->k, k);
	t2 = Z3_mk_int(z3_ctx, 1, slid_ctx->int_sort);
	t3 = Z3_mk_eq(z3_ctx, t1, t2);
	z3_ast_array_push(t, t3);

	ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}
Z3_ast slid_mk_sec_unfold(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int k)
{
	assert(pred->pid >= 0);
	assert(pred->pid < noll_vector_size(preds_array));

	int i, n1, n2;
	noll_pred_t *ppred;
	z3_ast_array *t;
	noll_pred_rule_t *r;
	Z3_ast t1, t2, t3, ret = NULL;

	t = z3_ast_array_new();

	ppred = noll_vector_at(preds_array, pred->pid);
	r = noll_vector_at(ppred->def->rec_rules, 0);

	if(ppred->typ->nDir >= 2){
		while((n1 = slid_get_trans_loc(r, 1)) > 0){
			n2 = slid_get_hole(ppred) + n1;
			t1 = slid_ctx_var_at(noll_vector_at(pred->args, 0));
			t2 = slid_ctx_var_at(noll_vector_at(pred->args, n2));
			t3 = Z3_mk_eq(z3_ctx, t1, t2);
			z3_ast_array_push(t, Z3_mk_not(z3_ctx, t3));

			i = noll_vector_at(pred->args, n2);

			t1 = slid_in_alloc_loc_find(slid_ctx->m, k, i);
			assert(t1 != NULL);
			t2 = Z3_mk_true(z3_ctx);
			z3_ast_array_push(t, Z3_mk_eq(z3_ctx, t1, t2));
		}
	}

	t1 = noll_vector_at(slid_ctx->k, k);
	t2 = Z3_mk_int(z3_ctx, 2, slid_ctx->int_sort);
	t3 = Z3_mk_ge(z3_ctx, t1, t2);
	z3_ast_array_push(t, t3);

	ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

int slid_get_hole(noll_pred_t *pred)
{
	assert(pred != NULL);

	unsigned int i;

	for(i = 0; i < noll_vector_size(pred->typ->argkind); i++){
		if(noll_vector_at(pred->typ->argkind, i) == NOLL_ATYP_LPENDING)
			return i;
	}

	return -1;
}

Z3_ast slid_mk_closures(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int k)
{
	assert(pred != NULL);

	unsigned int i, j;
	z3_ast_array *t, *t1;
	slid_data_constr_array *t2;
	slid_data_constr *t3;
	Z3_ast t4, ret = NULL;
	noll_pred_t *ppred;
	noll_pred_rule_array *rr;
	noll_pred_rule_t *r;
	noll_dform_array *dfs;
	slid_data_constr *dc;

	t = z3_ast_array_new();
	ppred = noll_vector_at(preds_array, pred->pid);
	rr = ppred->def->rec_rules;

	t1 = z3_ast_array_new();
	t2 = slid_data_constr_array_new();
	for(i = 0; i < noll_vector_size(rr); i++){

		r = noll_vector_at(rr, i);
		dfs = r->pure->data;

		j = ppred->typ->nDir+1;
		for(j; j <= (unsigned int)slid_get_hole(ppred); j++){
			t3 = slid_get_pred_data_constr(ppred, r, j);
			slid_data_constr_array_push(t2, t3);
		}

		for(j = 0; j < noll_vector_size(t2); j++){
			dc = noll_vector_at(t2, j);
			t4 = slid_mk_closure(z3_ctx, slid_ctx, dc, pred, k);
			if(t4 != NULL) z3_ast_array_push(t1, t4);
		}
		if(!noll_vector_empty(t1)){
			t4 = Z3_mk_and(z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
			z3_ast_array_push(t, t4);

			z3_ast_array_clear(t1);

			for (j = 0; j < noll_vector_size(t2); j++)
				slid_del_pred_data_constr(noll_vector_at(t2, j));
			slid_data_constr_array_clear(t2);
		}
	}

	if(!noll_vector_empty(t))
		ret = Z3_mk_or(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

slid_data_constr *slid_get_pred_data_constr(noll_pred_t *p, noll_pred_rule_t *r, unsigned int sid)
{
	slid_data_constr *ret;

	ret = (slid_data_constr *)malloc(sizeof(slid_data_constr));
	assert(ret != NULL);

	ret->sid = sid;
	ret->ce = slid_get_pred_data_constr_ce(p, r, sid);
	ret->cl = slid_get_pred_data_constr_clg(r, sid, NOLL_DATA_LE);
	ret->cg = slid_get_pred_data_constr_clg(r, sid, NOLL_DATA_GE);
	ret->stc = slid_get_pred_data_constr_stc(p, r, sid);
	ret->trans = slid_get_pred_data_constr_trans(p, r, sid);

	return ret;
}

void slid_del_pred_data_constr(slid_data_constr *dc)
{
	if(dc->ce != NULL)
		noll_dform_array_delete(dc->ce);
	if(dc->stc != NULL)
		noll_dform_array_delete(dc->stc);
	if(dc->trans != NULL)
		noll_dform_array_delete(dc->trans);
}

noll_ls_t *slid_get_rule_pred(noll_space_t *s)
{
	unsigned int i;
	noll_ls_t *ret;

	switch(s->kind){
	case NOLL_SPACE_PTO:
		return NULL;
	case NOLL_SPACE_LS:
		return &(s->m.ls);
	case NOLL_SPACE_SSEP:
		for(i = 0; i < noll_vector_size(s->m.sep); i++){
			ret = slid_get_rule_pred(noll_vector_at(s->m.sep, i));
			if(ret != NULL) return ret;
		}
	}
	return NULL;
}
int slid_get_trans_loc(noll_pred_rule_t *r, unsigned int sid)
{
	static unsigned int i;
	noll_ls_t *p;

	p = slid_get_rule_pred(r->rec);

	for(++i; i < noll_vector_size(p->args); i++){
		if(noll_vector_at(p->args, i) == sid)
			return i;
	}

	i = 0;
	return 0;
}

bool slid_is_trans_para(unsigned int sid0, unsigned int sid1, noll_pred_rule_t *r)
{
	unsigned int i;
	noll_ls_t *p;

	p = slid_get_rule_pred(r->rec);

	i = noll_vector_at(p->args, sid0-1);
	if(i == sid1) return true;
	else return false;
}
slid_data_constr_t slid_get_pred_data_constr_type(noll_pred_t *p, noll_pred_rule_t *r, noll_dform_t *df)
{
	noll_dterm_t *t1, *t2, *t3, *t4;

	if((df->kind == NOLL_DATA_EQ)\
	   || (df->kind == NOLL_DATA_LE)\
	   || (df->kind == NOLL_DATA_GE)){
		t1 = noll_vector_at(df->p.targs, 0);
		t2 = noll_vector_at(df->p.targs, 1);
		if((t1->kind == NOLL_DATA_VAR)\
		   && (noll_vector_at(p->typ->argkind, t1->p.sid-1) == NOLL_ATYP_IROOT)){
			switch(t2->kind){
			case NOLL_DATA_INT:
				return SLID_DATA_CONSTR_CONST;
			case NOLL_DATA_VAR:
				if(t2->p.sid <= p->def->fargs)
					return SLID_DATA_CONSTR_STATIC;
				if(slid_is_trans_para(t1->p.sid, t2->p.sid, r))
					return SLID_DATA_CONSTR_TRANS;
				break;
			case NOLL_DATA_PLUS:
				t3 = noll_vector_at(t2->args, 0);
				t4 = noll_vector_at(t2->args, 1);
				if((t3->kind == NOLL_DATA_VAR)\
				   && (t3->p.sid <= p->def->fargs))
					return SLID_DATA_CONSTR_STATIC;
				if((t3->kind == NOLL_DATA_VAR)\
				   && (t3->p.sid > p->def->fargs)\
				   && (slid_is_trans_para(t1->p.sid, t3->p.sid, r))\
				   && (t4->kind == NOLL_DATA_INT))
					return SLID_DATA_CONSTR_TRANS;
				break;
			}
		}
	}

	return SLID_DATA_CONSTR_UNDEF;
}

noll_dform_array *slid_get_pred_data_constr_ce(noll_pred_t *p, noll_pred_rule_t *r, unsigned int sid)
{
	noll_dform_array *dfs;
	noll_dform_t *df;
	noll_dform_array *t;
	unsigned int i;

	dfs = r->pure->data;

	if(dfs == NULL) return NULL;

	t = noll_dform_array_new();
	for(i = 0; i < noll_vector_size(dfs); i++){
		df = noll_vector_at(dfs, i);
		if((df->kind == NOLL_DATA_EQ)\
		   && (noll_vector_at(df->p.targs, 0)->kind == NOLL_DATA_VAR)\
		   && (noll_vector_at(df->p.targs, 0)->p.sid == sid)\
		   && (slid_get_pred_data_constr_type(p, r, df) == SLID_DATA_CONSTR_CONST))
			noll_dform_array_push(t, df);
	}
	if(noll_vector_empty(t))
		return NULL;
	return t;
}

noll_dform_t *slid_get_pred_data_constr_clg(noll_pred_rule_t *r,unsigned int sid, noll_data_op_t op_t)
{
	noll_dform_array *dfs;
	noll_dform_t *df;
	noll_dform_t *ret = NULL;
	noll_dterm_t *t1, *t2;
	unsigned int i;
	int c;
	int f=0;

	dfs = r->pure->data;

	if(dfs == NULL) return NULL;

	for(i = 0; i < noll_vector_size(dfs); i++){
		df = noll_vector_at(dfs, i);
		if(df->kind == op_t){
			t1 = noll_vector_at(df->p.targs, 0);
			t2 = noll_vector_at(df->p.targs, 1);
			if((t1->kind == NOLL_DATA_VAR)\
			   && (t1->p.sid == sid)\
			   && (t2->kind == NOLL_DATA_INT)){
				if(f == 0){
					f = 1;
					ret = df;
					c = t2->p.value;
				}
				switch(op_t){
				case NOLL_DATA_LE:
					if(c > t2->p.value){
						ret = df;
						c = t2->p.value;
					}
					break;
				case NOLL_DATA_GE:
					if(c < t2->p.value){
						ret = df;
						c = t2->p.value;
					}
					break;
				}
			}
		}
	}
	return ret;
}

noll_dform_array *slid_get_pred_data_constr_stc(noll_pred_t *p, noll_pred_rule_t *r, unsigned int sid)
{
	noll_dform_array *t;
	noll_dform_array *dfs;
	noll_dform_t *df;
	unsigned int i;

	dfs = r->pure->data;

	if(dfs == NULL) return NULL;

	t = noll_dform_array_new();
	for(i = 0; i < noll_vector_size(dfs); i++){
		df = noll_vector_at(dfs, i);
		if((noll_vector_at(df->p.targs, 0)->p.sid == sid)\
		   && (slid_get_pred_data_constr_type(p, r, df) == SLID_DATA_CONSTR_STATIC))
			noll_dform_array_push(t, df);
	}
	if(noll_vector_empty(t))
		return NULL;
	return t;
}
noll_dform_array *slid_get_pred_data_constr_trans(noll_pred_t *p, noll_pred_rule_t *r, unsigned int sid)
{
	noll_dform_array *dfs;
	noll_dform_t *df;
	noll_dform_array *t;
	unsigned int i;

	dfs = r->pure->data;

	if(dfs == NULL) return NULL;

	t = noll_dform_array_new();
	for(i = 0; i < noll_vector_size(dfs); i++){
		df = noll_vector_at(dfs, i);
		if((noll_vector_at(df->p.targs, 0)->p.sid == sid)\
		   && (slid_get_pred_data_constr_type(p, r, df) == SLID_DATA_CONSTR_TRANS))
			noll_dform_array_push(t, df);
	}
	if(noll_vector_empty(t))
		return NULL;
	return t;
}
Z3_ast slid_mk_closure(Z3_context z3_ctx, slid_context slid_ctx, slid_data_constr *dc, noll_ls_t *p, int k)
{
	noll_dform_t *df;
	z3_ast_array *t;
	Z3_ast t1, ret;

	t = z3_ast_array_new();
	assert(t != NULL);

	t1 = slid_mk_pred_data_constr_cst(z3_ctx, slid_ctx, dc, p);
	if(t1 != NULL) z3_ast_array_push(t, t1);

	t1 = slid_mk_pred_data_constr_stc(z3_ctx, slid_ctx, dc, p);
	if(t1 != NULL) z3_ast_array_push(t, t1);

	if(dc->trans != NULL){
		t1 = slid_mk_pred_data_constr_trans(z3_ctx, slid_ctx, dc, p, k);
		if(t1 != NULL) z3_ast_array_push(t, t1);
	}

	if(noll_vector_empty(t))
		ret = NULL;
	else
		ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));

	z3_ast_array_delete(t);
	return ret;
}
Z3_ast slid_mk_pred_data_constr_cst(Z3_context z3_ctx, slid_context slid_ctx, slid_data_constr *dc, noll_ls_t *p)
{
	unsigned int i;
	noll_dform_t *df;
	z3_ast_array *t;
	Z3_ast t1, ret = NULL;

	t = z3_ast_array_new();
	if(dc->ce != NULL){
		for(i = 0; i < noll_vector_size(dc->ce); i++){
			df = noll_vector_at(dc->ce, i);
			t1 = _slid_mk_pred_data_constr_cst(z3_ctx, slid_ctx, df, p);
			if(t1 != NULL) z3_ast_array_push(t, t1);
		}
	}

	if(dc->cl != NULL){
		t1 = _slid_mk_pred_data_constr_cst(z3_ctx, slid_ctx, dc->cl, p);
		if(t1 != NULL) z3_ast_array_push(t, t1);
	}

	if(dc->cg != NULL){
		t1 = _slid_mk_pred_data_constr_cst(z3_ctx, slid_ctx, dc->cg, p);
		if(t1 != NULL) z3_ast_array_push(t, t1);
	}

	if(noll_vector_empty(t))
		ret = NULL;
	else
		ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

Z3_ast _slid_mk_pred_data_constr_cst(Z3_context z3_ctx, slid_context slid_ctx,\
									 noll_dform_t *dform, noll_ls_t *pred)
{
	int c;
	Z3_ast a, b;

	a = slid_ctx_var_at(noll_vector_at(pred->args, noll_vector_at(dform->p.targs, 0)->p.sid-1));
	c = noll_vector_at(dform->p.targs, 1)->p.value;
	b = Z3_mk_int(z3_ctx, c, slid_ctx->int_sort);
	switch(dform->kind){
	case NOLL_DATA_EQ:
		return Z3_mk_eq(z3_ctx, a, b);
	case NOLL_DATA_LE:
		return Z3_mk_le(z3_ctx, a, b);
	case NOLL_DATA_GE:
		return Z3_mk_ge(z3_ctx, a, b);
	}
	return NULL;
}

Z3_ast slid_mk_pred_data_constr_stc(Z3_context z3_ctx, slid_context slid_ctx,\
									slid_data_constr *dc, noll_ls_t *p)
{
	unsigned int i;
	noll_dform_t *df;
	z3_ast_array *t;
	Z3_ast t1, ret = NULL;

	if((dc->stc != NULL) && (!noll_vector_empty(dc->stc))){
		t = z3_ast_array_new();
		for(i = 0; i < noll_vector_size(dc->stc); i++){
			df = noll_vector_at(dc->stc, i);
			switch(df->kind){
			case NOLL_DATA_EQ:
				t1 = _slid_mk_pred_data_constr_stc(z3_ctx, slid_ctx, df, p, Z3_mk_eq);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			case NOLL_DATA_LE:
				t1 = _slid_mk_pred_data_constr_stc(z3_ctx, slid_ctx, df, p, Z3_mk_le);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			case NOLL_DATA_GE:
				t1 = _slid_mk_pred_data_constr_stc(z3_ctx, slid_ctx, df, p, Z3_mk_ge);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			}
		}
		if(noll_vector_empty(t))
			ret = NULL;
		else
			ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));

		z3_ast_array_delete(t);
	}


	return ret;
}

Z3_ast _slid_mk_pred_data_constr_stc(Z3_context z3_ctx, slid_context slid_ctx,\
									 noll_dform_t *df, noll_ls_t *p,\
									 Z3_ast (*op_func)(Z3_context, Z3_ast, Z3_ast))
{
	noll_dterm_t *t1, *t2, *t3, *t4;
	Z3_ast a, b;
	Z3_ast c[2];
	Z3_ast d[2];

	t1 = noll_vector_at(df->p.targs, 0);
	t2 = noll_vector_at(df->p.targs, 1);

	a = slid_ctx_var_at(noll_vector_at(p->args, t1->p.sid-1));
	switch(t2->kind){
	case NOLL_DATA_VAR:
		b = slid_ctx_var_at(noll_vector_at(p->args, t2->p.sid-1));
		return op_func(z3_ctx, a, b);
	case NOLL_DATA_PLUS:
		t3 = noll_vector_at(t2->args, 0);
		t4 = noll_vector_at(t2->args, 1);
		c[0] = slid_ctx_var_at(noll_vector_at(p->args, t3->p.sid-1));
		c[1] = Z3_mk_int(z3_ctx, t4->p.value, slid_ctx->int_sort);
		b = Z3_mk_add(z3_ctx, 2, c);
		return op_func(z3_ctx, a, b);
	}

	return NULL;
}


Z3_ast slid_mk_pred_data_constr_trans(Z3_context z3_ctx, slid_context slid_ctx,\
									  slid_data_constr *dc, noll_ls_t *p,\
									  int k)
{
	unsigned int i;
	z3_ast_array *t;
	Z3_ast t1, ret = NULL;
	noll_dform_t *df;

	if(dc->trans != NULL){
		t = z3_ast_array_new();
		for(i = 0; i < noll_vector_size(dc->trans); i++){
			df = noll_vector_at(dc->trans, i);
			switch(df->kind){
			case NOLL_DATA_EQ:
				t1 = _slid_mk_pred_data_constr_trans(z3_ctx, slid_ctx, dc, df, p, k, Z3_mk_eq);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			case NOLL_DATA_LE:
				t1 = _slid_mk_pred_data_constr_trans(z3_ctx, slid_ctx, dc, df, p, k, Z3_mk_le);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			case NOLL_DATA_GE:
				t1 = _slid_mk_pred_data_constr_trans(z3_ctx, slid_ctx, dc, df, p, k, Z3_mk_ge);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			}
		}

		if(noll_vector_empty(t))
			ret = NULL;
		else
			ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));

		z3_ast_array_delete(t);
	}


	return ret;
}

Z3_ast _slid_mk_pred_data_constr_trans(Z3_context z3_ctx, slid_context slid_ctx,\
									   slid_data_constr *dc, noll_dform_t *df, noll_ls_t *p, int k,\
									   Z3_ast (*op_func)(Z3_context, Z3_ast, Z3_ast))
{
	noll_dterm_t *t1, *t2, *t3, *t4;
	noll_pred_t *pred;
	z3_ast_array *t;
	Z3_ast a, b, e, ret;
	Z3_ast c[2];
	Z3_ast d[2];
	int n, hole;
	unsigned int i;
	noll_dform_t *df1;

	t1 = noll_vector_at(df->p.targs, 0);
	t2 = noll_vector_at(df->p.targs, 1);

	pred = noll_vector_at(preds_array, p->pid);

	hole = slid_get_hole(pred);

	a = slid_ctx_var_at(noll_vector_at(p->args, t1->p.sid-1));
	switch(t2->kind){
	case NOLL_DATA_VAR:
		n = noll_vector_at(p->args, hole + t1->p.sid -1);
		b = slid_ctx_var_at(n);
		return op_func(z3_ctx, a, b);
	case NOLL_DATA_PLUS:
		t = z3_ast_array_new();
		t3 = noll_vector_at(t2->args, 0);
		t4 = noll_vector_at(t2->args, 1);
		c[0] = noll_vector_at(slid_ctx->k, k);
		c[1] = Z3_mk_int(z3_ctx, t4->p.value, slid_ctx->int_sort);
		d[0] = Z3_mk_mul(z3_ctx, 2, c);
		d[1] = slid_ctx_var_at(noll_vector_at(p->args, hole + t1->p.sid -1));
		b = Z3_mk_add(z3_ctx, 2, d);
		z3_ast_array_push(t, op_func(z3_ctx, a, b));

		/*if(((t4->p.value < 0)\
		  && ((df->kind == NOLL_DATA_LE) && (dc->cl != NULL)))\
		  || ((t4->p.value >0)\
		  && (df->kind == NOLL_DATA_GE) && (dc->cg != NULL))){
		  e = slid_mk_assist_constr(z3_ctx, slid_ctx, dc, df, p, k);
		  if(e != NULL) z3_ast_array_push(t, e);
		  }*/
		if(((t4->p.value < 0) && ((df->kind == NOLL_DATA_LE) && (dc->cl != NULL)))){
			e = slid_mk_assist_constr(z3_ctx, slid_ctx, noll_vector_at(dc->cl->p.targs, 1), df, p, k);
			if(e != NULL) z3_ast_array_push(t, e);
		}

		if (((t4->p.value >0) && (df->kind == NOLL_DATA_GE) && (dc->cg != NULL))) {
			e = slid_mk_assist_constr(z3_ctx, slid_ctx, noll_vector_at(dc->cg->p.targs, 1), df, p, k);
			if(e != NULL) z3_ast_array_push(t, e);
		}

		if((dc->stc != NULL) && (!noll_vector_empty(dc->stc))){
			for(i = 0; i < noll_vector_size(dc->stc); i++){
				df1 = noll_vector_at(dc->stc, i);
				switch(df1->kind){
				case NOLL_DATA_LE:
					if (((t4->p.value < 0) && ((df->kind == NOLL_DATA_LE) ))) {
						e = slid_mk_assist_constr(z3_ctx, slid_ctx, noll_vector_at(df1->p.targs, 1), df, p, k);
						if(e != NULL) z3_ast_array_push(t, e);
					}
					break;
				case NOLL_DATA_GE:
					if (((t4->p.value >0)\
						 && (df->kind == NOLL_DATA_GE))) {
						e = slid_mk_assist_constr(z3_ctx, slid_ctx, noll_vector_at(df1->p.targs, 1), df, p, k);
						if(e != NULL) z3_ast_array_push(t, e);
					}
					break;
				}
			}
		}
		ret =  Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));

		z3_ast_array_delete(t);
		return ret;
	}

	return NULL;
}

Z3_ast _slid_mk_assist_constr(Z3_context z3_ctx, slid_context slid_ctx,\
							  noll_dterm_t *t, noll_ls_t *p,\
							  Z3_ast a, Z3_ast c0,\
							  Z3_ast (*op_func)(Z3_context, Z3_ast, Z3_ast))
{
	Z3_ast b;
	Z3_ast c[2];
	Z3_ast d[2];
	noll_dterm_t *t1, *t2;

	c[0] = c0;
	switch(t->kind){
	case NOLL_DATA_INT:
		c[1] = Z3_mk_int(z3_ctx, t->p.value, slid_ctx->int_sort);
		break;
	case NOLL_DATA_VAR:
		c[1] = slid_ctx_var_at(noll_vector_at(p->args, t->p.sid-1));
		break;
	case NOLL_DATA_PLUS:
		t1 = noll_vector_at(t->args, 0);
		t2 = noll_vector_at(t->args, 1);
		d[0] = slid_ctx_var_at(noll_vector_at(p->args, t1->p.sid-1));
		d[1] = Z3_mk_int(z3_ctx, t2->p.value, slid_ctx->int_sort);
		c[1] = Z3_mk_add(z3_ctx, 2, d);
		break;
	}
	b = Z3_mk_add(z3_ctx, 2, c);
	return op_func(z3_ctx, a, b);
}

Z3_ast slid_mk_assist_constr(Z3_context z3_ctx, slid_context slid_ctx,\
							 noll_dterm_t *dt, noll_dform_t *df, noll_ls_t *p, int k)
{
	noll_dterm_t *t1, *t2, *t3, *t4;
	Z3_ast a, b;
	Z3_ast c[2];
	Z3_ast d[2];

	t1 = noll_vector_at(df->p.targs, 0);
	t2 = noll_vector_at(df->p.targs, 1);
	t3 = noll_vector_at(t2->args, 0);
	t4 = noll_vector_at(t2->args, 1);
	a = slid_ctx_var_at(noll_vector_at(p->args, t1->p.sid-1));

	c[0] = noll_vector_at(slid_ctx->k, k);
	c[1] = Z3_mk_int(z3_ctx, 1, slid_ctx->int_sort);
	d[0] = Z3_mk_sub(z3_ctx, 2, c);
	d[1] = Z3_mk_int(z3_ctx, t4->p.value, slid_ctx->int_sort);
	c[0] = Z3_mk_mul(z3_ctx, 2, d);

	switch(df->kind){
	case NOLL_DATA_LE:
		return _slid_mk_assist_constr(z3_ctx, slid_ctx, dt, p, a, c[0], Z3_mk_le);
	case NOLL_DATA_GE:
		return _slid_mk_assist_constr(z3_ctx, slid_ctx, dt, p, a, c[0], Z3_mk_ge);
	}

	return NULL;
}

Z3_ast slid_mk_sep_constr(Z3_context z3_ctx, slid_context slid_ctx)
{
	unsigned int i, j, k, l;
	unsigned int n1, n2, n3;
	slid_in_alloc_loc_array *t1, *t2;
	slid_in_alloc_loc *t3, *t4;
	unsigned int s1, s2;

	Z3_ast a[2];
	Z3_ast b, c, ret = NULL;
	z3_ast_array *t;


	if((slid_ctx->space == NULL) || (noll_vector_empty(slid_ctx->space))) return NULL;

	n1 = noll_vector_size(slid_ctx->m);
	t = z3_ast_array_new();
	for(i = 0; i < n1; i++){
		t1 = noll_vector_at(slid_ctx->m, i);
		n2 = noll_vector_size(t1);
		for(j = 0; j < n2; j++){
			for(k = 0; k < n1; k++){
				t2 = noll_vector_at(slid_ctx->m, k);
				n3 = noll_vector_size(t2);
				for(l = 0; l < n3; l++){
					if(i != k){
						t3 = slid_in_alloc_loc_locate(slid_ctx->m, i, j);
						t4 = slid_in_alloc_loc_locate(slid_ctx->m, k, l);
						s1 = t3->sid;
						s2 = t4->sid;
						a[0] = Z3_mk_eq(z3_ctx, slid_ctx_var_at(s1), slid_ctx_var_at(s2));
						a[1] = Z3_mk_eq(z3_ctx, t3->bvar, Z3_mk_true(z3_ctx));
						b = Z3_mk_and(z3_ctx, 2, a);
						c = Z3_mk_eq(z3_ctx, t4->bvar, Z3_mk_false(z3_ctx));
						z3_ast_array_push(t, Z3_mk_implies(z3_ctx, b, c));
					}
				}
			}
		}
	}
	if(!noll_vector_empty(t))
		ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}
