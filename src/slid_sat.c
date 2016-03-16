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


extern noll_pred_array *preds_array;

int slid_sat_check(noll_form_t *form)
{
	int ret;
	Z3_solver s;
	Z3_config cfg;
	Z3_context z3_ctx;
	slid_context slid_ctx;

	cfg = Z3_mk_config();
	z3_ctx = Z3_mk_context(cfg);
	Z3_del_config(cfg);

	slid_ctx = slid_mk_context(z3_ctx, form);

	if((slid_ctx->var == NULL) || noll_vector_empty(slid_ctx->var))
		return SLID_SAT;

	s = Z3_mk_solver(z3_ctx);
	Z3_solver_inc_ref(z3_ctx, s);

	Z3_solver_assert(z3_ctx, s, slid_mk_abstr(z3_ctx, slid_ctx, form));
	
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
	}
	
	Z3_del_context(z3_ctx);
	slid_del_context(slid_ctx);
	
	return ret;
}

void slid_mk_space_array(noll_space_array **space_arr, noll_space_t *space)
{	
	assert(space != NULL);


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
			for(int i=0; i<noll_vector_size(space->m.sep); i++)
				slid_mk_space_array(space_arr, noll_vector_at(space->m.sep, i));
			break;
	}
}

void slid_del_context(slid_context slid_ctx)
{
	for(int i=0; i<slid_ctx->row; i++)
		free(slid_ctx->m[i]);
	
	z3_ast_array_delete(slid_ctx->var);
	noll_space_array_delete(slid_ctx->space);	
}


slid_context slid_mk_context(Z3_context z3_ctx, noll_form_t *form)
{
	int i, j;
	char *str;
	noll_var_t *v;
	Z3_sort int_sort, bool_sort;
	Z3_ast tmp;

	int_sort = Z3_mk_int_sort(z3_ctx);
	bool_sort = Z3_mk_bool_sort(z3_ctx);

	slid_context ret = (slid_context)malloc(sizeof(_slid_context));
	assert(ret != NULL);

	ret->int_sort = int_sort;
	ret->bool_sort = bool_sort;

	if((form->lvars == NULL) || (noll_vector_empty(form->lvars))){
		ret->var = NULL;
		ret->row = 0;
	}else{
		ret->var = z3_ast_array_new();
		v = noll_vector_at(form->lvars, 0);
		tmp = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, v->vname), int_sort);
		z3_ast_array_push(ret->var, tmp);

		ret->space = NULL;
		if(form->space != NULL)
			slid_mk_space_array(&ret->space, form->space);
		ret->m = (Z3_ast **)malloc((noll_vector_size(form->lvars)-1) * sizeof(Z3_ast *));
		assert(ret->m != NULL);
		ret->k = z3_ast_array_new();

		for(i = 1; i < noll_vector_size(form->lvars); i++){
			v = noll_vector_at(form->lvars, i);
			tmp = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, v->vname), int_sort);
			z3_ast_array_push(ret->var, tmp);

			if((ret->space == NULL) || (noll_vector_empty(ret->space))) continue;

			ret->m[i-1] = (Z3_ast *)malloc(noll_vector_size(ret->space) * sizeof(Z3_ast));
			assert(ret->m[i-1] != NULL);

			for(j = 0; j < noll_vector_size(ret->space); j++){
				str = (char *)malloc(sizeof(char) * strlen("__slid_m_??_??"));
				assert(str != NULL);
				sprintf(str, "__slid_m_%d_%d", i, j);
				ret->m[i-1][j] = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, str), bool_sort);
			}
		}
		for(i = 0; i < noll_vector_size(ret->space); i++){
			str = (char *)malloc(sizeof(char) * strlen("__slid_k_??"));
			assert(str != NULL);
			sprintf(str, "__slid_k_%d", i-1);
			z3_ast_array_push(ret->k, Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, str), int_sort));
			
		}
		ret->column = noll_vector_size(ret->space);
		ret->row = noll_vector_size(ret->var)-1;
	}

	return ret;
}


Z3_ast slid_mk_abstr(Z3_context z3_ctx, slid_context slid_ctx, noll_form_t *f)
{
	assert(f != NULL);

	z3_ast_array *t;
	Z3_ast s;
	
	t = z3_ast_array_new();

	if(f->pure != NULL){
		s = slid_mk_pure_abstr(z3_ctx, slid_ctx, f->pure);
		if(s != NULL) z3_ast_array_push(t, s);
	}

	if((slid_ctx->space != NULL) && (!noll_vector_empty(slid_ctx->space))){
		s = slid_mk_space_abstr(z3_ctx, slid_ctx);
		if(s != NULL) z3_ast_array_push(t, s);
	}

	return Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
}


Z3_ast slid_mk_pure_abstr(Z3_context z3_ctx, slid_context slid_ctx, noll_pure_t *pure)
{
	assert(pure != NULL);

	int i, j, k;
	Z3_ast t1, t2, t3, ret;
	noll_dform_t *t4;
	z3_ast_array *t;

	t = z3_ast_array_new();
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

	ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

Z3_ast slid_mk_pure_data_constr(Z3_context z3_ctx, slid_context slid_ctx, noll_dform_t *data)
{
	assert(data != NULL);

	Z3_ast (*fun_arr1[5])(Z3_context, Z3_ast, Z3_ast)\
			= {Z3_mk_eq, Z3_mk_lt, Z3_mk_gt, Z3_mk_le, Z3_mk_ge};
	Z3_ast (*fun_arr2[3])(Z3_context, unsigned int, Z3_ast const[])\
			= {Z3_mk_distinct, Z3_mk_add, Z3_mk_sub};

	if(data->kind < 5)
		return _slid_mk_pure_data_constr1(z3_ctx, slid_ctx, data->p.targs, fun_arr1[data->kind]);
	if(data->kind < 8)
		return _slid_mk_pure_data_constr2(z3_ctx, slid_ctx, data->p.targs, fun_arr2[data->kind-5]);
	
	if(data->kind == NOLL_DATA_IMPLIES)
		return slid_mk_implies(z3_ctx, slid_ctx, data->p.bargs);
	else
		exit(1);
}

Z3_ast _slid_mk_pure_data_constr1(Z3_context z3_ctx, slid_context slid_ctx,\
				noll_dterm_array * terms, Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast))
{
	assert(terms != NULL);
	assert(noll_vector_size(terms) > 1);
	
	Z3_ast a1, a2, ret;
	z3_ast_array *t;

	t = z3_ast_array_new();
	for(int i=0; i<noll_vector_size(terms)-1; i++){
		a1 = slid_mk_term(z3_ctx, slid_ctx, noll_vector_at(terms, i));
		a2 = slid_mk_term(z3_ctx, slid_ctx, noll_vector_at(terms, i+1));
		z3_ast_array_push(t, f(z3_ctx, a1, a2)); 
	}
	ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}


Z3_ast _slid_mk_pure_data_constr2(Z3_context z3_ctx, slid_context slid_ctx,\
			noll_dterm_array *terms, Z3_ast (*f)(Z3_context, unsigned int, Z3_ast const[]))
{
	assert(terms != NULL);
	assert(noll_vector_size(terms) > 1);
	
	Z3_ast ret;
	z3_ast_array *t;

	t = z3_ast_array_new();
	for(int i=0; i<noll_vector_size(terms); i++)
		z3_ast_array_push(t, slid_mk_term(z3_ctx, slid_ctx, noll_vector_at(terms, i)));	

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

	Z3_ast ret;

	ret = slid_mk_pure_data_constr(z3_ctx, slid_ctx, noll_vector_at(forms, noll_vector_size(forms)-1));
	for(int i = noll_vector_size(forms)-2; i >=0; i--)
		ret = Z3_mk_implies(z3_ctx, slid_mk_pure_data_constr(z3_ctx, slid_ctx, noll_vector_at(forms, i)), ret);
	
	return ret;	
}

Z3_ast slid_mk_term(Z3_context z3_ctx, slid_context slid_ctx, noll_dterm_t *term)
{
	assert(term != NULL);

	Z3_ast (*fun_arr1[5])(Z3_context, Z3_ast, Z3_ast)\
			= {Z3_mk_eq, Z3_mk_lt, Z3_mk_gt, Z3_mk_le, Z3_mk_ge};
	Z3_ast (*fun_arr2[3])(Z3_context, unsigned int, Z3_ast const[])\
			= {Z3_mk_distinct, Z3_mk_add, Z3_mk_sub};

	if(term->kind < 5)
		return _slid_mk_pure_data_constr1(z3_ctx, slid_ctx, term->args, fun_arr1[term->kind]);
	if(term->kind < 8)
		return _slid_mk_pure_data_constr2(z3_ctx, slid_ctx, term->args, fun_arr2[term->kind-5]);
	switch(term->kind){
	case NOLL_DATA_INT:
		return Z3_mk_int(z3_ctx, term->p.value, slid_ctx->int_sort);
	case NOLL_DATA_VAR:
		return noll_vector_at(slid_ctx->var,term->p.sid);
	case NOLL_DATA_ITE:
		return slid_mk_ite(z3_ctx, slid_ctx, term);
	default:
		printf("Unsurport data constraints!\n");
		exit(0);
	}
}


Z3_ast slid_mk_space_abstr(Z3_context z3_ctx, slid_context slid_ctx)
{
	int i;
	z3_ast_array *t;
	noll_space_t *t1;
	Z3_ast t2, t3, ret;

	t = z3_ast_array_new();
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

	ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

Z3_ast slid_mk_pto(Z3_context z3_ctx, slid_context slid_ctx, noll_pto_t *pto, int k)
{
	assert(pto != NULL);

	Z3_ast ret, t1, t2;

	t1 = slid_ctx->m[pto->sid-1][k];
	t2 = Z3_mk_true(z3_ctx);
	ret = Z3_mk_eq(z3_ctx, t1, t2);

	return ret;
}

Z3_ast slid_mk_pred(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int k)
{
	assert(pred != NULL);

	z3_ast_array *t, *t1;
	Z3_ast t2, t3, ret;

	t = z3_ast_array_new();
	t1 = z3_ast_array_new();

	t2 = slid_mk_unfold(z3_ctx, slid_ctx, pred, k);
	if(t1 != NULL) z3_ast_array_push(t, t2);

	t2 = slid_mk_fir_unfold(z3_ctx, slid_ctx, pred, k);
	if(t1 != NULL) z3_ast_array_push(t1, t2);

	t2 = slid_mk_sec_unfold(z3_ctx, slid_ctx, pred, k);
	if(t1 != NULL) z3_ast_array_push(t1, t2);

	t2 = Z3_mk_or(z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
	z3_ast_array_clear(t1);
	if(t2 != NULL) z3_ast_array_push(t1, t2);
	t2 = slid_ctx->m[noll_vector_at(pred->args, 0)-1][k];
	t3 = Z3_mk_true(z3_ctx);
	z3_ast_array_push(t1, Z3_mk_eq(z3_ctx, t2, t3));
	t2 = slid_mk_closures(z3_ctx, slid_ctx, pred, k);
	if(t2 != NULL) z3_ast_array_push(t1, t2);
	t3 = Z3_mk_and(z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
	if(t3 != NULL) z3_ast_array_push(t, t3);

	ret = Z3_mk_or(z3_ctx, noll_vector_size(t), noll_vector_array(t));

	z3_ast_array_delete(t);
	z3_ast_array_delete(t1);

	return ret;
}


Z3_ast slid_mk_unfold(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int ki)
{
	int i, j, k;
	z3_ast_array * t, *t1;
	Z3_ast t2, t3, t4, t5, ret;
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
/*
int pred_has_data_constr(noll_pred_t *pred)
{
	int i;
	noll_pred_rule_t *rr;
	noll_pred_rule_array *rrs;

	rrs = pred->def->rec_rules;

	for(i=0; i<noll_vector_size(rrs); i++){
		rr = noll_vector_at(rrs, i);

		if((rr->pure->data != NULL)\
		&& (!noll_vector_empty(rr->pure->data)))
			return 1;
	}
	return 0;
}
*/
Z3_ast slid_mk_fir_unfold(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int k)
{
	assert(pred->pid >= 0);
	assert(pred->pid < noll_vector_size(preds_array));

	int n1, n2;
	noll_pred_t *ppred;
	z3_ast_array *t;
	noll_pred_rule_t *r;
	Z3_ast t1, t2, t3, ret;

	t = z3_ast_array_new();
	
	ppred = noll_vector_at(preds_array, pred->pid);

	r = noll_vector_at(ppred->def->rec_rules, 0);
	
	if(ppred->typ->nDir >= 2){
		t1 = slid_ctx_var_at(noll_vector_at(pred->args, 0));
		n1 = slid_get_trans_loc(r, 1);
		n2 = slid_get_hole(ppred) + n1;
		t2 = slid_ctx_var_at(noll_vector_at(pred->args, n2));
		z3_ast_array_push(t, Z3_mk_eq(z3_ctx, t1, t2));
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
	Z3_ast t1, t2, t3, ret;

	t = z3_ast_array_new();
	
	ppred = noll_vector_at(preds_array, pred->pid);
	r = noll_vector_at(ppred->def->rec_rules, 0);
	
	if(ppred->typ->nDir >= 2){
		t1 = slid_ctx_var_at(noll_vector_at(pred->args, 0));
		n1 = slid_get_trans_loc(r, 1);
		n2 = slid_get_hole(ppred) + n1;
		t2 = slid_ctx_var_at(noll_vector_at(pred->args, n2));
		t3 = Z3_mk_eq(z3_ctx, t1, t2);
		z3_ast_array_push(t, Z3_mk_not(z3_ctx, t3));

		i = noll_vector_at(pred->args, n2);

		t1 = slid_ctx->m[i-1][k];
		t2 = Z3_mk_true(z3_ctx);
		z3_ast_array_push(t, Z3_mk_eq(z3_ctx, t1, t2));
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

	int i;

	for(i = 0; i < noll_vector_size(pred->typ->argkind); i++){
		if(noll_vector_at(pred->typ->argkind, i) == NOLL_ATYP_LPENDING)
			return i;
	}

	return -1;
}

Z3_ast slid_mk_closures(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, int k)
{
	assert(pred != NULL);

	int i, j;
	z3_ast_array *t, *t1;
	slid_data_constr_array *t2;
	slid_data_constr *t3;
	Z3_ast t4, ret;
	noll_pred_t *ppred;
	noll_pred_rule_array *rr;
	noll_pred_rule_t *r;
	noll_dform_array *dfs;
	slid_data_constr *dc;

	t = z3_ast_array_new();
	ppred = noll_vector_at(preds_array, pred->pid);
	rr = ppred->def->rec_rules;

	for(i = 0; i < noll_vector_size(rr); i++){
		t1 = z3_ast_array_new();
		t2 = slid_data_constr_array_new();
	
		r = noll_vector_at(rr, i);
		dfs = r->pure->data;

		if(!ppred->typ->isUnaryLoc){
			j = ppred->typ->nDir+1;
			for(j; j <= slid_get_hole(ppred); j++){
				t3 = slid_get_pred_data_constr(ppred, r, j);
				slid_data_constr_array_push(t2, t3);
			}
		}

		for(j = 0; j < noll_vector_size(t2); j++){
			dc = noll_vector_at(t2, i);
			t4 = slid_mk_closure(z3_ctx, slid_ctx, dc, pred, k);
			z3_ast_array_push(t1, t4); 
		}
		t4 = Z3_mk_and(z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
		z3_ast_array_push(t, t4);

		z3_ast_array_delete(t1);

		for (j = 0; j < noll_vector_size(t2); j++)
			slid_del_pred_data_constr(noll_vector_at(t2, j));
		slid_data_constr_array_delete(t2);
	}

	ret = Z3_mk_or(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

slid_data_constr *slid_get_pred_data_constr(noll_pred_t *p, noll_pred_rule_t *r, int sid)
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
	int i;
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
int slid_get_trans_loc(noll_pred_rule_t *r, int sid)
{
	int i;
	noll_ls_t *p;

	p = slid_get_rule_pred(r->rec);

	for(i = 0; i < noll_vector_size(p->args); i++){
		if(noll_vector_at(p->args, i) == sid)
			return i;
	}

	return -1;
}

bool slid_is_trans_para(int sid0, int sid1, noll_pred_rule_t *r)
{
	int i;
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

noll_dform_array *slid_get_pred_data_constr_ce(noll_pred_t *p, noll_pred_rule_t *r, int sid)
{
	noll_dform_array *dfs;
	noll_dform_t *df;
	noll_dform_array *t;
	int i;

	dfs = r->pure->data;
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

noll_dform_t *slid_get_pred_data_constr_clg(noll_pred_rule_t *r,int sid, noll_data_op_t op_t)
{
	noll_dform_array *dfs;
	noll_dform_t *df;
	noll_dform_t *ret = NULL;
	noll_dterm_t *t1, *t2;
	int i, c;
	int f=0;

	dfs = r->pure->data;

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

noll_dform_array *slid_get_pred_data_constr_stc(noll_pred_t *p, noll_pred_rule_t *r, int sid)
{
	noll_dform_array *t;
	noll_dform_array *dfs;
	noll_dform_t *df;
	int i;

	dfs = r->pure->data;

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
noll_dform_array *slid_get_pred_data_constr_trans(noll_pred_t *p, noll_pred_rule_t *r, int sid)
{
	noll_dform_array *dfs;
	noll_dform_t *df;
	noll_dform_array *t;
	int i;

	dfs = r->pure->data;
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
	int i;
	noll_dform_t *df;
	z3_ast_array *t;
	Z3_ast t1, ret;
	
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
}

Z3_ast slid_mk_pred_data_constr_stc(Z3_context z3_ctx, slid_context slid_ctx,\
					slid_data_constr *dc, noll_ls_t *p)
{
	int i;
	noll_dform_t *df;
	z3_ast_array *t;
	Z3_ast t1, ret;
	
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
}


Z3_ast slid_mk_pred_data_constr_trans(Z3_context z3_ctx, slid_context slid_ctx,\
					slid_data_constr *dc, noll_ls_t *p,\
					int k)
{
	int i;
	z3_ast_array *t;
	Z3_ast t1, ret;
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

		if(((t4->p.value < 0)\
		&& ((df->kind == NOLL_DATA_LE) && (dc->cl != NULL)))\
		|| ((t4->p.value >0)\
		&& (df->kind == NOLL_DATA_GE) && (dc->cg != NULL))){
			e = slid_mk_assist_constr(z3_ctx, slid_ctx, dc, df, p, k);
			if(e != NULL) z3_ast_array_push(t, e);
		}
		ret =  Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));

		z3_ast_array_delete(t);
		return ret;
	}
	
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
			     slid_data_constr *dc, noll_dform_t *df, noll_ls_t *p, int k)
{
	noll_dterm_t *t1, *t2, *t3, *t4, *t5;
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
		t5 = noll_vector_at(dc->cl->p.targs, 1);
		return _slid_mk_assist_constr(z3_ctx, slid_ctx, t5, p, c[0], a, Z3_mk_le);
	case NOLL_DATA_GE:
		t5 = noll_vector_at(dc->cg->p.targs, 1);
		return _slid_mk_assist_constr(z3_ctx, slid_ctx, t1, p, c[0], a, Z3_mk_ge);
	}
}
/*
Z3_ast _slid_mk_closure(Z3_context z3_ctx, slid_context slid_ctx, noll_ls_t *pred, \
                        int k, noll_dterm_t *term1, noll_dterm_t *term2,\
			Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast))
{
	Z3_ast a, b;
	Z3_ast c[2];
	Z3_ast d[2];
	noll_pred_t *ppred;
	noll_dterm2_t *_para1, *_para2;

	ppred = noll_vector_at(preds_array, pred->pid);
	a = noll_vector_at(slid_ctx, noll_vector_at(pred->args, term1->p.sid-1));

	switch(term2->kind){
	case NOLL_DATA_INT:
		return f(z3_ctx, a, Z3_mk_int(z3_ctx, term2->p.value, slid_ctx->int_sort));
	case NOLL_DATA_VAR:
		if(term2->p.sid <= ppred->typ->fargs){
			assert(noll_vector_at(ppred->typ->argkind, term2->p.sid-1) == NOLL_ATYP_BORDER);
			b = noll_vector_at(slid_ctx->var, noll_vector_at(pred->args, term2->p.sid-1));
		}else if(noll_vector_at(ppred->typ->argkind, slid_get_counterpart(ppred, term1->p.sid-1)) == NOLL_ATYP_LPENDING){
			b = noll_vector_at(slid_ctx->var, noll_vector_at(pred->args, slid_get_counterpart(ppred, term1->p.sid-1)));
		}else{
			exit(1);
		}
		return f(z3_ctx, a, b);
	case NOLL_DATA_PLUS:
		assert(term2->args != NULL);
		assert(noll_vector_size(term2->args) == 2);
		_para1 = noll_vector_at(term2->args, 0);
		_para2 = noll_vector_at(term2->args, 1);
		assert(_para1->kind == NOLL_DATA_VAR);
		assert(_para1->p.sid <= noll_vector_size(pred->args));
		assert(_para2->kind == NOLL_DATA_INT);
		if(_para1->p.sid <= ppred->typ->fagrs){
			assert(noll_vector_at(ppred->typ->argkind, _para1->p.sid-1) == NOLL_ATYP_BORDER);
			c[0] = noll_vector_at(slid_ctx->var, noll_vector_at(pred->args, _para1->p.sid-1));
			c[1] = Z3_mk_int(z3_ctx, _para2->p.value, slid_ctx->int_sort);
			b = Z3_mk_add(z3_ctx, 2, c);
			return f(z3_ctx, a, b);
		}else if(noll_vector_at(ppred->typ->argkind, slid_get_counterpart(ppred, term1->p.sid-1)) == NOLL_ATYP_LPENDING){
			if((kind == NOLL_DATA_LE) && (_para2->p.value < 0) && (slid_get_assist_constr(ppred, term1->p.sid, kind, &e))){
				c[0] = noll_vector_at(slid_ctx->k, k);
				c[1] = Z3_mk_int(z3_ctx, 1, slid_ctx->int_sort);
				d[0] = Z3_mk_sub(z3_ctx, 2, c);
				d[1] = Z3_mk_int(z3_ctx, _para2->p.value, slid_ctx->int_sort);
				if(e->kind == NOLL_DATA_INT)
					c[0] = Z3_mk_int(z3_ctx, e->p.value, slid_ctx->int_sort);
				else{
					b[0] = noll_vector_at(slid_ctx->var, noll_vector_at(pred->args, e->args[0]->p.sid-1));
					b[1] = Z3_mk_int(z3_ctx, e->args[1]->p.value, slid_ctx->int_sort);
					c[0] = Z3_mk_add(z3_ctx, 2, b);
				}
				c[1] = Z3_mk_mul(z3_ctx, 2, d);
				b[0] = Z3_mk_add(z3_ctx, 2, c);
				z3_ast_array_push(t, f(z3_ctx, a, b[0]));
			}
		}else{
			exit(0);
		}
		c[0] = noll_vector_at(slid_ctx->var, noll_vector_at(pred->args, slid_get_counterpart(ppred, _para1->p.sid-1)));
		d[0] = noll_vector_at(slid_ctx->k, k);
		d[1] = Z3_mk_int(z3_ctx, _para2->p.value, slid_ctx->int_sort);
		c[1] = Z3_mk_mul(z3_ctx, 2, d);
		b = Z3_mk_add(z3_ctx, 2, c);
		z3_ast_array_push(z3_ctx, f(z3_ctx, a, b));
		return Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	}
}

	


int slid_get_counterpart(noll_pred_t *pred, int src)
{
	assert(pred->typ->isUnaryLoc == false);
	int ret;

	ret = (slid_get_src_para_num(pred) + src);

	return ret;
}

int slid_get_src_para_num(noll_pred_t *pred)
{
	assert(pred->typ->isUnaryLoc == false);

	int i, s;

	s = (pred->typ->isTwoDir) ? 2:1;
	
	for(i = s; i < noll_vector_size(pred->typ->argkind); i++){
		if(noll_vector_at(pred->typ->argkind, i) == NOLL_ATYP_LPENDING)
			return i;
	}
	exit(1);
}*/

Z3_ast slid_mk_sep_constr(Z3_context z3_ctx, slid_context slid_ctx)
{
	int i, j, k, l, m, n, num;
	Z3_ast a[2];
	Z3_ast b, c, ret;
	z3_ast_array *t;

	num = slid_ctx->row * slid_ctx->column;
	t = z3_ast_array_new();
	for(i = 0; i < num; i++){
		for(j = 0; j < num; j++){
			if(i != j){
				k = i/slid_ctx->column;
				l = i - k*slid_ctx->column;
				m = j/slid_ctx->column;
				n = j - m*slid_ctx->column;
				a[0] = Z3_mk_eq(z3_ctx, slid_ctx_var_at(k+1), slid_ctx_var_at(m+1));
				a[1] = slid_ctx->m[k][l];
				b = Z3_mk_and(z3_ctx, 2, a);
				c = Z3_mk_not(z3_ctx, slid_ctx->m[m][n]);
				z3_ast_array_push(t, Z3_mk_implies(z3_ctx, b, c));
			}
		}
	}
	ret = Z3_mk_and(z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

