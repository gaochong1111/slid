#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>
#include<memory.h>
#include<setjmp.h>

#include<assert.h>

#include "noll_vector.h"
#include "noll_preds.h"



void exitf(const char* message) 
{
  fprintf(stderr,"BUG: %s.\n", message);
  exit(1);
}

/**
   \brief exit if unreachable code was reached.
*/
void unreachable() 
{
    exitf("unreachable code was reached");
}

/**
   \brief Simpler error handler.
 */
void error_handler(Z3_context c, Z3_error_code e) 
{
    printf("Error code: %d\n", e);
    exitf("incorrect use of Z3");
}

static jmp_buf g_catch_buffer;
/**
   \brief Low tech exceptions. 
   
   In high-level programming languages, an error handler can throw an exception.
*/
void throw_z3_error(Z3_context c, Z3_error_code e) 
{
    longjmp(g_catch_buffer, e);
}

/**
   \brief Create a logical context.  

   Enable model construction. Other configuration parameters can be passed in the cfg variable.

   Also enable tracing to stderr and register custom error handler.
*/
Z3_context mk_context_custom(Z3_config cfg, Z3_error_handler err) 
{
    Z3_context ctx;
    
    Z3_set_param_value(cfg, "model", "true");
    ctx = Z3_mk_context(cfg);
    Z3_set_error_handler(ctx, err);
    
    return ctx;
}

Z3_solver mk_solver(Z3_context ctx) 
{
  Z3_solver s = Z3_mk_solver(ctx);
  Z3_solver_inc_ref(ctx, s);
  return s;
}

void del_solver(Z3_context ctx, Z3_solver s)
{
  Z3_solver_dec_ref(ctx, s);
}

/**
   \brief Create a logical context.

   Enable model construction only.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_context() 
{
    Z3_config  cfg;
    Z3_context ctx;
    cfg = Z3_mk_config();
    ctx = mk_context_custom(cfg, error_handler);
    Z3_del_config(cfg);
    return ctx;
}

/**
   \brief Create a logical context.

   Enable fine-grained proof construction.
   Enable model construction.

   Also enable tracing to stderr and register standard error handler.
*/
Z3_context mk_proof_context() {
    Z3_config cfg = Z3_mk_config();
    Z3_context ctx;
    Z3_set_param_value(cfg, "proof", "true");
    ctx = mk_context_custom(cfg, throw_z3_error);
    Z3_del_config(cfg);
    return ctx;
}

/**
   \brief Create a variable using the given name and type.
*/
Z3_ast mk_var(Z3_context ctx, const char * name, Z3_sort ty) 
{
    Z3_symbol   s  = Z3_mk_string_symbol(ctx, name);
    return Z3_mk_const(ctx, s, ty);
}

/**
   \brief Create a boolean variable using the given name.
*/
Z3_ast mk_bool_var(Z3_context ctx, const char * name) 
{
    Z3_sort ty = Z3_mk_bool_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create an integer variable using the given name.
*/
Z3_ast mk_int_var(Z3_context ctx, const char * name) 
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create a Z3 integer node using a C int. 
*/
Z3_ast mk_int(Z3_context ctx, int v) 
{
    Z3_sort ty = Z3_mk_int_sort(ctx);
    return Z3_mk_int(ctx, v, ty);
}

/**
   \brief Create a real variable using the given name.
*/
Z3_ast mk_real_var(Z3_context ctx, const char * name) 
{
    Z3_sort ty = Z3_mk_real_sort(ctx);
    return mk_var(ctx, name, ty);
}

/**
   \brief Create the unary function application: <tt>(f x)</tt>.
*/
Z3_ast mk_unary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x) 
{
    Z3_ast args[1] = {x};
    return Z3_mk_app(ctx, f, 1, args);
}

/**
   \brief Create the binary function application: <tt>(f x y)</tt>.
*/
Z3_ast mk_binary_app(Z3_context ctx, Z3_func_decl f, Z3_ast x, Z3_ast y) 
{
    Z3_ast args[2] = {x, y};
    return Z3_mk_app(ctx, f, 2, args);
}

/**
   \brief Check whether the logical context is satisfiable, and compare the result with the expected result.
   If the context is satisfiable, then display the model.
*/
void check(Z3_context ctx, Z3_solver s, Z3_lbool expected_result)
{
    Z3_model m      = 0;
    Z3_lbool result = Z3_solver_check(ctx, s);
    switch (result) {
    case Z3_L_FALSE:
        printf("unsat\n");
        break;
    case Z3_L_UNDEF:
        printf("unknown\n");        
	m = Z3_solver_get_model(ctx, s);
	if (m) Z3_model_inc_ref(ctx, m);
        printf("potential model:\n%s\n", Z3_model_to_string(ctx, m));
        break;
    case Z3_L_TRUE:
	m = Z3_solver_get_model(ctx, s);
	if (m) Z3_model_inc_ref(ctx, m);
        printf("sat\n%s\n", Z3_model_to_string(ctx, m));
        break;
    }
    if (result != expected_result) {
        exitf("unexpected result");
    }
    if (m) Z3_model_dec_ref(ctx, m);
}

/**
   \brief Prove that the constraints already asserted into the logical
   context implies the given formula.  The result of the proof is
   displayed.
   
   Z3 is a satisfiability checker. So, one can prove \c f by showing
   that <tt>(not f)</tt> is unsatisfiable.

   The context \c ctx is not modified by this function.
*/
void prove(Z3_context ctx, Z3_solver s, Z3_ast f, Z3_bool is_valid)
{
    Z3_model m = 0;
    Z3_ast   not_f;

    /* save the current state of the context */
    Z3_solver_push(ctx, s);

    not_f = Z3_mk_not(ctx, f);
    Z3_solver_assert(ctx, s, not_f);
        
    switch (Z3_solver_check(ctx, s)) {
    case Z3_L_FALSE:
        /* proved */
        printf("valid\n");
        if (!is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_UNDEF:
        /* Z3 failed to prove/disprove f. */
        printf("unknown\n");
        m = Z3_solver_get_model(ctx, s);
        if (m != 0) {
	  Z3_model_inc_ref(ctx, m);
            /* m should be viewed as a potential counterexample. */
  	    printf("potential counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    case Z3_L_TRUE:
        /* disproved */
        printf("invalid\n");
        m = Z3_solver_get_model(ctx, s);
        if (m) {
	  Z3_model_inc_ref(ctx, m);
            /* the model returned by Z3 is a counterexample */
            printf("counterexample:\n%s\n", Z3_model_to_string(ctx, m));
        }
        if (is_valid) {
            exitf("unexpected result");
        }
        break;
    }
    if (m) Z3_model_dec_ref(ctx, m);

    /* restore scope */
    Z3_solver_pop(ctx, s, 1);
}

/**
*
*
*
*
*/








#define INITSIZE 5

Z3_ast *lvars;
Z3_ast *svars;
Z3_ast **alloc_m;
Z3_ast *space_k;

noll_space_array spatial_forms;

NOLL_VECTOR_DECLARE(noll_space_array, noll_space_t *);

typedef struct ast_node{
	Z3_ast *data;
	int size;
	int capacity; 
}ast_array;

void init_ast_array(ast_array *aa)
{
	aa->data = NULL;
	aa->size = 0;
	aa->capacity = 0;
}

void push_ast_array(ast_array *aa, Z3_ast a)
{
	if(aa->data == NULL){
		aa->data = (Z3_ast *)malloc(INITSIZE * sizeof(Z3_ast));
		assert(aa->data != NULL);
		aa->capacity = INITSIZE;
	}

	if(aa->size == aa->capacity){
		Z3_ast *t = (Z3_ast *)malloc(aa->capacity * 2 * sizeof(Z3_ast));
		assert(t != NULL);
		for(i=0; i<aa->size; i++)
			t[i] = aa->data[i];
		free(aa->data);
		aa->data = t;
		aa->capacity *= 2;
	}

	aa->data[aa->size++] = a;
}

/*Z3_ast get_sl_form_abstr_s(Z3_context ctx, noll_space_t * sform)
{
	assert(sform != NULL);

	int i;
	ast_array t;

	index++;

	switch(sform->kind){
		case NOLL_SPACE_PTO:
			return Z3_mk_eq(ctx, alloc[sform->m.pto.sid][index], Z3_mk_true(ctx)); 
		case NOLL_SPACE_LS:
			return get_sl_form_abstr_s_pred(ctx, &(sform->m.ls));
		case NOLL_SPACE_SSEP:
			ast_array t;
			init_ast_array(&t);
			assert(sform->m.sep != NULL);
			assert(sform->m.sep->size_ > 0);
			for(i=0; i<sform->m.sep->size; i++)
				push_ast_array(&t, get_sl_form_abstr_s(ctx, sform->m.sep->data_[i]));
			return Z3_mk_and(ctx, t.size, t.data);
		default:
			exit(0);
	}
}*/

Z3_ast get_sl_form_abstr_s(Z3_context ctx, noll_space_array *spatial_forms)
{
	assert(spatial_forms != NULL);
	assert(spatial_forms->size_ > 0);

	int i;
	ast_array t;
	
	init_ast_array(&t);
	for(i=0; i<spatial_forms->size_; i++){
		switch(spatial_forms->data_[i]->kind){
			case NOLL_SPACE_PTO:
				push_ast_array(&t, Z3_mk_eq(ctx, alloc_m[spatial_forms->data_[i]->m.pto.sid][i], Z3_mk_true(ctx)));
				break;
			case NOLL_SPACE_LS:
				push_ast_array(&t, get_sl_form_abstr_s_pred(ctx, &(spatial_forms->data_[i]->m.ls), i));
				break;
			default:
				exit(0);
		}
	}

	return Z3_mk_and(ctx, t.size, t.data);
		
}

Z3_ast get_base_rules(Z3_context ctx, noll_rule_t *br, noll_ls_t * ls)
{
	assert (br != NULL);

	int i, j;
	ast_array t;

	br = preds_array->data_[ls->pid]->def->

	init_ast_array(&t);
	if(br->pure->m != NULL){
		for(i=0; i<br->pure->size-1; i++){
			for(j=1; j<br->pure->size-i; j++){
				if(br->pure->m[i][j] == NOLL_PURE_EQ)
					push_ast_array(&t, Z3_mk_eq(ctx, lvars[ls->args[i]][ls->args[j+i]]));
				if(form->t->m[i][j] == NOLL_PURE_NEQ)
					push_ast_array(&t, Z3_mk_not(ctx, Z3_mk_eq(ctx, lvars[ls->args[i]][ls->args[j+i]])));
			}
		}
	}

	return Z3_mk_and(ctx, t.size, t.data);
}

Z3_ast get_ast_closure(Z3_constext ctx, noll_data_op_t kind, noll_ls_t *ls, noll_dterm_t *para1, noll_dterm_t *para2, int index_k)
{
	switch(kind){
		case NOLL_DATA_EQ:
			if(para2->kind == NOLL_DATA_INT)
				return Z3_mk_eq(ctx, lvars[ls->args->data_[para1->p.sid-1]], Z3_mk_int(ctx, para2->p.value));
			else
				return Z3_mk_eq(ctx, lvars[ls->args->data_[para1->p.sid-1]], lvars[ls->args->data_[para2->p.sid-1]]);
		case NOLL_DATA_LE:

		case NOLL_DATA_GE:
	}
}

Z3_ast get_presburger(Z3_context ctx, noll_ls_t *ls, int index_k, int index_dform)
{
	assert((index_dform >= 0) && (index_dform < preds_array->data_[ls->pid]->def->rec_rules->data_[0]->pure->size_));
	assert((ls->pid >= 0) && (ls->pid < preds_array->size_));
	assert(ls != NULL);

	int constant_c;
	noll_pred_t *pred;
	noll_dform_t *data_constraint;
	noll_dterm_t *first_para;
	noll_dterm_t *second_para;

	pred = preds_array->data_[ls->pid];
	data_constraint = pred->def->rec-rules->data_[0]->pure->data->data_[index_dform];

	assert((data_constraint->kind == NOLL_DATA_EQ) || (data_constraint->kind == NOLL_DATA_LE) || (data_constraint->kind == NOLL_DATA_GE));

	first_para = data_constraint->p.targs->data_[0];
	second_para = data_constraint->p.targs->data_[1];
	if(second_para->kind == NOLL_DATA_INT){
		return get_ast_closure(ctx, data_constraint->kind, ls, first_para, second_para, index_k);
	}else if(second_para->kind == NOLL_DATA_VAR){
		return get_ast_closure(ctx, data_constraint->kind, ls, first_para, second_para, index_k);
	}else{
		constant_c = second_para->args->data_[1]->p.value;
		return get_ast_closure(ctx, data_constraint->kind, ls, first_para->p.sid, constant_c, index_k);
	}

}

Z3_ast get_presburgers(Z3_context ctx, noll_ls_t *ls, int index_k)
{
	assert((ls->pid >= 0) && (ls->pid < preds_array->size_));
	assert(ls != NULL);

	int i;
	ast_array t;
	noll_dform_array *delta;

	delta = preds_array->data_[pid]->def->rec_rules->data_[0]->pure->data;

	init_ast_array(&t);
	for(i=0; i<delta->size_; i++)
		push_ast_array(&t, get_presburger(ctx, ls, index_k, i));
	
	return Z3_mk_and(ctx, t.size, t.data);
}

Z3_ast get_unfold1(Z3_context ctx, noll_ls_t *ls, int index_k)
{
	assert((ls->pid >= 0) && (ls->pid < preds_array->size_));
	assert(ls != NULL);

	ast_array t;
	init_ast_array(&t);
	
	if(!preds_array->data_[ls->pid]->typ->isUnaryLoc)
//
	push_ast_array(&t, Z3_mk_eq(ctx, space_k[index_k], Z3_mk_int(ctx, 1)));
	push_ast_array(&t, get_presburger(ctx, ls, index_k));

	return Z3_mk_and(ctx, t.size, t.data);

}

Z3_ast get_unfold_form(Z3_context ctx, noll_ls_t *ls, int f, int index_k)
{
	assert((ls->pid >=0) && (ls->pid < preds_array->size_));

	switch(f){
		case 0:
			int i;
			ast_array t;
			init_ast_array(&t);
			for(i=0; i<preds_array->data_[pid]->def->base_rules->size_; i++)
				push_ast_array(&t, get_base_rules(ctx, preds_array->data_[ls->pid]->def->base_rules->data_[i], ls));
			return Z3_mk_and(ctx, t.size, t.data);	
		case 1:
			return get_unfold1(ctx, ls, index_k);
		case 2:
			return get_unfold2(ctx, pid, ls, index_k);
	}	
}

Z3_ast get_sl_form_abstr_s_pred(Z3_context ctx, noll_ls_t *pred, int index_k)
{
	assert(pred != NULL);

	int i;
	ast_array t;
		
	init_ast_array(&t);
	for(i=0; i<3; i++)
		push_ast_array(&t, get_unfold_form(ctx, pred, i, index_k));

	return Z3_mk_or(ctx, t.size, t.data);
}


/*
int get_spatial_form_size(noll_space_t * space)
{
	if(space == NULL) return 0;

	int i;
	int sum = 0;

	switch(space->kind){
		case NOLL_SPACE_PTO:
			return 1;
		case NOLL_SPACE_LS:
			return 1;
		case NOLL_SPACE_SSEP:
			for(i=0; i<space->m->sep->size_; i++)
				sum += get_spatial_form_size(space->m->sep->data_[i]);
			return sum;
		default:
			exit(0);
	}
}
*/

void get_space_array(noll_space_t *space)
{
	assert(space != NULL);
	assert(spatial_forms != NULL);

	switch(space->kind){
		case NOLL_SPACE_PTO:
			noll_space_array_push(spatial_forms, space);
			break;
		case NOLL_SPACE_LS:
			noll_space_array_push(spatial_forms, space);
			break;
		case NOLL_SPACE_SSEP:
			for(i=0; i<space->m.sep->size_; i++)
				get_space_array(spatial_forms, space->m.sep->data_[i]);
			break;
		default:
			exit(0);
	}
}
Z3_ast get_sl_form_abstr(Z3_context ctx, noll_form_t *form)
{
	assert(form != NULL);
	assert((form->pure != NULL) || (form->space != NULL));

	char name[30];
	ast_array abstr;
	Z3_sort int_sort;
	Z3_sort bool_sort;

	int_sort = Z3_mk_int_sort(ctx);
	bool_sort = Z3_mk_bool_sort(ctx);

	lvars = NULL;
	svars = NULL;

	if((form->lvars != NULL) && (form->lvars->size_ > 0)){
		lvars = (Z3_ast *)malloc(form->lvars->size_ * sizeof(Z3_ast));
		assert(lvars != NULL);

		for(i=0; i<form->lvars->size_; i++){
			lvars[i] = mk_var(ctx, form->lvars->data_[i]->vname, int_sort);
			
			if(form->space == NULL){
			       	spatial_forms = NULL;
			}else{
				spatial_forms = noll_space_array_new();
				get_space_array(form->space);
			}
			if( (spatial_forms != NULL) && (spatial_forms->size_ > 0)){
				alloc_m[i] = (Z3_ast *)malloc(spatial_forms->size_ * sizeof(Z3_ast));
				assert(alloc_m[i] != NULL);
				
				space_k = (Z3_ast *)malloc(spatial_forms->size_ * sizeof(Z3_ast));
				assert(space_k != NULL);

				sprintf(name, "SPACEK[%d]", i);
				space_k[i] = mk_var(ctx, name, int_sort);

				for(j=0; j<spatial_forms->size_; j++){
					sprintf(name, "ALLOC[%d][%d]", i, j);
					alloc_m[i][j] = mk_var(ctx, name, bool_sort);
				}
			}
		}
	}
		
	if((form->svars != NULL) && (form->svars->size_ > 0)){
		svars = (Z3_ast *)malloc(form->svars->size_ * sizeof(Z3_ast));
		assert(svars != NULL);

		for(i=0; i<form->svars->size_; i++)
			svars[i] = mk_var(ctx, form_svars->data_[i]->vname, int_sort);
	}



	init_ast_array(&abstr);
	if(form->pure != NULL)
		push_ast_array(&abstr, get_sl_form_abstr_p(ctx, form));
	if((sptial->forms != NULL) && (spatial_forms->size_ > 0))
		push_ast_array(&abstr, get_sl_form_abstr_s(ctx);

	return Z3_mk_and(ctx, abstr.size, abstr.data);
}

Z3_ast get_sl_form_abstr_p(Z3_context ctx, noll_form_t *form)
{
	assert(form != NULL);
	assert(form->pure != NULL);
	assert((form->pure->m != NULL) || (form->pure->data != NULL));

	int i, j;
	ast_array pure;

	init_ast_array(&pure);
	if(form->pure->m != NULL){
		for(i=0; i<form->pure->size-1; i++){
			for(j=1; j<form->pure->size-i; j++){
				if(form->pure->m[i][j] == NOLL_PURE_EQ)
					push_ast_array(&pure, Z3_mk_eq(ctx, lvars[i][j+i]));
				if(form->pure->m[i][j] == NOLL_PURE_NEQ)
					push_ast_array(&pure, Z3_mk_not(ctx, Z3_mk_eq(ctx, lvars[i][j+i])));
			}
		}
	}

	if(form->pure->data != NULL){
		for(i=0; i<form->pure->data->size_; i++)
			push_ast_array(&pure, get_sl_form_abstr_pd(ctx, form->pure->data->data_[i]));
	}

	return Z3_mk_and(ctx, pure.size, pure.data);
}

Z3_ast get_sl_form_abstr_pd_eq(Z3_context ctx, noll_dterm_array * dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ > 1);
	
	int i;
	ast_array t;

	init_ast_array(&t);
	for(i=0; i<dterms->size_-1; i++)
		push_ast_array(&t, Z3_mk_eq(ctx, get_sl_form_abstr_pd_term(ctx, dterms->data_[i]), get_sl_form_abstr_pd_term(ctx, dterms->data_[i+1])));
	return Z3_mk_and(ctx, t.size, t.data);
}


Z3_ast get_sl_form_abstr_pd_neq(Z3_context ctx, noll_dterm_array * dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ > 1);
	
	int i;
	ast_array t;

	init_ast_array(&t);
	for(i=0; i<dterms->size_; i++)
		push_ast_array(&t, get_sl_form_abstr_pd_term(ctx, dterms->data_[i]));	


	return Z3_mk_distinct(ctx, t.size, t.data);

}

Z3_ast get_sl_form_abstr_pd_ite(Z3_context ctx, noll_dterm_array *dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ == 3);
	
	return Z3_mk_ite(ctx, get_sl_form_abstr_pd(ctx, dterms->data_[0]->p->cond), get_sl_form_abstr_pd_term(ctx, dterms->data_[1]), get_sl_form_abstr_pd_term(ctx, dterms->data_[2]));
}

Z3_ast get_sl_form_abstr_pd_lt(Z3_context ctx, noll_dterm_array *dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ > 1);

	int i;
	ast_array t;

	init_ast_array(&t);
	for(i=0; i<dterms->size_-1; i++)
		push_ast_array(t, Z3_mk_lt(ctx, get_sl_form_abstr_pd_term(ctx, dterms->data_[i]), get_sl_form_abstr_pd_term(ctx, dterms->data_[i+1])));

	return Z3_mk_and(ctx, t.size, t.data);
}

Z3_ast get_sl_form_abstr_pd_gt(Z3_context ctx, noll_dterm_array *dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ > 1);

	int i;
	ast_array t;

	init_ast_array(&t);
	for(i=0; i<dterms->size_-1; i++)
		push_ast_array(&t, Z3_mk_gt(ctx, get_sl_form_abstr_pd_term(ctx, dterms->data_[i]), get_sl_form_abstr_pd_term(ctx, dterms->data_[i+1])));

	return Z3_mk_and(ctx, t.size, t.data);
}


Z3_ast get_sl_form_abstr_pd_le(Z3_context ctx, noll_dterm_array *dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ > 1);

	int i;
	ast_array t;

	init_ast_array(&t);
	for(i=0; i<dterms->size_-1; i++)
		push_ast_array(&t, Z3_mk_le(ctx, get_sl_form_abstr_pd_term(ctx, dterms->data_[i]), get_sl_form_abstr_pd_term(ctx, dterms->data_[i+1])));

	return Z3_mk_and(ctx, t.size, t.data);
}


Z3_ast get_sl_form_abstr_pd_ge(Z3_context ctx, noll_dterm_array *dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ > 1);

	int i;
	ast_array t;

	init_ast_array(&t);
	for(i=0; i<dterms->size_-1; i++)
		push_ast_array(&t, Z3_mk_ge(ctx, get_sl_form_abstr_pd_term(ctx, dterms->data_[i]), get_sl_form_abstr_pd_term(ctx, dterms->data_[i+1])));

	return Z3_mk_and(ctx, t.size, t.data);
}

Z3_ast get_sl_form_abstr_pd_plus(Z3_context, noll_dterm_array *dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ > 0);

	int i;
	ast_array t;

	init_ast_array(&t);
	for(i=0; i<dterms->size_; i++)
		push_ast_array(&t, get_sl_form_abstr_pd_term(ctx, dterms->data_[i]));
	return Z3_mk_add(ctx, t.size, t.data);
}


Z3_ast get_sl_form_abstr_pd_minus(Z3_context, noll_dterm_array *dterms)
{
	assert(dterms != NULL);
	assert(dterms->size_ > 0);

	int i;
	ast_array t;

	init_ast_array(&t);
	for(i=0; i<dterms->size_; i++)
		push_ast_array(&t, get_sl_form_abstr_pd_term(ctx, dterms->data_[i]));
	return Z3_mk_sub(ctx, t.size, t.data);
}

Z3_ast get_sl_form_abstr_pd_implies(Z3_context, noll_dform_array *dforms)
{
	assert(dforms != NULL);
	assert(dforms->size_ > 1);

	int i;
	Z3_ast ret;

	ret = get_sl_form_abstr_pd(ctx, dforms->data_[dforms->size_-1]);
	for(i = dforms->size_-2; i >=0; i--)
		ret = Z3_mk_implies(ctx, get_sl_form_abstr_pd(ctx, dforms->data_[i]), ret);
	
	return ret;	
}

Z3_ast get_sl_form_abstr_pd_term(Z3_context ctx, noll_dterm_t *dterm)
{
	assert(dterm != NULL);

	switch(dterm->kind){
		case NOLL_DATA_INT:
			Z3_sort int_sort = Z3_mk_int_sort(ctx);
			return Z3_mk_int(ctx, dterm->p->value, int_sort);
		case NOLL_DATA_VAR:
			return svars[dterm->p->sid];
		case NOLL_DATA_FIELD:
			return lvars[dterm->p->sid];
		case NOLL_DATA_EQ:
			return get_sl_form_abstr_pd_eq(ctx, dterm->args);
		case NOLL_DATA_NEQ:
			return get_sl_form_abstr_pd_neq(ctx, dterm->args);
		case NOLL_DATA_ITE:
			return get_sl_form_abstr_pd_ite(ctx, dterm->args);
		case NOLL_DATA_LT:
			return get_sl_form_abstr_pd_lt(ctx, dterm->args);
		case NOLL_DATA_GT:
			return get_sl_form_abstr_pd_gt(ctx, dterm->args);
		case NOLL_DATA_LE:
			return get_sl_form_abstr_pd_le(ctx, dterm->args);
		case NOLL_DATA_GE:
			return get_sl_form_abstr_pd_ge(ctx, dterm->args);
		case NOLL_DATA_PLUS:
			return get_sl_form_abstr_pd_plus(ctx, dterm->args);
		case NOLL_DATA_MINUS:
			return get_sl_form_abstr_pd_minus(ctx, dterm->args);
		//case NOLL_DATA_SUBSET:
		//	return get_sl_form_abstr_pd_subset(ctx, dform->p->targs);
		default:
			printf("Unsurport data constraints!\n");
			exit(0);
	}
}

Z3_ast get_sl_form_abstr_pd(Z3_context ctx, noll_dform_t * dform)
{
	assert(dform != NULL);
	
	switch(dform->kind){
		case NOLL_DATA_EQ:
			return get_sl_form_abstr_pd_eq(ctx, dform->p->targs);
		case NOLL_DATA_NEQ:
			return get_sl_form_abstr_pd_neq(ctx, dform->p->targs);
		case NOLL_DATA_ITE:
			return get_sl_form_abstr_pd_ite(ctx, dform->p->targs);
		case NOLL_DATA_LT:
			return get_sl_form_abstr_pd_lt(ctx, dform->p->targs);
		case NOLL_DATA_GT:
			return get_sl_form_abstr_pd_gt(ctx, dform->p->targs);
		case NOLL_DATA_LE:
			return get_sl_form_abstr_pd_le(ctx, dform->p->targs);
		case NOLL_DATA_GE:
			return get_sl_form_abstr_pd_ge(ctx, dform->p->targs);
		case NOLL_DATA_PLUS:
			return get_sl_form_abstr_pd_plus(ctx, dform->p->targs);
		case NOLL_DATA_MINUS:
			return get_sl_form_abstr_pd_minus(ctx, dform->p->targs);
		//case NOLL_DATA_SUBSET:
		//	return get_sl_form_abstr_pd_subset(ctx, dform->p->targs);
		case NOLL_DATA_IMPLIES:
			return get_sl_form_abstr_pd_implies(ctx, dform->p->targs);
		default:
			printf("Unsurport data constraints!\n");
			exit(0);
	}
}
