//check sat procedure

#ifndef SLID_SAT_H
#define SLID_SAT_H

#include <z3.h>

#include "noll_vector.h"
#include "noll_form.h"
#include "noll_preds.h"

typedef enum{
	SLID_UNSAT = 0,
	SLID_SAT,
	SLID_UNDEF
}slid_sat_t;

typedef enum{
	SLID_DATA_CONSTR_CONST = 0,
	SLID_DATA_CONSTR_STATIC,
	SLID_DATA_CONSTR_TRANS,
	SLID_DATA_CONSTR_UNDEF
}slid_data_constr_t;

typedef struct{
	int sid;
	noll_dform_array *ce;
	noll_dform_t *cl;
	noll_dform_t *cg;
	noll_dform_array *stc;
	noll_dform_array *trans;
}slid_data_constr;

NOLL_VECTOR_DECLARE(slid_data_constr_array, slid_data_constr *);
NOLL_VECTOR_DECLARE(z3_ast_array, Z3_ast);

//context of the noll formula to be transformed to Z3 formula
typedef struct{
	z3_ast_array *var;        //nil + variables in the formula
	z3_ast_array *k;          //times unfolding the predicates
	noll_space_array *space;  //spatial part of the formula
	Z3_ast **m;               //matrix of bool variables
	size_t row;               //size of space array
	size_t column;            //size of var array
	Z3_sort int_sort, bool_sort;
}_slid_context;

typedef _slid_context* slid_context;


int slid_sat_check(noll_form_t *);

slid_context slid_mk_context(Z3_context, noll_form_t *);
void slid_del_context(slid_context);

void slid_mk_space_array(noll_space_array **, noll_space_t *);

//
Z3_ast slid_mk_abstr(Z3_context, slid_context, noll_form_t *);

Z3_ast slid_mk_pure_abstr(Z3_context, slid_context, noll_pure_t *);

Z3_ast slid_mk_pure_data_constr(Z3_context, slid_context, noll_dform_t *);
Z3_ast _slid_mk_pure_data_constr1(Z3_context, slid_context, noll_dterm_array *, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));
Z3_ast _slid_mk_pure_data_constr2(Z3_context, slid_context, noll_dterm_array *, Z3_ast (*)(Z3_context, unsigned int, Z3_ast const[]));
Z3_ast slid_mk_ite(Z3_context, slid_context, noll_dterm_t *);
Z3_ast slid_mk_implies(Z3_context, slid_context, noll_dform_array *);
Z3_ast slid_mk_term(Z3_context, slid_context, noll_dterm_t *);

Z3_ast slid_mk_space_abstr(Z3_context, slid_context); 

Z3_ast slid_mk_pto(Z3_context, slid_context, noll_pto_t *, int);
Z3_ast slid_mk_pred(Z3_context, slid_context, noll_ls_t *, int);
Z3_ast slid_mk_unfold(Z3_context, slid_context, noll_ls_t *, int);
Z3_ast slid_mk_fir_unfold(Z3_context, slid_context, noll_ls_t *, int);
Z3_ast slid_mk_sec_unfold(Z3_context, slid_context, noll_ls_t *, int);
int slid_get_hole(noll_pred_t *);
Z3_ast slid_mk_closures(Z3_context, slid_context, noll_ls_t *, int);
Z3_ast slid_mk_closure(Z3_context, slid_context, slid_data_constr *,  noll_ls_t *, int);
//Z3_ast _slid_mk_closure(Z3_context, slid_context, noll_ls_t *, int, Z3_ast, noll_dterm_t *, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));
//int slid_get_counterpart(noll_pred_t *, int);
//int slid_get_src_para_num(noll_pred_t *);
int slid_get_trans_loc(noll_pred_rule_t *, int);
slid_data_constr *slid_get_pred_data_constr(noll_pred_t *, noll_pred_rule_t *, int);
void slid_del_pred_data_constr(slid_data_constr *);
noll_dform_array *slid_get_pred_data_constr_ce(noll_pred_t *, noll_pred_rule_t *, int);
noll_dform_t *slid_get_pred_data_constr_clg(noll_pred_rule_t *, int, noll_data_op_t);
noll_dform_array *slid_get_pred_data_constr_stc(noll_pred_t *, noll_pred_rule_t *, int);
noll_dform_array *slid_get_pred_data_constr_trans(noll_pred_t *, noll_pred_rule_t *, int);
noll_ls_t *slid_get_rule_pred(noll_space_t *);
bool slid_is_trans_para(int, int, noll_pred_rule_t *);
slid_data_constr_t slid_get_pred_data_constr_type(noll_pred_t *, noll_pred_rule_t *, noll_dform_t *);

Z3_ast slid_mk_pred_data_constr_cst(Z3_context, slid_context, slid_data_constr *, noll_ls_t *);
Z3_ast _slid_mk_pred_data_constr_cst(Z3_context, slid_context, noll_dform_t *, noll_ls_t *);


Z3_ast slid_mk_pred_data_constr_stc(Z3_context, slid_context, slid_data_constr *, noll_ls_t *);
Z3_ast _slid_mk_pred_data_constr_stc(Z3_context, slid_context, noll_dform_t *, noll_ls_t *, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));


Z3_ast slid_mk_pred_data_constr_trans(Z3_context, slid_context, slid_data_constr *, noll_ls_t *, int);
Z3_ast _slid_mk_pred_data_constr_trans(Z3_context, slid_context, slid_data_constr *, noll_dform_t *, noll_ls_t *, int, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));

Z3_ast slid_mk_assist_constr(Z3_context, slid_context, slid_data_constr *, noll_dform_t *, noll_ls_t *, int);
Z3_ast _slid_mk_assist_constr(Z3_context, slid_context, noll_dterm_t *, noll_ls_t *, Z3_ast, Z3_ast, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));

Z3_ast slid_mk_sep_constr(Z3_context, slid_context);


#endif //slid_sat.h
