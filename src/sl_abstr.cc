#include <algorithm>
#include "sl_abstr.h"
#include "sl_sat.h"
#include <string>

using namespace std;

int sl_abstr::_counter;


vector<Z3_ast> sl_abstr::get_k_m_ast()
{
	vector<Z3_ast> res;

	for (size_t i = 0; i < k.size(); ++i)
		res.push_back(k[i].node);
	for (size_t i = 0; i < m.size(); ++i) {
		for (size_t j = 0; j < m[i].size(); ++j)
			res.push_back(m[i][j].node);
	}
	return res;
}
sl_abstr::sl_abstr(const sl_abstr& abs)
{
	f = abs.f;
	ctx = abs.ctx;
	k = abs.k;
	m = abs.m;
	abstr = abs.abstr;
	//id = abs.id;
}
sl_abstr& sl_abstr::operator=(const sl_abstr& abs)
{
	if (this == &abs)
		return *this;
	f = abs.f;
	ctx = abs.ctx;
	k = abs.k;
	m = abs.m;
	abstr = abs.abstr;
	//id = abs.id;
}
sl_abstr::sl_abstr(sl_abstr&& abs) noexcept
{
	f = abs.f;
	ctx = abs.ctx;
	k = abs.k;
	m = abs.m;
	abstr = abs.abstr;
	//id = abs.id;
	abs.abstr = nullptr;
}
sl_abstr& sl_abstr::operator=(sl_abstr&& abs) noexcept
{
	if (this == &abs)
		return *this;
	f = abs.f;
	ctx = abs.ctx;
	k = abs.k;
	m = abs.m;
	abstr = abs.abstr;
	//id = abs.id;
	abs.abstr = nullptr;
}
size_t sl_abstr::get_var_size()
{
	return ctx.var.size();
}
sl_context& sl_abstr::get_context()
{
	return ctx;
}
/*
 *vector<Z3_symbol> sl_abstr::get_z3_symbol_k()
 *{
 *        vector<Z3_symbol> res;
 *        for (size_t i = 0; i < k.size(); ++i)
 *                res.push_back(k[i].symbol);
 *        return res;
 *}
 *vector<Z3_symbol> sl_abstr::get_z3_symbol_m()
 *{
 *        vector<Z3_symbol> res;
 *        for (size_t i = 0; i < m.size(); ++i) {
 *                for (size_t j = 0; j < m[i].size(); ++j)
 *                        res.push_back(m[i][j].symbol);
 *        }
 *        return res;
 *}
 */

bool sl_abstr::check_eq(size_t u, size_t v)
{
	Z3_ast a, b, eq, c[2];
	a = ctx.var[u].node;
	b = ctx.var[v].node;
	eq = Z3_mk_eq(ctx.z3_ctx, a, b);
	c[0] = abstr;
	c[1] = Z3_mk_not(ctx.z3_ctx, eq);
	if (!sl_sat::check_sat(ctx.z3_ctx, Z3_mk_and(ctx.z3_ctx, 2, c)))
		return true;
	return false;
}
bool sl_abstr::check_eq(Z3_ast a, Z3_ast b)
{
	Z3_ast eq, c[2];
	eq = Z3_mk_eq(ctx.z3_ctx, a, b);
	c[0] = abstr;
	c[1] = Z3_mk_not(ctx.z3_ctx, eq);
	if (!sl_sat::check_sat(ctx.z3_ctx, Z3_mk_and(ctx.z3_ctx, 2, c)))
		return true;
	return false;
}
Z3_ast sl_abstr::get_abstr()
{
	if (abstr == nullptr)
		mk_abstr();
	return abstr;
}
void sl_abstr::set_abstr(Z3_ast ast)
{
	abstr = ast;
}
vector<noll_space_t*>& sl_abstr::get_spatial_atoms()
{
	return f.sp_atoms;
}
Z3_ast sl_abstr::get_unfold_times(size_t sid)
{
	return k[sid].node;
}
Z3_context sl_abstr::get_z3_context()
{
	return ctx.z3_ctx;
}
Z3_sort sl_abstr::get_z3_sort_int()
{
	return ctx.isort;
}

Z3_sort sl_abstr::get_z3_sort_bool()
{
	return ctx.bsort;
}
Z3_ast sl_abstr::get_var_ast(size_t i)
{
	return ctx.var[i].node;
}
void sl_abstr::add_var(sl_var& v)
{
	ctx.var.push_back(v);
}
bool sl_abstr::check_sat()
{
	if (abstr == nullptr)
		mk_abstr();
	return sl_sat::check_sat(ctx.z3_ctx, abstr);
}
bool sl_abstr::is_sp_atom_empty(size_t i)
{
	Z3_ast k_ast = get_unfold_times(i);
	Z3_ast zero, a[2];
	zero = Z3_mk_int(ctx.z3_ctx, 0, ctx.isort);
	a[0] = get_abstr();
	a[1] = Z3_mk_gt(ctx.z3_ctx, k_ast, zero);
	if (!sl_sat::check_sat(ctx.z3_ctx, Z3_mk_and(ctx.z3_ctx, 2, a)))
		return true;
	return false;
}
bool sl_abstr::check_sat_unfold_once(size_t k)
{
	Z3_ast k_ast = get_unfold_times(k);
	Z3_ast one, a[2];
	one = Z3_mk_int(get_z3_context(), 1, get_z3_sort_int());
	a[0] = get_abstr();
	a[1] = Z3_mk_eq(get_z3_context(), k_ast, one);
	return sl_sat::check_sat(get_z3_context(), Z3_mk_and(get_z3_context(), 2, a));
}
bool sl_abstr::check_sat_unfold_twice(size_t k)
{
	Z3_ast k_ast = get_unfold_times(k);
	Z3_ast two, a[2];
	two = Z3_mk_int(get_z3_context(), 2, get_z3_sort_int());
	a[0] = get_abstr();
	a[1] = Z3_mk_ge(get_z3_context(), k_ast, two);
	return sl_sat::check_sat(get_z3_context(), Z3_mk_and(get_z3_context(), 2, a));
}

void sl_abstr::init_bvar(sl_for& formula)
{
	noll_space_t *space;
	for (size_t i = 0; i < formula.sp_atoms.size(); ++i) {
		space = formula.sp_atoms[i];
		switch(space->kind){
		case NOLL_SPACE_PTO:
			m.push_back(mk_pto_bvar(space->m.pto.sid, i));
			break;
		case NOLL_SPACE_LS:
			m.push_back(mk_ls_bvar(&(space->m.ls), i));
			break;
		}
	}
}
vector<sl_var> sl_abstr::mk_pto_bvar(size_t id, size_t i)
{
	vector<sl_var> res;
	
	res.push_back(mk_bvar(id, i));

	return res;
}
sl_var sl_abstr::mk_bvar(size_t id, size_t i)
{
	noll_var_t* var;
	sl_var res;
	string tmp;
	string str;

	var = noll_vector_at(f.nollf->lvars, id);
	//str = (char *)malloc(sizeof(char)*(strlen(var->vname)+strlen("[,]")+3));
	//assert(str != NULL);
	//sprintf(str, "%d_[%s, %d]", _counter, var->vname, i);
	tmp = var->vname;
	str = to_string(_counter) + "_[" + tmp + "," + to_string(i) + "]";
	res.sid = id;
	/*
	 *res.type = ctx.bsort;
	 *res.symbol = Z3_mk_string_symbol(ctx.z3_ctx, str);
	 */
	res.node = Z3_mk_const(ctx.z3_ctx, Z3_mk_string_symbol(ctx.z3_ctx, str.c_str()), ctx.bsort);

	return res;
}
vector<int> sl_abstr::get_in_alloc_loc_index(noll_ls_t *ls)
{
	int i, j, k;
	noll_pred_t* pred;
	noll_pred_rule_t* r;
	vector<int> res;

	res.push_back(noll_vector_at(ls->args, 0));

	pred = noll_vector_at(preds_array, ls->pid);
	r = noll_vector_at(pred->def->rec_rules, 0);
	while((i = slid_get_trans_loc(r, 1)) > 0){
		j = slid_get_hole(pred) + i;
		k = noll_vector_at(ls->args, j);
		res.push_back(k);
	}

	return res;
}
vector<sl_var> sl_abstr::mk_ls_bvar(noll_ls_t* ls, size_t i)
{
	vector<int> t;
	vector<sl_var> res;
	t = get_in_alloc_loc_index(ls);
	for (size_t k = 0; k < t.size(); ++k)
		res.push_back(mk_bvar(t[k], i));

	return res;
}

void sl_abstr::init_kvar(sl_for& formula)
{
	noll_space_t* space;
	Z3_symbol symbol;
	Z3_ast node;
	sl_var var;

	for(size_t i = 0; i < formula.sp_atoms.size(); ++i){
		space = formula.sp_atoms[i];
		string str = to_string(_counter) + "_k_" + to_string(i);
		//str = (char *)malloc(sizeof(char) * (strlen("slid_k_")+3));
		//assert(str != NULL);
		//sprintf(str, "%d_k_%d", _counter, i);
		symbol = Z3_mk_string_symbol(ctx.z3_ctx, str.c_str());
		node = Z3_mk_const(ctx.z3_ctx, symbol, ctx.isort);
		k.push_back(sl_var(i, node));
	}
}
sl_abstr::sl_abstr(noll_form_t* f0, sl_context& c)
: f(f0), ctx(c), abstr(nullptr)
{
	if(!f.sp_atoms.empty()){	
		init_bvar(f);
		init_kvar(f);
		_counter++;
	}
}
void sl_abstr::init(noll_form_t* f0, sl_context& c)
{
	f.init(f0);
	ctx = c;
	if(!f.sp_atoms.empty()){	
		init_bvar(f);
		init_kvar(f);
		_counter++;
	}
}

void sl_abstr::mk_abstr()
{
	assert(f.nollf != NULL);


	abstr = Z3_mk_true(ctx.z3_ctx);
	if((f.nollf)->pure != NULL) {
		mk_pure_abstr((f.nollf)->pure);
	
		Z3_solver s;
		s = Z3_mk_solver(ctx.z3_ctx);
		Z3_solver_inc_ref(ctx.z3_ctx, s);

		Z3_solver_assert(ctx.z3_ctx, s, abstr);
		if(Z3_solver_check(ctx.z3_ctx, s) == Z3_L_FALSE){
			//slid_ctx->sat_type = SLID_UNSAT;
			//f->kind = NOLL_FORM_UNSAT;
			return;
		}
	}

	if(!f.sp_atoms.empty())
		mk_space_abstr();
}


void sl_abstr::mk_pure_abstr(noll_pure_t *pure)
{
	assert(pure != NULL);

	unsigned int i, j, k;
	Z3_ast t1, t2, t3;
	noll_dform_t *t4;
	z3_ast_array *t;

	t = z3_ast_array_new();
	z3_ast_array_push(t, abstr);
	if((pure->m != NULL) && (pure->size > 0)){
		for(i = 0; i < pure->size-1; i++){
			for(j = 1; j < pure->size-i; j++){
				t1 = ctx.var[i].node;
				t2 = ctx.var[i+j].node;
				if(pure->m[i][j] == NOLL_PURE_EQ){
					t3 = Z3_mk_eq(ctx.z3_ctx, t1, t2);
					z3_ast_array_push(t, t3);
				}
				if(pure->m[i][j] == NOLL_PURE_NEQ){
					t3 = Z3_mk_eq(ctx.z3_ctx, t1, t2);
					z3_ast_array_push(t, Z3_mk_not(ctx.z3_ctx, t3));
				}
			}
		}
	}

	if((pure->data != NULL) && (!noll_vector_empty(pure->data))){
		for(k = 0; k < noll_vector_size(pure->data); k++){
			t4 = noll_vector_at(pure->data, k);
			t1 = mk_pure_data_constr(t4);
			if(t1 != NULL) z3_ast_array_push(t, t1);
		}
	}

	abstr = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);
}

Z3_ast sl_abstr::mk_pure_data_constr(noll_dform_t *data)
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
		return mk_pure_data_constr1(data->p.targs, fun_arr1[data->kind]);
	case NOLL_DATA_NEQ:
	case NOLL_DATA_PLUS:
	case NOLL_DATA_MINUS:
		return mk_pure_data_constr2(data->p.targs, fun_arr2[data->kind-5]);
	case NOLL_DATA_IMPLIES:
		return mk_implies(data->p.bargs);
	default:
		printf("Unsurport operator!\n");
		exit(1);
	}
}

Z3_ast sl_abstr::mk_pure_data_constr1(noll_dterm_array * terms, Z3_ast (*f)(Z3_context, Z3_ast, Z3_ast))
{
	assert(terms != NULL);
	assert(noll_vector_size(terms) > 1);
	
	unsigned int i;
	Z3_ast a1, a2, ret = NULL;
	z3_ast_array *t;

	t = z3_ast_array_new();
	for(i = 0; i < noll_vector_size(terms)-1; i++){
		a1 = mk_term(noll_vector_at(terms, i));
		a2 = mk_term(noll_vector_at(terms, i+1));
		z3_ast_array_push(t, f(ctx.z3_ctx, a1, a2)); 
	}
	if(!noll_vector_empty(t))
		ret = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}


Z3_ast sl_abstr::mk_pure_data_constr2(noll_dterm_array *terms, Z3_ast (*f)(Z3_context, unsigned int, Z3_ast const[]))
{
	assert(terms != NULL);
	assert(noll_vector_size(terms) > 1);
	
	unsigned int i;
	z3_ast_array *t;
	Z3_ast t1, ret = NULL;

	t = z3_ast_array_new();
	for(i = 0; i < noll_vector_size(terms); i++){
		t1 = mk_term(noll_vector_at(terms, i));
		if(t1 != NULL) z3_ast_array_push(t, t1);	
	}
	
	if(!noll_vector_empty(t))
		ret = f(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

Z3_ast sl_abstr::mk_ite(noll_dterm_t *term)
{
	assert(term != NULL);
	assert(term->args != NULL);
	assert(noll_vector_size(term->args) == 2);

	Z3_ast cond, s, t;


	cond = mk_pure_data_constr(term->p.cond);
	s = mk_term(noll_vector_at(term->args, 0));
	t = mk_term(noll_vector_at(term->args, 1));
	

	return Z3_mk_ite(ctx.z3_ctx, cond, s, t);
}


Z3_ast sl_abstr::mk_implies(noll_dform_array *forms)
{
	assert(forms != NULL);
	assert(noll_vector_size(forms) > 1);

	int i;
	noll_dform_t *df;
	Z3_ast t, ret = NULL;


	df = noll_vector_at(forms, noll_vector_size(forms)-1);
	ret = mk_pure_data_constr(df);
	for(i = noll_vector_size(forms)-2; i >= 0; i--){
		df = noll_vector_at(forms, i);
		t = mk_pure_data_constr(df);
		ret = Z3_mk_implies(ctx.z3_ctx, t, ret);
	}
	
	return ret;	
}

Z3_ast sl_abstr::mk_term(noll_dterm_t *term)
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
		return mk_pure_data_constr1(term->args, fun_arr1[term->kind]);
	case NOLL_DATA_NEQ:
	case NOLL_DATA_PLUS:
	case NOLL_DATA_MINUS:
		return mk_pure_data_constr2(term->args, fun_arr2[term->kind-5]);
	case NOLL_DATA_INT:
		return Z3_mk_int(ctx.z3_ctx, term->p.value, ctx.isort);
	case NOLL_DATA_VAR:
		return ctx.var[term->p.sid].node;
	case NOLL_DATA_ITE:
		return mk_ite(term);
	default:
		printf("Unsurport operator of data constraints!\n");
		exit(1);
	}
}


void sl_abstr::mk_space_abstr()
{
	unsigned int i;
	z3_ast_array *t;
	noll_space_t *t1;
	Z3_ast t2, t3;

	t = z3_ast_array_new();
	z3_ast_array_push(t, abstr);
	for(i = 0; i < f.sp_atoms.size(); i++){
		t1 = f.sp_atoms[i];
		switch(t1->kind){
		case NOLL_SPACE_PTO:
			t2 = mk_pto(&(t1->m.pto), i);
			if(t2 != NULL) z3_ast_array_push(t, t2);
			break;
		case NOLL_SPACE_LS:
			t2 = mk_pred(&(t1->m.ls), i);
			if(t2 != NULL) z3_ast_array_push(t, t2);
			break;
		}
	}

	t3 = mk_sep_constr();
	if(t3 != NULL) z3_ast_array_push(t, t3);

	abstr = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);
}

Z3_ast sl_abstr::mk_pto(noll_pto_t *pto, int i)
{
	assert(pto != NULL);

	Z3_ast r[2];
	Z3_ast ki, one;
	one = Z3_mk_int(ctx.z3_ctx, 1, ctx.isort);
	ki = k[i].node;
	r[0] = Z3_mk_eq(ctx.z3_ctx, ki, one);
	size_t sid = pto->sid;
	r[1] = (*find_if(begin(m[i]), end(m[i]), [sid](sl_var& v){return v.sid==sid;})).node;

	return Z3_mk_and(ctx.z3_ctx, 2, r);
}
Z3_ast sl_abstr::mk_abstr(noll_ls_t* pred, size_t ki)
{
	assert(pred != NULL);

	vector<int> loc = get_trans_loc(pred);
	vector<Z3_ast> s, t;
	Z3_ast a[2], t1 = NULL;

	a[0] = mk_fir_unfold(pred, ki, loc);
	a[1] = mk_sec_unfold(pred, ki, loc);

	t.push_back(mk_unfold(pred, ki));
	
	s.push_back(Z3_mk_or(ctx.z3_ctx, 2, a));
	t1 = mk_closures(pred, ki);
	if (t1 != NULL)
		s.push_back(t1);
	t.push_back(Z3_mk_and(ctx.z3_ctx, s.size(), &(*(begin(s)))));

	return Z3_mk_or(ctx.z3_ctx, t.size(), &(*(begin(t))));
}

vector<int> sl_abstr::get_trans_loc(noll_ls_t* pred)
{
	vector<int> res;
	noll_pred_t* def_pred;
	noll_pred_rule_t* r;
	noll_ls_t *p;

	def_pred = noll_vector_at(preds_array, pred->pid);
	r = noll_vector_at(def_pred->def->rec_rules, 0);

	p = slid_get_rule_pred(r->rec);

	for(size_t i = 0; i < noll_vector_size(p->args); i++){
		if(noll_vector_at(p->args, i) == 1)
			res.push_back(noll_vector_at(pred->args, slid_get_hole(def_pred) + i));
	}
	return res;
}

Z3_ast sl_abstr::mk_pred(noll_ls_t *pred, int ki)
{
	assert(pred != NULL);

	vector<int> loc = get_trans_loc(pred);
	vector<Z3_ast> s, t;
	Z3_ast a[2], t1, t2, t3, t4, t5 = NULL;

	a[0] = mk_fir_unfold(pred, ki, loc);
	a[1] = mk_sec_unfold(pred, ki, loc);
	loc.push_back(noll_vector_at(pred->args, 0));
	for (size_t i = 0; i < loc.size(); ++i) {
		Z3_ast bvar;
		int sid = loc[i];
		bvar = (*find_if(begin(m[ki]), end(m[ki]), [sid](sl_var& v){return v.sid==sid;})).node;
		t.push_back(Z3_mk_not(ctx.z3_ctx, bvar));
		s.push_back(bvar);
	}
	t.push_back(mk_unfold(pred, ki));
	
	t3 = Z3_mk_and(ctx.z3_ctx, t.size(), &(*(begin(t))));
	t.clear();
	t.push_back(t3);

	t4 = Z3_mk_and(ctx.z3_ctx, s.size(), &(*(begin(s))));
	s.clear();
	s.push_back(t4);

	s.push_back(Z3_mk_or(ctx.z3_ctx, 2, a));
	t5 = mk_closures(pred, ki);
	if (t5 != NULL)
		s.push_back(t5);
	t.push_back(Z3_mk_and(ctx.z3_ctx, s.size(), &(*(begin(s)))));

	return Z3_mk_or(ctx.z3_ctx, t.size(), &(*(begin(t))));
}


Z3_ast sl_abstr::mk_unfold(noll_ls_t *pred, int ki)
{
	unsigned int i, j, l;
	z3_ast_array * t, *t1;
	Z3_ast t2, t3, t4, t5, ret = NULL;
	noll_pred_t *ppred;
	noll_pred_rule_t *br;

	t = z3_ast_array_new();
	ppred = noll_vector_at(preds_array, pred->pid);

	for(l = 0; l < noll_vector_size(ppred->def->base_rules); l++){
		t1 = z3_ast_array_new();
		br = noll_vector_at(ppred->def->base_rules, l);



		assert(br->pure->m != NULL);
		assert(br->pure->size > 0);
		for(i = 0; i < br->pure->size-1; i++){
			for(j = 1; j < br->pure->size-i; j++){
				if(i == 0)
					t2 = ctx.var[0].node;
				else 
					t2 = ctx.var[noll_vector_at(pred->args, i-1)].node;
				t3 = ctx.var[noll_vector_at(pred->args, i+j-1)].node;
				if(br->pure->m[i][j] == NOLL_PURE_EQ){
					t4 = Z3_mk_eq(ctx.z3_ctx, t2, t3);
					z3_ast_array_push(t1, Z3_mk_eq(ctx.z3_ctx, t2, t3));
				}
				if(br->pure->m[i][j] == NOLL_PURE_NEQ){
					t4 = Z3_mk_eq(ctx.z3_ctx, t2, t3);
					z3_ast_array_push(t1, Z3_mk_not(ctx.z3_ctx, t4));
				}
			}
		}
		t5 = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
		z3_ast_array_push(t, t5);
		z3_ast_array_delete(t1);
		
	}
	t4 = Z3_mk_or(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_clear(t);
	z3_ast_array_push(t, t4);

	t2 = k[ki].node;
	t3 = Z3_mk_int(ctx.z3_ctx, 0, ctx.isort);
	z3_ast_array_push(t, Z3_mk_eq(ctx.z3_ctx, t2, t3));

	ret = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}
Z3_ast sl_abstr::mk_fir_unfold(noll_ls_t *pred, int ki, vector<int>& loc)
{
	assert(pred->pid >= 0);
	assert(pred->pid < noll_vector_size(preds_array));

	vector<Z3_ast> t;
	Z3_ast t1, t2;

	t1 = ctx.var[noll_vector_at(pred->args, 0)].node;
	for (size_t i = 0; i < loc.size(); ++i) {
		t2 = ctx.var[loc[i]].node;
		t.push_back(Z3_mk_eq(ctx.z3_ctx, t1, t2));
	}
	
	t1 = k[ki].node;
	t2 = Z3_mk_int(ctx.z3_ctx, 1, ctx.isort);
	t.push_back(Z3_mk_eq(ctx.z3_ctx, t1, t2));
	
	return Z3_mk_and(ctx.z3_ctx, t.size(), &(*(begin(t))));
}
Z3_ast sl_abstr::mk_sec_unfold(noll_ls_t *pred, int ki, vector<int>& loc)
{
	assert(pred->pid >= 0);
	assert(pred->pid < noll_vector_size(preds_array));

	vector<Z3_ast> t;
	Z3_ast t1, t2;

	t1 = ctx.var[noll_vector_at(pred->args, 0)].node;
	for (size_t i = 0; i < loc.size(); ++i) {
		t2 = ctx.var[loc[i]].node;
		t.push_back(Z3_mk_not(ctx.z3_ctx, Z3_mk_eq(ctx.z3_ctx, t1, t2)));
	}
	
	t1 = k[ki].node;
	t2 = Z3_mk_int(ctx.z3_ctx, 2, ctx.isort);
	t.push_back(Z3_mk_ge(ctx.z3_ctx, t1, t2));
	
	return Z3_mk_and(ctx.z3_ctx, t.size(), &(*(begin(t))));
}

Z3_ast sl_abstr::mk_closures(noll_ls_t *pred, int ki)
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
			t4 = mk_closure(dc, pred, ki);
			if(t4 != NULL) z3_ast_array_push(t1, t4); 
		}
		if(!noll_vector_empty(t1)){
			t4 = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t1), noll_vector_array(t1));
			z3_ast_array_push(t, t4);

			z3_ast_array_clear(t1);

			for (j = 0; j < noll_vector_size(t2); j++)
				slid_del_pred_data_constr(noll_vector_at(t2, j));
			slid_data_constr_array_clear(t2);
		}
	}

	if(!noll_vector_empty(t))
		ret = Z3_mk_or(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

Z3_ast sl_abstr::mk_closure(slid_data_constr *dc, noll_ls_t *p, int ki)
{
	noll_dform_t *df;
	z3_ast_array *t;
	Z3_ast t1, ret;

	t = z3_ast_array_new();
	assert(t != NULL);

	t1 = mk_pred_data_constr_cst(dc, p);
	if(t1 != NULL) z3_ast_array_push(t, t1);

	t1 = mk_pred_data_constr_stc(dc, p);
	if(t1 != NULL) z3_ast_array_push(t, t1);

	if(dc->trans != NULL){
		t1 = mk_pred_data_constr_trans(dc, p, ki);
		if(t1 != NULL) z3_ast_array_push(t, t1);
	}

	if(noll_vector_empty(t))
		ret = NULL;
	else
		ret = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));

	z3_ast_array_delete(t);
	return ret;
}
Z3_ast sl_abstr::mk_pred_data_constr_cst(slid_data_constr *dc, noll_ls_t *p)
{
	unsigned int i;
	noll_dform_t *df;
	z3_ast_array *t;
	Z3_ast t1, ret = NULL;
	
	t = z3_ast_array_new();
	if(dc->ce != NULL){
		for(i = 0; i < noll_vector_size(dc->ce); i++){
			df = noll_vector_at(dc->ce, i);
			t1 = mk_pred_data_constr_cst(df, p);
			if(t1 != NULL) z3_ast_array_push(t, t1);
		}
	}

	if(dc->cl != NULL){
		t1 = mk_pred_data_constr_cst(dc->cl, p);
		if(t1 != NULL) z3_ast_array_push(t, t1);
	}

	if(dc->cg != NULL){
		t1 = mk_pred_data_constr_cst(dc->cg, p);
		if(t1 != NULL) z3_ast_array_push(t, t1);
	}

	if(noll_vector_empty(t))
		ret = NULL;
	else
		ret = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

Z3_ast sl_abstr::mk_pred_data_constr_cst(noll_dform_t *dform, noll_ls_t *pred)
{
	int c;
	Z3_ast a, b;
		
	a = ctx.var[noll_vector_at(pred->args, noll_vector_at(dform->p.targs, 0)->p.sid-1)].node;
	c = noll_vector_at(dform->p.targs, 1)->p.value;
	b = Z3_mk_int(ctx.z3_ctx, c, ctx.isort);
	switch(dform->kind){
	case NOLL_DATA_EQ:
		return Z3_mk_eq(ctx.z3_ctx, a, b);
	case NOLL_DATA_LE:
		return Z3_mk_le(ctx.z3_ctx, a, b);
	case NOLL_DATA_GE:
		return Z3_mk_ge(ctx.z3_ctx, a, b);
	}
	return NULL;
}

Z3_ast sl_abstr::mk_pred_data_constr_stc(slid_data_constr *dc, noll_ls_t *p)
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
				t1 = mk_pred_data_constr_stc(df, p, Z3_mk_eq);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			case NOLL_DATA_LE:
				t1 = mk_pred_data_constr_stc(df, p, Z3_mk_le);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			case NOLL_DATA_GE:
				t1 = mk_pred_data_constr_stc(df, p, Z3_mk_ge);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			}	
		}
		if(noll_vector_empty(t))
			ret = NULL;
		else
			ret = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));

		z3_ast_array_delete(t);
	}


	return ret;
}

Z3_ast sl_abstr::mk_pred_data_constr_stc(noll_dform_t *df, noll_ls_t *p,\
					Z3_ast (*op_func)(Z3_context, Z3_ast, Z3_ast))
{
	noll_dterm_t *t1, *t2, *t3, *t4;
	Z3_ast a, b;
	Z3_ast c[2];
	Z3_ast d[2];

	t1 = noll_vector_at(df->p.targs, 0);
	t2 = noll_vector_at(df->p.targs, 1);

	a = ctx.var[noll_vector_at(p->args, t1->p.sid-1)].node;
	switch(t2->kind){
	case NOLL_DATA_VAR:
		b = ctx.var[noll_vector_at(p->args, t2->p.sid-1)].node;
		return op_func(ctx.z3_ctx, a, b);
	case NOLL_DATA_PLUS:
		t3 = noll_vector_at(t2->args, 0);
		t4 = noll_vector_at(t2->args, 1);
		c[0] = ctx.var[noll_vector_at(p->args, t3->p.sid-1)].node;
		c[1] = Z3_mk_int(ctx.z3_ctx, t4->p.value, ctx.isort);
		b = Z3_mk_add(ctx.z3_ctx, 2, c);
		return op_func(ctx.z3_ctx, a, b);
	}

	return NULL;
}


Z3_ast sl_abstr::mk_pred_data_constr_trans(slid_data_constr *dc, noll_ls_t *p, int ki)
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
				t1 = mk_pred_data_constr_trans(dc, df, p, ki, Z3_mk_eq);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			case NOLL_DATA_LE:
				t1 = mk_pred_data_constr_trans(dc, df, p, ki, Z3_mk_le);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			case NOLL_DATA_GE:
				t1 = mk_pred_data_constr_trans(dc, df, p, ki, Z3_mk_ge);
				if(t1 != NULL) z3_ast_array_push(t, t1);
				break;
			}
		}

		if(noll_vector_empty(t))
			ret = NULL;
		else
			ret = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));

		z3_ast_array_delete(t);
	}


	return ret;
}

Z3_ast sl_abstr::mk_pred_data_constr_trans(slid_data_constr *dc, noll_dform_t *df, noll_ls_t *p, int ki,\
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

	a = ctx.var[noll_vector_at(p->args, t1->p.sid-1)].node;
	switch(t2->kind){
	case NOLL_DATA_VAR:
		n = noll_vector_at(p->args, hole + t1->p.sid -1);
		b = ctx.var[n].node;
		return op_func(ctx.z3_ctx, a, b);
	case NOLL_DATA_PLUS:
		t = z3_ast_array_new();
		t3 = noll_vector_at(t2->args, 0);
		t4 = noll_vector_at(t2->args, 1);
		c[0] = k[ki].node;
		c[1] = Z3_mk_int(ctx.z3_ctx, t4->p.value, ctx.isort);
		d[0] = Z3_mk_mul(ctx.z3_ctx, 2, c);
		d[1] = ctx.var[noll_vector_at(p->args, hole + t1->p.sid -1)].node;
		b = Z3_mk_add(ctx.z3_ctx, 2, d);
		z3_ast_array_push(t, op_func(ctx.z3_ctx, a, b));

		/*if(((t4->p.value < 0)\
		&& ((df->kind == NOLL_DATA_LE) && (dc->cl != NULL)))\
		|| ((t4->p.value >0)\
		&& (df->kind == NOLL_DATA_GE) && (dc->cg != NULL))){
			e = slid_mk_assist_constr(z3_ctx, slid_ctx, dc, df, p, k);
			if(e != NULL) z3_ast_array_push(t, e);
		}*/
		if(((t4->p.value < 0) && ((df->kind == NOLL_DATA_LE) && (dc->cl != NULL)))){
			e = mk_assist_constr(noll_vector_at(dc->cl->p.targs, 1), df, p, ki);
			if(e != NULL) z3_ast_array_push(t, e);
		}

		if (((t4->p.value >0) && (df->kind == NOLL_DATA_GE) && (dc->cg != NULL))) {
			e = mk_assist_constr(noll_vector_at(dc->cg->p.targs, 1), df, p, ki);
			if(e != NULL) z3_ast_array_push(t, e);
		}

		if((dc->stc != NULL) && (!noll_vector_empty(dc->stc))){
				for(i = 0; i < noll_vector_size(dc->stc); i++){
					df1 = noll_vector_at(dc->stc, i);
					switch(df1->kind){
					case NOLL_DATA_LE:
						if (((t4->p.value < 0) && ((df->kind == NOLL_DATA_LE) ))) {
							e = mk_assist_constr(noll_vector_at(df1->p.targs, 1), df, p, ki);
							if(e != NULL) z3_ast_array_push(t, e);
						}
						break;
					case NOLL_DATA_GE:
						if (((t4->p.value >0)\
								&& (df->kind == NOLL_DATA_GE))) {
							e = mk_assist_constr(noll_vector_at(df1->p.targs, 1), df, p, ki);
							if(e != NULL) z3_ast_array_push(t, e);
						}
						break;
					}
				}
			}
		ret =  Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));

		z3_ast_array_delete(t);
		return ret;
	}
	
	return NULL;
}

Z3_ast sl_abstr::mk_assist_constr(noll_dterm_t *t, noll_ls_t *p,\
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
		c[1] = Z3_mk_int(ctx.z3_ctx, t->p.value, ctx.isort);
		break;
	case NOLL_DATA_VAR:
		c[1] = ctx.var[noll_vector_at(p->args, t->p.sid-1)].node;
		break;
	case NOLL_DATA_PLUS:
		t1 = noll_vector_at(t->args, 0);
		t2 = noll_vector_at(t->args, 1);
		d[0] = ctx.var[noll_vector_at(p->args, t1->p.sid-1)].node;
		d[1] = Z3_mk_int(ctx.z3_ctx, t2->p.value, ctx.isort);
		c[1] = Z3_mk_add(ctx.z3_ctx, 2, d);
		break;
	}
	b = Z3_mk_add(ctx.z3_ctx, 2, c);
	return op_func(ctx.z3_ctx, a, b);
}

Z3_ast sl_abstr::mk_assist_constr(noll_dterm_t *dt, noll_dform_t *df, noll_ls_t *p, int ki)
{
	noll_dterm_t *t1, *t2, *t3, *t4;
	Z3_ast a, b;
	Z3_ast c[2];
	Z3_ast d[2];

	t1 = noll_vector_at(df->p.targs, 0);
	t2 = noll_vector_at(df->p.targs, 1);
	t3 = noll_vector_at(t2->args, 0);
	t4 = noll_vector_at(t2->args, 1);
	a = ctx.var[noll_vector_at(p->args, t1->p.sid-1)].node;
	
	c[0] = k[ki].node;
	c[1] = Z3_mk_int(ctx.z3_ctx, 1, ctx.isort);
	d[0] = Z3_mk_sub(ctx.z3_ctx, 2, c);
	d[1] = Z3_mk_int(ctx.z3_ctx, t4->p.value, ctx.isort);
	c[0] = Z3_mk_mul(ctx.z3_ctx, 2, d);

	switch(df->kind){
	case NOLL_DATA_LE:
		return mk_assist_constr(dt, p, a, c[0], Z3_mk_le);
	case NOLL_DATA_GE:
		return mk_assist_constr(dt, p, a, c[0], Z3_mk_ge);
	}

	return NULL;
}

Z3_ast sl_abstr::mk_sep_constr()
{
	unsigned int i, j, ki, l;
	unsigned int n1, n2, n3;
	unsigned int s1, s2;

	Z3_ast a[2];
	Z3_ast b, c, ret = NULL;
	z3_ast_array *t;


	if (f.sp_atoms.empty()) return NULL;

	n1 = m.size();
	t = z3_ast_array_new();
	for(i = 0; i < n1; i++){
		n2 = m[i].size();
		for(j = 0; j < n2; j++){
			for(ki = 0; ki < n1; ki++){
				n3 = m[ki].size();
				for(l = 0; l < n3; l++){
					if(i != ki){
						s1 = m[i][j].sid;
						s2 = m[ki][l].sid;
						a[0] = Z3_mk_eq(ctx.z3_ctx, ctx.var[s1].node, ctx.var[s2].node);
						a[1] = Z3_mk_eq(ctx.z3_ctx, m[i][j].node, Z3_mk_true(ctx.z3_ctx));
						b = Z3_mk_and(ctx.z3_ctx, 2, a);
						c = Z3_mk_eq(ctx.z3_ctx, m[ki][l].node, Z3_mk_false(ctx.z3_ctx));
						z3_ast_array_push(t, Z3_mk_implies(ctx.z3_ctx, b, c));
					}
				}
			}
		}
	}
	if(!noll_vector_empty(t))
		ret = Z3_mk_and(ctx.z3_ctx, noll_vector_size(t), noll_vector_array(t));
	z3_ast_array_delete(t);

	return ret;
}

