#ifndef SL_ABSTR_H
#define SL_ABSTR_H

#include <vector>
#include <z3.h>

#include "sl_for.h"
#include "sl_var.h"
#include "sl_context.h"
#include "noll_form.h"
#include "slid_sat.h"


class sl_abstr {
public:
	sl_abstr(): abstr(nullptr) {}

	sl_abstr(const sl_abstr&);
	sl_abstr& operator=(const sl_abstr&);

	sl_abstr(sl_abstr&&) noexcept;
	sl_abstr& operator=(sl_abstr&&) noexcept;

	sl_abstr(noll_form_t*, sl_context&);

	//void init(sl_for&, sl_context&);

	void mk_abstr();
	Z3_ast mk_abstr(noll_ls_t*, size_t);

	std::vector<noll_space_t*>& get_spatial_atoms();
	bool is_sp_atom_empty(size_t);
	Z3_ast get_unfold_times(size_t);

	sl_context& get_context();

	Z3_ast get_abstr();
	void set_abstr(Z3_ast);

	std::vector<Z3_ast> get_k_m_ast();
	/*
	 *std::vector<Z3_symbol> get_z3_symbol_k();
	 *std::vector<Z3_symbol> get_z3_symbol_m();
	 */

        bool check_eq(size_t, size_t);


	//Z3_ast mk_abstr(sl_context&, noll_ls_t*);

	void init(noll_form_t*, sl_context&);
	Z3_context get_z3_context();
	Z3_sort get_z3_sort_int();
	Z3_sort get_z3_sort_bool();
	Z3_ast get_var_ast(size_t);
	size_t get_var_size();
	void add_var(sl_var&);
	bool check_sat_unfold_once(size_t);
	bool check_sat_unfold_twice(size_t);
	bool check_sat();
/*
 *        Z3_ast get_unfold_times(size_t);
 *        bool check_unfold_once(size_t);
 *        bool check_unfold_once(noll_space_t*);
 *        sl_context& get_context();
 *
 *        bool check_unfold_twice(size_t);
 *        bool check_unfold_twice(noll_space_t*);
 *        Z3_ast get_abstr();
 *        
 *        bool check_eq(sl_context&, size_t, size_t);
 */
	Z3_ast mk_pred(noll_ls_t*, int);
private:
	void init_kvar(sl_for&);
	void init_bvar(sl_for&);

	std::vector<sl_var> mk_pto_bvar(size_t, size_t);
	std::vector<sl_var> mk_ls_bvar(noll_ls_t*, size_t);
	sl_var mk_bvar(size_t, size_t);
	std::vector<int> get_in_alloc_loc_index(noll_ls_t*);

	void mk_pure_abstr(noll_pure_t*);
	Z3_ast mk_pure_data_constr(noll_dform_t*);
	Z3_ast mk_pure_data_constr1(noll_dterm_array*, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));
	Z3_ast mk_pure_data_constr2(noll_dterm_array*, Z3_ast (*)(Z3_context, unsigned int, Z3_ast const[]));
	Z3_ast mk_ite(noll_dterm_t*);
	Z3_ast mk_implies(noll_dform_array*);
	Z3_ast mk_term(noll_dterm_t*);

	std::vector<int> get_trans_loc(noll_ls_t*);

	void mk_space_abstr();
	Z3_ast mk_pto(noll_pto_t*, int);
	Z3_ast mk_unfold(noll_ls_t*, int);
	Z3_ast mk_fir_unfold(noll_ls_t*, int, std::vector<int>&);
	Z3_ast mk_sec_unfold(noll_ls_t*, int, std::vector<int>&);
	Z3_ast mk_closures(noll_ls_t*, int);
	Z3_ast mk_closure(slid_data_constr*, noll_ls_t*, int);
	Z3_ast mk_pred_data_constr_cst(slid_data_constr*, noll_ls_t*);
	Z3_ast mk_pred_data_constr_cst(noll_dform_t*, noll_ls_t*);
	Z3_ast mk_pred_data_constr_stc(slid_data_constr*, noll_ls_t*);
	Z3_ast mk_pred_data_constr_stc(noll_dform_t*, noll_ls_t*, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));
	Z3_ast mk_pred_data_constr_trans(slid_data_constr*, noll_ls_t*, int);
	Z3_ast mk_pred_data_constr_trans(slid_data_constr*, noll_dform_t*, noll_ls_t*,
					int, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));
	Z3_ast mk_assist_constr(noll_dterm_t*, noll_ls_t*, Z3_ast, Z3_ast, Z3_ast (*)(Z3_context, Z3_ast, Z3_ast));
	Z3_ast mk_assist_constr(noll_dterm_t*, noll_dform_t*, noll_ls_t*, int);
	
	Z3_ast mk_sep_constr();


	sl_for f;
	sl_context ctx;
	std::vector<sl_var> k;
	std::vector<std::vector<sl_var>> m;
	Z3_ast abstr;

	static int _counter;
};

#endif // sl_abstr.h

