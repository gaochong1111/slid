#ifndef SL_ENTAIL_H
#define SL_ENTAIL_H

#include <set>
#include <stack>
#include <vector>
#include <utility>

#include "sl_abstr.h"
#include "sl_formula.h"
#include "noll_form.h"
#include "graph.h"

#include <z3.h>


class splitter {
public:
	splitter(sl_formula&);
	bool get_split_formula(sl_formula&);
	void set_offset(size_t);
private:
	void split();
	std::vector<sl_formula> split(sl_formula&);

	Z3_ast get_sub_constr(sl_formula&, const std::vector<int>&) const;
	Z3_ast get_sub_constr(sl_formula&) const;
	bool next(std::vector<int>&, const std::vector<int>&) const;

	std::stack<sl_formula> s;
	std::vector<sl_formula> vecf;
	size_t offset = 0;
};

class sl_entail {
public:
	/*
	 *enum sl_entail_t {
	 *        SL_ENTAIL_UNSAT = -1,
	 *        SL_ENTAIL_UNKNOWN,
	 *        SL_ENTAIL_SAT
	 *};
	 */
	sl_entail();
	bool check_entail();

private:
	bool check_sub_model_entail(splitter&, sl_formula&);

	bool check_abstr_entail(sl_formula&, sl_formula&);

	bool check_hom(sl_formula&, sl_formula&);
	bool check_hom(sl_formula&, sl_formula&, std::map<graph::edge_descriptor, bool>&, std::map<std::pair<int, int>, bool>&);

	bool match_pto(sl_formula&, std::vector<graph::edge_descriptor>& path, noll_pto_t&,
			std::map<graph::edge_descriptor, bool>& visited);
	bool match_pred(sl_formula&, std::vector<graph::edge_descriptor>& path, noll_ls_t&,
			std::map<graph::edge_descriptor, bool>& visited, std::map<std::pair<int, int>, bool>&);
	bool check_sep_constr(std::vector<graph::edge_descriptor>&, std::map<graph::edge_descriptor, bool>& visited);
	bool check_coverage(sl_formula&, std::map<graph::edge_descriptor, bool>&, std::map<std::pair<int, int>, bool>&);
	noll_space_t* edge_to_atom(sl_formula&, graph::edge_descriptor&);
	size_t edge_to_atom_id(sl_formula&, graph::edge_descriptor&);
	bool match_pto(sl_formula&, std::vector<graph::edge_descriptor>&, noll_pto_t&);
	bool match_pto_field(noll_uid_array*, noll_uid_array*);
	bool match_pred_field(noll_space_t*, noll_ls_t*);
	bool match_pred(sl_formula&, std::vector<graph::edge_descriptor>&, noll_ls_t*);
	noll_ls_t* transform(sl_formula&, Z3_ast, noll_space_t*, size_t, std::vector<int>&, std::vector<int>&);
	std::vector<int> get_transform_param(sl_formula&, Z3_ast, noll_space_t*, size_t, std::vector<int>&, std::vector<int>&);
	int get_var_loc_in_pto(noll_pto_t*, size_t);
	std::vector<int> mk_sour_param(sl_formula&, Z3_ast, noll_pto_t&, size_t, std::vector<int>&);
	std::vector<int> mk_sour_param(sl_formula&, Z3_ast, noll_ls_t&, size_t, std::vector<int>&);
	noll_pto_t* get_pred_rule_pto(noll_pred_t*);
	noll_ls_t* get_pred_rule_pred(noll_pred_t*);
	noll_pto_t* get_pred_rule_pto(noll_space_t*);
	noll_ls_t* get_pred_rule_pred(noll_space_t*);
	void mk_new_var(sl_formula&, noll_pred_t*, size_t, Z3_ast, int);
	int get_step_len(noll_pred_t*, size_t);
	std::vector<int> get_sour_param(noll_ls_t*);
	std::vector<int> get_dest_param(noll_ls_t*);
	std::vector<int> get_static_param(noll_ls_t*);
	bool check_abstr_entail(sl_formula&, noll_ls_t*, size_t);
	noll_pred_t* get_pred_def(size_t);
	size_t get_field_num(noll_pto_t*);
	size_t get_param_num(noll_ls_t*);
	bool match_heap(sl_formula&, noll_space_t*, noll_ls_t*);
	bool match_heap(sl_formula&, std::map<int, int>&, noll_pto_t*, noll_ls_t*);
	bool match_heap(sl_formula&, std::map<int, int>&, noll_ls_t*, noll_ls_t*);

	//std::map<int, int> mk_var_map(noll_ls_t*, noll_ls_t*);
	//bool check_var_map(sl_formula&, std::map<int, int>&, noll_ls_t*, noll_ls_t*);
	bool match_heap_deep(sl_formula&, noll_ls_t*, noll_ls_t*);
	bool match_heap_deep(sl_formula&, std::map<int, int>&, noll_ls_t*, noll_ls_t*);
	bool check_entail(sl_formula&, size_t, noll_ls_t*);
	bool match_sour_param(sl_formula&, std::vector<int>&, noll_ls_t*);


	sl_formula posf;
	std::vector<sl_formula> negf;
};

#endif // sl_entail.h
