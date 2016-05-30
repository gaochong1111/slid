#include <algorithm>
#include <cassert>

#include "sl_entail.h"
#include "noll_entl.h"
#include "slid_sat.h"
#include "sl_sat.h"

using namespace std;


splitter::splitter(sl_formula& f)
	: startf(f)
{
	s.push(f);
}

bool splitter::get_split_formula(sl_formula& f)
{
	if (offset < vecf.size()) {
		f = vecf[offset];
		return true;
	}
	assert(offset == vecf.size());
	if (s.empty())
		return false;
	split();
	f = vecf[offset++];
	return true;
}

void splitter::set_offset(size_t i)
{
	offset = i;
}

void splitter::split()
{
	assert(!s.empty());

	s.top().mk_graph();
	if (s.top().is_dag_like()) {
		vecf.push_back(s.top());
		s.pop();
		return;
	}
	
	vector<sl_formula> formulas;
	formulas = split(s.top());
	s.pop();
	for (size_t i = 0; i < formulas.size(); ++i) {
		if (formulas[i].check_sat())
			s.push(formulas[i]);
	}
	split();
}
vector<sl_formula> splitter::split(sl_formula& fp)
{
	vector<sl_formula> res;
	vector<Z3_ast> t;
	vector<int> cc_cycle_num(fp.get_cc_cycle_num());
	sl_formula f(startf);
	vector<int> k(cc_cycle_num.size());

	do {
		t.clear();
		t.push_back(fp.get_abstr());
		t.push_back(get_sub_constr(fp, k));
		f.set_abstr(Z3_mk_and(fp.get_z3_context(), t.size(), &(*(begin(t)))));
		res.push_back(f);
	} while (next(k, cc_cycle_num));

	t.clear();
	t.push_back(fp.get_abstr());
	t.push_back(get_sub_constr(fp));
	f.set_abstr(Z3_mk_and(fp.get_z3_context(), t.size(), &(*(begin(t)))));
	res.push_back(f);

	return res;
}
bool splitter::next(vector<int>& k, const vector<int>& num) const
{
	int i;
	for (i = k.size() - 1; i >= 0; --i) {
		if ((num[i] == 0) || (k[i] == (num[i] - 1)))
			continue;
		k[i] += 1;
		for (size_t j = i + 1; j < k.size(); ++j)
			k[j] = 0;
		break;
	}
	if (i < 0)
		return false;
	return true;
}
Z3_ast splitter::get_sub_constr(sl_formula& fp, const vector<int>& k) const
{
	Z3_context z3_ctx = fp.get_z3_context();
	Z3_sort isort = fp.get_z3_sort_int();
	Z3_ast zero, gt, res;
	vector<Z3_ast> t, t2;
	vector<graph::cc_cycle_t>& cycle = fp.get_cc_cycle();
	size_t u, v, m;

	zero = Z3_mk_int(z3_ctx, 0, isort);
	res = Z3_mk_true(z3_ctx);

	for (size_t i = 0; i < cycle.size(); ++i) {
		t.clear();
		for (size_t j = 0; (k[i] < cycle[i].size()) && (j < cycle[i][k[i]].size()); ++j) {
			u = cycle[i][k[i]][j];
			v = (j == cycle[i][k[i]].size()-1 ? cycle[i][k[i]][0] : cycle[i][k[i]][j+1]);
			m = fp.get_edge_property(u, v);
			assert(m >= 0);
			gt = Z3_mk_gt(z3_ctx, fp.get_unfold_times(m), zero);
			t.push_back(gt);
		}
		if (!t.empty())
			t2.push_back(Z3_mk_or(z3_ctx, t.size(), &(*begin(t))));
	}
	if (!t2.empty())
		res = Z3_mk_and(z3_ctx, t2.size(), &(*begin(t2)));
	return res;
}
Z3_ast splitter::get_sub_constr(sl_formula& fp) const
{
	size_t u, v, j, m;
	Z3_context z3_ctx = fp.get_z3_context();
	Z3_sort isort = fp.get_z3_sort_int();
	Z3_ast zero, eq, res;
	vector<Z3_ast> t;
	vector<graph::cc_cycle_t>& cycle = fp.get_cc_cycle();

	res = Z3_mk_true(z3_ctx);

	zero = Z3_mk_int(z3_ctx, 0, isort);
	for (size_t i = 0; i < cycle.size(); ++i) {
		for (size_t j = 0; j < cycle[i].size(); ++j) {
			for (size_t k = 0; k < cycle[i][j].size(); ++k) {
				u = cycle[i][j][k];
				v = k == cycle[i][j].size()-1 ? cycle[i][j][0] : cycle[i][j][k+1];
				m = fp.get_edge_property(u, v);
				assert(m > 0);
				eq = Z3_mk_eq(z3_ctx, fp.get_unfold_times(m), zero);
				t.push_back(eq);
			}
		}
	}
	if (!t.empty())
		res = Z3_mk_and(z3_ctx, t.size(), &(*begin(t)));
	return res;
}
extern noll_pred_array *preds_array;
extern noll_entl_t *noll_prob;

sl_entail::sl_entail()
{
	sl_context ctx;
	ctx.init();
	posf.sl_abstr::init(noll_prob->pform, ctx);
	for (size_t i = 0; i < noll_vector_size(noll_prob->nform); ++i)
		negf.push_back(sl_formula(noll_vector_at(noll_prob->nform, i), ctx));
}

bool sl_entail::check_entail()
{
	splitter sp(posf);

	if (!posf.check_sat())
		return true;

	for (size_t i = 0; i < negf.size(); ++i) {
		if ((negf[i].check_sat())
		&& (check_abstr_entail(posf, negf[i]))){
			if (check_sub_model_entail(sp, negf[i]))
				return true;
		}
	}
	return false;
}

bool sl_entail::check_sub_model_entail(splitter& s, sl_formula& neg)
{
	sl_formula t;
	s.set_offset(0);
	while (s.get_split_formula(t)) {
		if (!check_hom(t, neg))
			return false;
	}
	return true;
}

bool sl_entail::check_abstr_entail(sl_formula& pos, sl_formula& neg)
{
	Z3_ast exists, implies;
	Z3_context z3_ctx = pos.get_z3_context();
	vector<Z3_ast> bound(neg.get_k_m_ast());

	exists = Z3_mk_exists_const(z3_ctx, 0, bound.size(), (Z3_app*)(&(*begin(bound))), 0, NULL, neg.get_abstr());
/*
 *        Z3_sort isort, bsort;
 *        isort = pos.get_z3_sort_int();
 *        bsort = pos.get_z3_sort_bool();
 *        vector<Z3_symbol> ksym(neg.get_z3_symbol_k());
 *        vector<Z3_symbol> msym(neg.get_z3_symbol_m());
 *        vector<Z3_sort> types(neg.get_spatial_atoms().size(), isort);
 *        vector<Z3_symbol> names(begin(ksym), end(ksym));
 *
 *        types.insert(end(types), msym.size(), bsort);
 *        names.insert(end(names), begin(msym), end(msym));
 *
 *        exists = Z3_mk_exists(z3_ctx, 0, 0, NULL, types.size(), &(*begin(types)), &(*begin(names)), neg.get_abstr());
 */
	implies = Z3_mk_implies(z3_ctx, pos.get_abstr(), exists);


	return !(sl_sat::check_sat(z3_ctx, Z3_mk_not(z3_ctx, implies)));

}
bool sl_entail::check_hom(sl_formula& pos, sl_formula& neg,
				map<graph::edge_descriptor, bool>& visited, map<pair<int, int>, bool>& cov)
{
	noll_space_t* spatial_atom;
	vector<noll_space_t*>& spatial_atom_vec = neg.get_spatial_atoms();
	vector<graph::edge_descriptor> path;

	for (size_t i = 0; i < spatial_atom_vec.size(); ++i) {
		spatial_atom = spatial_atom_vec[i];
		path.clear();
		switch (spatial_atom->kind) {
			case NOLL_SPACE_PTO:
				if (!match_pto(pos, path, spatial_atom->m.pto, visited))
					return false;
				break;
			case NOLL_SPACE_LS:
				if (!neg.is_sp_atom_empty(i)) {
					if (!match_pred(pos, path, spatial_atom->m.ls, visited, cov))
						return false;
				}
				break;
		}
		for (size_t j = 0; j < path.size(); ++j)
			visited[path[j]] = true;
	}

	if (!check_coverage(pos, visited, cov))
		return false;

	return true;
}

bool sl_entail::check_hom(sl_formula& pos, sl_formula& neg)
{
	map<graph::edge_descriptor, bool> visited;
	graph::edge_iterator ei, ei_end;
	for (tie(ei, ei_end) = pos.get_edge(); ei != ei_end; ++ei)
		visited[*ei] = false;

	map<pair<int, int>, bool> cov;
	vector<pair<int, int>> coords;
	coords = pos.get_cycle_coords();
	for (size_t i = 0; i < coords.size(); ++i)
		cov[coords[i]] = false;
	
	return check_hom(pos, neg, visited, cov);
}

bool sl_entail::match_pto(sl_formula& pos,
		  	  vector<graph::edge_descriptor>& path,
			  noll_pto_t& pto,
			  map<graph::edge_descriptor, bool>& visited)
{
	size_t sour, dest;

	sour = pto.sid;
	dest = noll_vector_at(pto.dest, 0);
	sour = pos.var_to_ver(sour);
	dest = pos.var_to_ver(dest);
	path = pos.get_path(sour, dest);

	if ((path.empty()) || (path.size() > 1) 
	|| (!check_sep_constr(path, visited))
	|| (!match_pto(pos, path, pto)))
		return false;
	return true;
}
bool sl_entail::match_pred(sl_formula& pos,
		  	  vector<graph::edge_descriptor>& path,
			  noll_ls_t& pred,
			  map<graph::edge_descriptor, bool>& visited,
			  map<pair<int, int>, bool>& cov)
{
	size_t sour, dest;
	pair<int, int> cycle_coord;
	vector<graph::edge_descriptor> path1, path2;

	sour = noll_vector_at(pred.args, 0);
	dest = noll_vector_at(pred.args, slid_get_hole(noll_vector_at(preds_array, pred.pid)));
	sour = pos.var_to_ver(sour);
	dest = pos.var_to_ver(dest);
	path = pos.get_path(sour, dest);

	if (check_sep_constr(path, visited)) {
		cycle_coord = pos.get_cycle_coord(dest);
		if (match_pred(pos, path, &pred)) {
			if (pos.is_cycle(cycle_coord)) {
				path1 = pos.get_path(dest);
				path2 = pos.merge_path(path, path1);
				if (check_sep_constr(path2, visited) && match_pred(pos, path2, &pred))
					cov[cycle_coord] = true;
			}
			return true;
		} else {
			if (pos.is_cycle(cycle_coord)) {
				path1 = pos.get_path(dest);
				path2 = pos.merge_path(path, path1);
				if (check_sep_constr(path2, visited) && match_pred(pos, path2, &pred)) {
					path = path2;
					return true;
				}
			}
		}
	}

	return false;
}

bool sl_entail::check_sep_constr(vector<graph::edge_descriptor>& path,
				map<graph::edge_descriptor, bool>& visited)
{
	for (size_t i = 0; i < path.size(); ++i) {
		if (visited[path[i]] == true)
			return false;
	}
	return true;
}
bool sl_entail::check_coverage(sl_formula& pos, map<graph::edge_descriptor, bool>& visited, map<pair<int, int>, bool>& cov)
{
	for (auto it = begin(visited); it != end(visited); ++it) {
		if (it->second == false) {
			pair<int, int> coord;
			coord = pos.get_cycle_coord(it->first);
			if (!pos.is_cycle(coord))
				return false;
			vector<graph::edge_descriptor> cycle;
			size_t sour = pos.source(it->first);

			cycle = pos.get_path(sour);
			for (size_t i = 0; i < cycle.size(); ++i) {
				if (visited[cycle[i]] == true)
					return false;
				visited[cycle[i]] = true;
			}
			if (cov[coord] == false)
				return false;
		}
	}
	return true;
}

noll_space_t* sl_entail::edge_to_atom(sl_formula& f, graph::edge_descriptor& edge)
{
	return (f.get_spatial_atoms())[f.get_edge_property(edge)];
}
size_t sl_entail::edge_to_atom_id(sl_formula& f, graph::edge_descriptor& edge)
{
	return f.get_edge_property(edge);
}

bool sl_entail::match_pto(sl_formula& pos, vector<graph::edge_descriptor>& path, noll_pto_t& neg_pto)
{
	noll_space_t* spatial_atom;
	size_t u, v;

	spatial_atom = edge_to_atom(pos, path[0]);
	if (spatial_atom->kind  == NOLL_SPACE_PTO) {
		noll_pto_t& pos_pto = spatial_atom->m.pto;
		if (match_pto_field(pos_pto.fields, neg_pto.fields)) {
			for (size_t i = 1; i < noll_vector_size(pos_pto.dest); ++i) {
				u = noll_vector_at(pos_pto.dest, i);
				v = noll_vector_at(neg_pto.dest, i);
				if (!pos.check_eq(u, v))
					return false;
			}
			return true;
		}
	}
	return false;
}

bool sl_entail::match_pto_field(noll_uid_array* f1, noll_uid_array* f2)
{
	if (noll_vector_size(f1) == noll_vector_size(f2)) {
		for (size_t i = 0; i < noll_vector_size(f1); ++i) {
			if (noll_vector_at(f1, i) != noll_vector_at(f2, i))
				return false;
		}
		return true;
	}
	return false;
}

/*
 *bool sl_entail::match_pred(sl_formula& pos, vector<graph::edge_descriptor>& path, noll_ls_t& pred)
 *{
 *        size_t sour_ver, dest_ver;
 *        vector<int> path;
 *        grahp& pos_graph = pos.get_graph();
 *
 *        sour_ver = pos_graph.var_to_vertex(pto.sid);
 *        dest_ver = pos_graph.var_to_vertex(noll_vector_at(pto.dest, 0));
 *
 *        if (pos_graph.is_in_same_cc(sour_ver, dest_ver)) {
 *                path = pos_graph.get_path(sour_ver, dest_ver);
 *                if (!path.empty())
 *                        return match_pred(pos, path, pred);
 *                return false;
 *        }
 *        return false;
 *}
 */

bool sl_entail::match_pred_field(noll_space_t* spatial_atom, noll_ls_t* pred)
{
	noll_pto_t* pto1, *pto2;
	noll_pred_t* def_pred2;
	def_pred2 = noll_vector_at(preds_array, pred->pid);
	pto2 = get_pred_rule_pto(def_pred2);
	switch (spatial_atom->kind) {
		case NOLL_SPACE_PTO:
			pto1 = &(spatial_atom->m.pto);
			break;
		case NOLL_SPACE_LS:
			noll_pred_t* def_pred1;
			def_pred1 = noll_vector_at(preds_array, spatial_atom->m.ls.pid);
			pto1 = get_pred_rule_pto(def_pred1);
			break;
	}
	return match_pto_field(pto1->fields, pto2->fields);
}

bool sl_entail::match_pred(sl_formula& pos, vector<graph::edge_descriptor>& path, noll_ls_t* pred)
{
	vector<int> dest_param, static_param;
	noll_space_t* spatial_atom;
	noll_ls_t* trans_pred;
	Z3_ast unfold_times;
	size_t atom_id;

	dest_param = get_dest_param(pred);
	static_param = get_static_param(pred);

	for (int i = path.size() - 1; i >= 0; --i) {
		spatial_atom = edge_to_atom(pos, path[i]);

		if (!match_pred_field(spatial_atom, pred))
			return false;

		if ((spatial_atom->kind == NOLL_SPACE_LS)
		&& (spatial_atom->m.ls.pid == pred->pid)) {
			dest_param = get_sour_param(&(spatial_atom->m.ls));
		} else {
		
			atom_id = edge_to_atom_id(pos, path[i]);
			unfold_times = pos.get_unfold_times(atom_id);
			trans_pred = transform(pos, unfold_times, spatial_atom,
						pred->pid, dest_param, static_param);

			if (!check_entail(pos, atom_id, trans_pred))
				return false;
			dest_param = get_sour_param(trans_pred);
			noll_uid_array_delete(trans_pred->args);
			delete trans_pred;
		}
	}
	if (!match_sour_param(pos, dest_param, pred))
		return false;

	return true;
}

bool sl_entail::match_sour_param(sl_formula& pos, vector<int>& dest_param, noll_ls_t* neg_pred)
{
	for (size_t i = 0; i < dest_param.size(); ++i) {
		if (!pos.check_eq(dest_param[i], noll_vector_at(neg_pred->args, i+1)))
			return false;
	}
	return true;
}

noll_ls_t* sl_entail::transform(sl_formula& pos, Z3_ast unfold_times, noll_space_t* spatial_atom, size_t pid,
				vector<int>& dest_param, vector<int>& static_param)
{
	noll_ls_t* res;

	vector<int> param;

	param = get_transform_param(pos, unfold_times, spatial_atom, pid, dest_param, static_param);

	res = new noll_ls_t;
	res->pid = pid;
	res->args = noll_uid_array_new();
	for (size_t i = 0; i < param.size(); ++i)
		noll_uid_array_push(res->args, param[i]);

	return res;
}

vector<int> sl_entail::get_transform_param(sl_formula& pos, Z3_ast unfold_times, noll_space_t* spatial_atom, size_t pid,
					   vector<int>& dest_param, vector<int>& static_param)
{
	noll_pto_t* pto;
	noll_ls_t* pred;
	vector<int> param;
	vector<int> sour_param;
	switch (spatial_atom->kind) {
		case NOLL_SPACE_PTO:
			pto = &(spatial_atom->m.pto);
			param.push_back(pto->sid);
			sour_param = mk_sour_param(pos, unfold_times, *pto, pid, dest_param);
			param.insert(end(param), begin(sour_param), end(sour_param));
			param.push_back(noll_vector_at(pto->dest, 0));
			break;
		case NOLL_SPACE_LS:
			pred = &(spatial_atom->m.ls);
			param.push_back(noll_vector_at(pred->args, 0));
			sour_param = mk_sour_param(pos, unfold_times, *pred, pid, dest_param);
			param.insert(end(param), begin(sour_param), end(sour_param));
			param.push_back(noll_vector_at(pred->args, slid_get_hole(noll_vector_at(preds_array, pred->pid))));
			break;
	}
	param.insert(end(param), begin(dest_param), end(dest_param));
	param.insert(end(param), begin(static_param), end(static_param));

	return param;
}

int sl_entail::get_var_loc_in_pto(noll_pto_t* pto, size_t id)
{
	for (size_t i = 0; i < noll_vector_size(pto->dest); ++i) {
		if (noll_vector_at(pto->dest, i) == id)
			return i;
	}
	return -1;
}
vector<int> sl_entail::mk_sour_param(sl_formula& pos, Z3_ast unfold_times,
					noll_pto_t& pos_pto, size_t pid, vector<int>& dest_param)
{
	vector<int> res;
	size_t vid, pparam_bound, nparam_bound;
	noll_pred_t* ndef_pred;
	noll_pto_t* ndpred_pto;
	int c, npto_loc;
	ndef_pred = noll_vector_at(preds_array, pid);
	ndpred_pto = get_pred_rule_pto(ndef_pred);
	nparam_bound = slid_get_hole(ndef_pred);
	for (size_t i = 1; i < nparam_bound; ++i) {
		npto_loc = get_var_loc_in_pto(ndpred_pto, i+1);
		if (npto_loc >= 0) {
			vid = noll_vector_at(pos_pto.dest, npto_loc);
		} else {
			vid = pos.get_var_size();
			mk_new_var(pos, ndef_pred, i+1, unfold_times, dest_param[i-1]);
		}
		res.push_back(vid);
	}
	return res;
}
int get_sour_param_num(noll_pred_t* pred)
{
	return slid_get_hole(pred);
}

vector<int> sl_entail::mk_sour_param(sl_formula& pos, Z3_ast unfold_times,
					noll_ls_t& pos_pred, size_t pid, vector<int>& dest_param)
{
	vector<int> res;
	size_t vid, pparam_bound, nparam_bound;
	noll_pred_t* pdef_pred;
	noll_pred_t* ndef_pred;
	noll_pto_t* pdpred_pto;
	noll_pto_t* ndpred_pto;
	Z3_ast c_ast, c_mul_k, dest_ast, new_var_ast;
	int c, npto_loc;

	pdef_pred = noll_vector_at(preds_array, pos_pred.pid);
	ndef_pred = noll_vector_at(preds_array, pid);
	pdpred_pto = get_pred_rule_pto(pdef_pred);
	ndpred_pto = get_pred_rule_pto(ndef_pred);

	nparam_bound = get_sour_param_num(ndef_pred);
	for (size_t i = 1; i < nparam_bound; ++i) {
		npto_loc = get_var_loc_in_pto(ndpred_pto, i+1);
		if (npto_loc >= 0) {
			vid = noll_vector_at(pos_pred.args, noll_vector_at(pdpred_pto->dest, npto_loc)-1);
		} else {
			vid = pos.get_var_size();
			mk_new_var(pos, ndef_pred, i+1, unfold_times, dest_param[i-1]);
		}
		res.push_back(vid);
	}
	return res;
}
noll_pto_t* sl_entail::get_pred_rule_pto(noll_pred_t* pred)
{
	noll_space_t* sp_atoms;
	sp_atoms = noll_vector_at(pred->def->rec_rules, 0)->pto;
	return get_pred_rule_pto(sp_atoms);
}
noll_pto_t* sl_entail::get_pred_rule_pto(noll_space_t* sp)
{
	switch (sp->kind) {
		case NOLL_SPACE_PTO:
			return &(sp->m.pto);
		case NOLL_SPACE_LS:
			return nullptr;
		case NOLL_SPACE_SSEP:
			for (size_t i = 0; i < noll_vector_size(sp->m.sep); ++i) {
				noll_pto_t* ret = get_pred_rule_pto(noll_vector_at(sp->m.sep, i));
				if (ret != nullptr)
					return ret;
			}
	}
	return nullptr;
}
noll_ls_t* sl_entail::get_pred_rule_pred(noll_pred_t* pred)
{
	noll_space_t* sp_atoms;
	sp_atoms = noll_vector_at(pred->def->rec_rules, 0)->rec;
	return get_pred_rule_pred(sp_atoms);
}
noll_ls_t* sl_entail::get_pred_rule_pred(noll_space_t* sp)
{
	switch (sp->kind) {
		case NOLL_SPACE_PTO:
			return nullptr;
		case NOLL_SPACE_LS:
			return &(sp->m.ls);
		case NOLL_SPACE_SSEP:
			for (size_t i = 0; i < noll_vector_size(sp->m.sep); ++i) {
				noll_ls_t* ret = get_pred_rule_pred(noll_vector_at(sp->m.sep, i));
				if (ret != nullptr)
					return ret;
			}
	}
	return nullptr;
}
void sl_entail::mk_new_var(sl_formula& pos, noll_pred_t* pred, size_t sid, Z3_ast unfold_times, int dest_param)
{
	int c;
	Z3_ast b[2], a[2], new_var_ast;
	sl_var new_var;

	c = get_step_len(pred, sid);
	b[0] = Z3_mk_int(pos.get_z3_context(), c, pos.get_z3_sort_int());
	b[1] = unfold_times;
	a[0] = Z3_mk_mul(pos.get_z3_context(), 2, b);
	a[1] = pos.get_var_ast(dest_param);
	new_var_ast = Z3_mk_add(pos.get_z3_context(), 2, a);
	new_var.node = new_var_ast;
	pos.add_var(new_var);

}
int sl_entail::get_step_len(noll_pred_t* pred, size_t sid)
{
	noll_dform_array* eqs;
	noll_dform_t* eq;
	noll_dterm_t* plus;
	noll_dterm_t* c;
	noll_pred_rule_t* rule;
	rule = noll_vector_at(pred->def->rec_rules, 0);
	eqs = slid_get_pred_data_constr_trans(pred, rule, sid);
	assert(noll_vector_size(eqs) == 1);
	eq = noll_vector_at(eqs, 0);
	assert(eq->kind == NOLL_DATA_EQ);
	plus = noll_vector_at(eq->p.targs, 1);
	assert(plus->kind == NOLL_DATA_PLUS);
	c = noll_vector_at(plus->args, 1);
	assert(c->kind == NOLL_DATA_INT);
	return c->p.value;
}
vector<int> sl_entail::get_sour_param(noll_ls_t* pred)
{
	int dir_num;
	vector<int> res;
	noll_pred_t* def_pred;
	def_pred = noll_vector_at(preds_array, pred->pid);
	dir_num = slid_get_hole(def_pred);
	res.insert(end(res), 
		   noll_vector_array(pred->args)+1,
		   noll_vector_array(pred->args)+dir_num);
	return res;
}
vector<int> sl_entail::get_dest_param(noll_ls_t* pred)
{
	int dir_num;
	vector<int> res;
	noll_pred_t* def_pred;
	def_pred = noll_vector_at(preds_array, pred->pid);
	dir_num = slid_get_hole(def_pred);
	res.insert(end(res),
		   noll_vector_array(pred->args)+dir_num+1,
		   noll_vector_array(pred->args)+dir_num*2);
	return res;
}
vector<int> sl_entail::get_static_param(noll_ls_t* pred)
{
	int dir_num;
	vector<int> res;
	noll_pred_t* def_pred;
	def_pred = noll_vector_at(preds_array, pred->pid);
	dir_num = slid_get_hole(def_pred);
	res.insert(end(res),
		   noll_vector_array(pred->args)+dir_num*2,
		   noll_vector_array(pred->args)+noll_vector_size(pred->args));
	return res;
}

/*
 *shared_ptr<noll_ls_t> sl_entail::transform_pto(sl_formula& pos, vector<int>& new_vars,
 *                                                noll_pto_t* pos_pto,
 *                                                     noll_ls_t* neg_pred,
 *                                                     vector<int>& dest_para, vector<int>& static_para)
 *{
 *        [>positive and negative predicate direction number<]
 *        size_t pdir_num, ndir_num;
 *        noll_pred_t* ndef_pred;
 *        noll_pto_t* ndpred_pto;
 *        Z3_ast c_ast, k_ast, c_mul_k, dest_ast, new_var;
 *        int c, npto_loc;
 *        sl_abstr& abs = pos.abs;
 *        sl_context& ctx = abs.ctx;
 *        ndef_pred = noll_vector_at(preds_array, neg_pred->pid);
 *        ndir_num = ndef_pred->typ->nDir;
 *        ndpred_pto = get_pred_rule_pto(ndef_pred);
 *        shared_ptr<noll_ls_t> res = make_shared<noll_ls_t>();
 *        res->pid = neg_pred->pid;
 *        res->args = noll_uid_array_new();
 *        for (size_t i = 0; i < noll_vector_size(neg->pred->args); ++i) {
 *                if (i == 0) {
 *                        noll_uid_array_push(res->args, pos_pto->sid);
 *                } else if (i < ndir_num) {
 *                        npto_loc = get_var_loc_in_pto(ndpred_pto, i+1);
 *                        if (npto_loc >= 0) {
 *                                if (noll_vector_at(pos_pto->field, npto_loc)
 *                                != noll_vector_at(ndpred_pto->field, npto_loc))
 *                                        return nullptr;
 *                                vid = noll_vector_at(pos_pto->dest, npto_loc);
 *                                noll_uid_array_push(res->args, vid);
 *                        } else {
 *                                vid = var_num + new_vars.size();
 *                                c = get_step_len(ndef_pred);
 *                                c_ast = Z3_mk_int(ctx.z3_ctx, c, ctx.isort);
 *                                k_ast = Z3_mk_int(ctx.z3_ctx, 1, ctx.isort);
 *                                c_mul_k = Z3_mk_mul(ctx.z3_ctx, c_ast, k_ast);
 *                                dest_ast = ctx.var[dest_para[i-1]]->node;
 *                                new_var = Z3_mk_sub(ctx.z3_ctx, dest_ast, c_mul_k);
 *                                new_vars.push_back(new_var);
 *                                noll_uid_array_push(res->args, vid);
 *                        }
 *                } else if (i == ndir_num) {
 *                        noll_uid_array_push(res->args, noll_vector_at(pos_pto->dest, 0));
 *                } else if (i < 2*ndir_num) {
 *                        noll_uid_array_push(res->args, dest_para[i-ndir_num-1]);
 *                } else {
 *                        noll_uid_array_push(res->args, static_para[i-2*ndir_num]);
 *                }
 *        }
 *
 *        return res;
 *}
 *
 *shared_ptr<noll_ls_t> sl_entail::transform_pred(sl_formula& pos, size_t k, vector<int>& new_vars,
 *                                                noll_ls_t* pos_pred,
 *                                                     noll_ls_t* neg_pred,
 *                                                     vector<int>& dest_para, vector<int>& static_para)
 *{
 *        [>positive and negative predicate direction number<]
 *        size_t pdir_num, ndir_num;
 *        noll_pred_t* pdef_pred, *ndef_pred;
 *        noll_pto_t* pdpred_pto, * ndpred_pto;
 *        Z3_ast c_ast, k_ast, c_mul_k, dest_ast, new_var;
 *        int c, npto_loc;
 *        sl_abstr& abs = pos.abs;
 *        sl_context& ctx = abs.ctx;
 *        pdef_pred = noll_vector_at(preds_array, pos_pred->pid);
 *        ndef_pred = noll_vector_at(preds_array, neg_pred->pid);
 *        pdir_num = pdef_pred->typ->nDir;
 *        ndir_num = ndef_pred->typ->nDir;
 *        pdpred_pto = get_pred_rule_pto(pdef_pred);
 *        ndpred_pto = get_pred_rule_pto(ndef_pred);
 *        shared_ptr<noll_ls_t> res = make_shared<noll_ls_t>();
 *        res->pid = neg_pred->pid;
 *        res->args = noll_uid_array_new();
 *        for (size_t i = 0; i < noll_vector_size(neg->pred->args); ++i) {
 *                if (i == 0) {
 *                        noll_uid_array_push(res->args, noll_vector_at(pos_pred->args, 0));
 *                } else if (i < ndir_num) {
 *                        npto_loc = get_var_loc_in_pto(ndpred_pto, i+1);
 *                        if (npto_loc >= 0) {
 *                                if (noll_vector_at(pdpred_pto->field, npto_loc)
 *                                != noll_vector_at(ndpred_pto->field, npto_loc))
 *                                        return nullptr;
 *                                vid = noll_vector_at(pos_pred->args, noll_vector_at(pdpred_pto->dest, npto_loc)-1);
 *                                noll_uid_array_push(res->args, vid);
 *                        } else {
 *                                vid = var_num + new_vars.size();
 *                                c = get_step_len(ndef_pred);
 *                                c_ast = Z3_mk_int(ctx.z3_ctx, c, ctx.isort);
 *                                k_ast = abs.k[k]->node;
 *                                c_mul_k = Z3_mk_mul(ctx.z3_ctx, c_ast, k_ast);
 *                                dest_ast = ctx.var[dest_para[i-1]]->node;
 *                                new_var = Z3_mk_sub(ctx.z3_ctx, dest_ast, c_mul_k);
 *                                new_vars.push_back(new_var);
 *                                noll_uid_array_push(res->args, vid);
 *                        }
 *                } else if (i == ndir_num) {
 *                        noll_uid_array_push(res->args, noll_vector_at(pos_pred->args, pdir_num));
 *                } else if (i < 2*ndir_num) {
 *                        noll_uid_array_push(res->args, dest_para[i-ndir_num-1]);
 *                } else {
 *                        noll_uid_array_push(res->args, static_para[i-2*ndir_num]);
 *                }
 *        }
 *
 *        return res;
 *}
 *
 */

bool sl_entail::check_abstr_entail(sl_formula& pos, noll_ls_t* pred, size_t k)
{
	Z3_ast imply, not_imply;
	imply = Z3_mk_implies(pos.get_z3_context(), pos.get_abstr(), pos.mk_abstr(pred, k));
	not_imply = Z3_mk_not(pos.get_z3_context(), imply);
	if (!sl_sat::check_sat(pos.get_z3_context(), not_imply))
		return true;
	return false;
}

noll_pred_t* sl_entail::get_pred_def(size_t id)
{
	return noll_vector_at(preds_array, id);
}
bool sl_entail::match_heap(sl_formula& pos,
			   noll_space_t* sp_atom,
			   noll_ls_t* neg_pred)
{
	map<int, int> m;
	switch (sp_atom->kind) {
		case NOLL_SPACE_PTO:
			return match_heap(pos, m, &(sp_atom->m.pto), neg_pred);
		case NOLL_SPACE_LS:
			return match_heap(pos, m, &(sp_atom->m.ls), neg_pred);
	}
}

bool sl_entail::match_heap(sl_formula& pos,
			   map<int, int>& m,
			   noll_pto_t* pos_pto,
			   noll_ls_t* neg_pred)
{
	int vid1, vid2;
	noll_pto_t* neg_pto;
	neg_pto = get_pred_rule_pto(get_pred_def(neg_pred->pid));

	int field_num = noll_vector_size(neg_pto->dest);
	int npara_num = noll_vector_size(neg_pred->args);

	for (size_t i = 0; i < field_num; ++i) {
		vid2 = noll_vector_at(neg_pto->dest, i);
		vid1 = noll_vector_at(pos_pto->dest, i);
		if (vid2 <= npara_num) {
			vid2 = noll_vector_at(neg_pred->args, vid2-1);
			if (!pos.check_eq(vid1, vid2))
				return false;
		} else {
			auto ret = m.insert(make_pair(vid2, vid1));
			if (!ret.second && (vid1 != m[vid2])) {
				if (!pos.check_eq(vid1, m[vid2]))
					return false;
			}
		}
	}
	return true;
}
size_t sl_entail::get_field_num(noll_pto_t* pto)
{
	return noll_vector_size(pto->dest);
}
size_t sl_entail::get_param_num(noll_ls_t* pred)
{
	return noll_vector_size(pred->args);
}
bool sl_entail::match_heap(sl_formula& pos,
			   map<int, int>& m,
			   noll_ls_t* pos_pred,
			   noll_ls_t* neg_pred)
{
	int vid1, vid2;

	noll_pto_t* pos_pto, *neg_pto;
	pos_pto = get_pred_rule_pto(get_pred_def(pos_pred->pid));
	neg_pto = get_pred_rule_pto(get_pred_def(neg_pred->pid));

	int field_num = get_field_num(neg_pto);
	int ppara_num = get_param_num(pos_pred);
	int npara_num = get_param_num(neg_pred);

	for (size_t i = 0; i < field_num; ++i) {
		vid2 = noll_vector_at(neg_pto->dest, i);
		vid1 = noll_vector_at(pos_pto->dest, i);
		if (vid2 <= npara_num) {
			if (vid1 > ppara_num)
				return false;
			vid2 = noll_vector_at(neg_pred->args, vid2-1);
			vid1 = noll_vector_at(pos_pred->args, vid1-1);
			if (!pos.check_eq(vid1, vid2))
				return false;
		} else {
			auto ret = m.insert(make_pair(vid2, vid1));
			if (!ret.second && (vid1 != m[vid2])) {
				if ((vid1 > ppara_num) || (m[vid2] > ppara_num))
					return false;
				vid2 = noll_vector_at(neg_pred->args, vid2-1);
				vid1 = noll_vector_at(pos_pred->args, vid1-1);
				if (!pos.check_eq(vid1, m[vid2]))
					return false;
			}
		}
	}
	return true;
}

/*
 *map<int, int> sl_entail::mk_var_map(noll_ls_t*pos_pred, noll_ls_t* neg_pred)
 *{
 *        map<int, int> m;
 *        int vid1, vid2;
 *        noll_pto_t* pos_pto, *neg_pto;
 *        pos_pto = get_pred_rule_pto(get_pred_def(pos_pred->pid));
 *        neg_pto = get_pred_rule_pto(get_pred_def(neg_pred->pid));
 *        int field_num = get_field_num(neg_pto);
 *        int npara_num = get_param_num(neg_pred);
 *
 *        vid1 = noll_vector_at(pos_pred->args, pos_pto->sid-1);
 *        vid2 = noll_vector_at(neg_pred->args, neg_pto->sid-1);
 *        m[vid2] = vid1;
 *        for (size_t i = 0; i < field_num; ++i) {
 *                vid1 = noll_vector_at(pos_pto->dest, i);
 *                vid1 = noll_vector_at(pos_pred->args, vid1-1);
 *                vid2 = noll_vector_at(neg_pto->dest, i);
 *                if (vid2 > npara_num) {
 *                        vid2 = noll_vector_at(neg_pred->args, vid2-1);
 *                        m[vid2] = vid1;
 *                }
 *        }
 *        
 *        return m;
 *}
 */

bool sl_entail::match_heap_deep(sl_formula& pos, map<int, int>& m, noll_ls_t* pos_pred, noll_ls_t* neg_pred)
{
	int vid1, vid2, u, v;
	map<int, int> m1;

	noll_pto_t* pos_pto, *neg_pto;
	noll_ls_t* dpos_pred, *dneg_pred;
	pos_pto = get_pred_rule_pto(get_pred_def(pos_pred->pid));
	neg_pto = get_pred_rule_pto(get_pred_def(neg_pred->pid));
	dpos_pred = get_pred_rule_pred(get_pred_def(pos_pred->pid));
	dneg_pred = get_pred_rule_pred(get_pred_def(neg_pred->pid));
	
	int field_num = get_field_num(neg_pto);
	int ppara_num = get_param_num(pos_pred);
	int npara_num = get_param_num(neg_pred);

	vid1 = noll_vector_at(dpos_pred->args, pos_pto->sid-1);
	vid2 = noll_vector_at(dneg_pred->args, neg_pto->sid-1);
	if (vid1 != m[vid2])
		return false;
	for (size_t i = 0; i < field_num; ++i) {
		vid2 = noll_vector_at(neg_pto->dest, i);
		vid1 = noll_vector_at(pos_pto->dest, i);
		if (vid2 <= npara_num) {
			if (vid1 > ppara_num)
				return false;
			vid2 = noll_vector_at(dneg_pred->args, vid2-1);
			vid1 = noll_vector_at(dpos_pred->args, vid1-1);

			if (vid2 <= npara_num) {
				u = noll_vector_at(pos_pred->args, vid1-1);
				v = noll_vector_at(neg_pred->args, vid2-1);
				if (!((vid2 == 1 && vid1 == 1) || (pos.is_static_param(get_pred_def(pos_pred->pid), vid1) &&
								   pos.is_static_param(get_pred_def(neg_pred->pid), vid2) &&
								   pos.check_eq(u, v))))
					return false;
			} else {
				auto ret1 = m.insert(make_pair(vid2, vid1));
				if ((!ret1.second)  && (vid1 != m[vid2]))
						return false;
			}
		} else {
			auto ret2 = m1.insert(make_pair(vid2, vid1));
			if (!ret2.second && (vid1 != m1[vid2]))
				return false;
		}
	}
	return true;
}

bool sl_entail::match_heap_deep(sl_formula& pos,
				noll_ls_t* pos_pred,
				noll_ls_t* neg_pred)
{
	map<int, int> m;
	if (match_heap(pos, m, pos_pred, neg_pred)) {
		if (match_heap_deep(pos, m, pos_pred, neg_pred))
			return true;
	}
	return false;
}

bool sl_entail::check_entail(sl_formula& pos, size_t k, noll_ls_t* neg)
{
	if (check_abstr_entail(pos, neg, k)) {
		noll_space_t* sp_atom = pos.get_spatial_atoms()[k];
		if (pos.check_sat_unfold_once(k)) {
			if (!match_heap(pos, sp_atom, neg))
				return false;
		}
		if (pos.check_sat_unfold_twice(k)) {
			if (!match_heap_deep(pos, &(sp_atom->m.ls), neg))
				return false;
		}
		return true;
	}
	return false;
}
