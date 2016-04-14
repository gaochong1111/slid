#include <iostream>
#include <memory>
#include <set>
#include <vector>

#include <boost/config.hpp>
#include <boost/graph/adjacency_list.hpp>

#include "sl_entail.h"
#include "noll_form.h"
#include "noll_preds.h"
#include "noll_entl.h"


using namespace std;

extern noll_pred_t *noll_prob;

sl_entail::sl_entail(): kind(SL_ENTAIL_UNKOWN)
{
	size_t i;
	Z3_config cfg;
	noll_var_t* v;
	Z3_ast t;
	noll_form_t* neg_formula_ptr;
	shared_ptr<sl_formula> neg_formula_sptr;

	cfg = Z3_mk_config();
	z3_ctx = Z3_mk_context(cfg);
	Z3_del_config(cfg);

	isort = Z3_mk_int_sort(z3_ctx);
	bsort = Z3_mk_bool_sort(z3_ctx);

	for (i = 0; i < noll_vector_size(form->lvars); ++i){
		v = noll_vector_at(form->lvars, i);
		t = Z3_mk_const(z3_ctx, Z3_mk_string_symbol(z3_ctx, v->vname), int_sort);
		var.push_back(t);
	}

	pos_formula = make_shared<sl_formula>(noll_prob->pform, z3_ctx, isort, bsort, var);
	for (i = 0; i < noll_vector_size(noll_prob->nform); ++i) {
		neg_formula_ptr = noll_vector_at(noll_prob->nform, i);
		neg_formula_sptr = make_shared<sl_formula>(neg_formula_ptr, z3_ctx, isort, bsort, var);
		neg_forula.push_back(neg_formula_sptr);
	}
}

void sl_entail::check_entail()
{
}

bool sl_entail::check_entail(shared_ptr<sl_formula>& neg_formula)
{
	if (!pos_formula->issat()) {
		kind = SL_ENTAIL_SAT;
		return true;
	}
	if(!neg_formula->issat()) {
		kind = SL_ENTAIL_UNSAT;
		return false;
	}
	build_graph();
	return check_hom();
}

bool sl_entail::check_entail()
{
	get_heap_map(pos_formula->abstr);
}
map<Z3_ast, Graph> sl_entail::get_heap_map(Z3_ast abstr)
{
	map<Z3_ast, Graph> res, t;
	vector<set<int>> cc;
	vector<set<vector<int>>> cycle;
	vector<Z3_ast> abstrs;
	shared_ptr<Graph> g = make_graph(abstr);
	cc = get_connected_component(*g);
	cycle = get_cycle(*g, cc);
	if (is_dag_like(*g, cc, cycle)) {
		res[abstr] = *g;
		return res;
	}
	abstrs = disassemble(abstr, g, cycle);	
	for (size_t i = 0; i < abstrs.size(); ++i) {
		t = get_heap_map(abstrs[i]);
		res.insert(begin(t), end(t));
	}
	return res;
}
vector<set<int>> sl_entail::get_connected_component(Graph& g)
{
	size_t i, k, l;
	Graph::out_edge_iterator out_it1, out_it2;
	Graph::in_edge_iterator in_it1, in_it2;
	vector<set<int>> res;
	set<int> t;
	size_t num = boost::num_vertics(g);
	vector<int> visited(num);
	for (i = 0; i < visited.size(); ++i)
		visited[i] = 0;

	for (i = 0; i < num; ++i) {
		if (visited[i])
			continue;
		q.push(i);
		while (!q.empty()) {
			k = q.front();
			visited[k] = 1;
			t.insert(k);
			tie(out_it1, out_it2) = boost::out_edges(k, g);
			for (; out_it1 != out_it2; ++out_it1) {
				l = boost::target(*out_it1, g);
				if (!visited[l])
					q.push(l);
			}
			tie(in_it1, in_it2) = boost::out_edges(k, g);
			for (; in_it1 != in_it2; ++in_it1) {
				l = boost::target(*in_it1, g);
				if (!visited[l])
					q.push(l);
			}
			q.pop();
		}
		res.push_back(t);
	}
	return res;
}
vector<set<vector<int>>> sl_entail::get_cycle(Graph& g, vector<set<int>>& cc)
{
	size_t i, j;
	vector<set<vector<int>>> res;
	set<vector<int>> t;
	vector<int> c, visited, s;
	for (i = 0; i < cc.size(); ++i) {
		c.assign(begin(cc[i]), end(cc[i]));
		visited.resize(cc[i].size());
		for (j = 0; j < visited.size(); ++j)
			visited[j] = 0;
		s.clear();
		for (j = 0; j < visited.size(); ++j) {
			if (visited[j])
				continue;
			s.push_back(c[j]);
			dfs(g, j, c, s, visited, t);
			s.pop_back();
		}
		res.push_back(t);
	}
}
void sl_entail::dfs(Graph& g, int v, vector<int>& c, vector<int>& s, vector<int> visited, set<vector<int>>& r)
{
	Graph::out_edge_iterator it1, it2;
	visited[v] = 1;
	if (i = locate(s) != -1)
		r.insert(vector<int>(begin(s)+i, end(s)-1));	
	tie(it1, it2) = boost::out_edges(c[v], g);
	for (; it1 != it2; ++it1) {
		t = boost::target(*it1, g);
		if(!visited[find(c, t)]) {
			s.push_back(t);
			dfs(g, t, c, s, visited, r);
			s.pop_back();
		}
	}
}
int sl_entail::locate(vector<int>& vec)
{
	int k = vec[end(vec)-1];
	for (size_t i = vec.size()-2; i >= 0; --i) {
		if (k == vec[i])
			return i;
	}
	return -1;
}
int sl_entail::find(vector<int>& vec, int k)
{
	for (size_t i = 0; i < vec.size(); ++i) {
		if (vec[i] == k)
			return i;
	}
	return -1;
}
bool sl_entail::is_dag_like(Graph& g, vector<set<vector<int>>>& c)
{
	int u, v;
	set<vector<int>> cycle, t;
	Graph::out_edge_iterator it1, it2;
	for (size_t i = 0; i < c.size(); ++i) {
		t = c[i];
		for (auto it = begin(t); it != end(t); ++it)
			cycle.insert(*it);
	}
	for (auto it = begin(cycle); it != end(cycle); ++it) {
		for (size_t i = 0; i < it->size(); ++i) {
			u = (*it)[i];
			v = (i == it->size()-1) ? (*it)[0] : (*it)[i+1];
			tie(it1, it2) = boost::out_edges(u, g);
			if ((boost::out_degree(u, g) == 1) || (boost::target(*it1, g) != v))
				return false;
		}
	}
	return true;
}


shared_ptr<Graph> sl_entail::make_graph()
{
	return make_graph(pos_formula->abstr);
}
shared_ptr<Graph> sl_entail::make_graph(Z3_ast abstr)
{
	shared_ptr<Graph> res = make_shared<Graph>();

	add_vertex(abstr, *res);
	add_edge(abstr, *res);

	return res;
}

vector<set<int>> sl_entail::get_equivalence_class(Z3_ast abstr)
{
	size_t i, j, k;
	size_t lvar_num = noll_prob->pform->pure->size;
	Z3_ast eq, neq;
	deque<int> q;
	vector<set<int>> res;
	set<int> t;
	vector<int> visited(lvar_num);

	for (i = 0; i < visited.size(); ++i)
		visited[i] = 0;

	for (i = 0; i < lvar_num; ++i) {
		if (visited[i])
			continue;
		q.push(i);
		while (!q.empty()) {
			k = q.front();
			visited[k] = 1;
			t.insert(k);
			for (j = 1; j < pure->size-k; ++j) {
				eq = Z3_mk_eq(z3_ctx, var[k], var[k+j]);
				neq = Z3_mk_and(z3_ctx, abstr, Z3_mk_not(z3_ctx, eq));
				if ((pos_formula->check_sat(neq) == sl_formula::SL_SAT_UNSAT)
				&& (visited[k+j] == 0))
					q.push(k+j);
			}
			q.pop();
		}
		res.push_back(t);
	}
	return res;
}

void sl_entail::add_vertex(Z3_ast abstr, Graph& g)
{
	set<int> eq_class;
	vector<set<int>> eq_class_set;
	eq_class_set = get_equivalence_class(abstr);
	for (size_t i = 0; i < eq_class_set->size(); ++i) {
		eq_class = eq_class_set[i];	
		boost::add_vertex(g);
		g[i].insert(begin(*eq_class), end(*eq_class));
		for (auto it = begin(*eq_class);
		it != end(*eq_class); ++it)
			g[boost::graph_bundle][*it] = i;
	}
}

void sl_entail::add_edge(Z3_ast abstr, Graph& g)
{
	Z3_ast zero, t, f;
	noll_space_t* space;
	size_t source, target;
	for (size_t i = 0; i < pos_formula.space.size(); ++i) {
		space = pos_formula.space[i];
		switch (space->kind) {
			case NOLL_SPACE_PTO:
				noll_pto_t& pto;
				pto = space->m.pto;
				source = g[boost::graph_bundle][pto.sid];
				target = g[boost::graph_bundle][noll_vector_at(pto.dest, 0)];
				boost::add_edge(source, target, space, g);
				break;
			case NOLL_SPACE_LS:
				zero = Z3_mk_int(z3_ctx, 0);
				t = Z3_mk_gt(z3_ctx, pos_formula.k[i], zero);
				f = Z3_mk_and(z3_ctx, abstr, t);
				if (pos_formula->check_sat(f) != sl_formula::SL_SAT_UNSAT) {
					noll_ls_t& ls;
					ls = space->m.ls;
					n = get_hole(preds_array[ls.pid]);
					source = g[boost::graph_bundle][noll_vector_at(ls.args, 0)];
					target = g[boost::graph_bundle][noll_vector_at(ls.args, n)];
					boost::add_edge(source, target, space, g);
				}
				break;
		}
	}
}

/*
 *void sl_entail::build_graph()
 *{
 *        rewrite_pure_matrix();
 *        add_vertex();
 *        add_edge();
 *}
 *void sl_entail::rewrite_pure_matrix()
 *{
 *        noll_pure_t* pure;
 *        pure = noll_prob->pform->pure;
 *        for (int i=0; i < pure->size-1; ++i) {
 *                for (int j = 1; j < pure->size-i; ++j) {
 *                        if(pure->m[i][j] == NOLL_PURE_OTHER){
 *                                if (pos_formula->check_equal(i, i+j))
 *                                        pure->m[i][j] = NOLL_PURE_EQ;
 *                                if (pos_formula->check_unequal(i, i+j))
 *                                        pure->m[i][j] = NOLL_PURE_NEQ;
 *                        }
 *                }
 *        }
 *}
 *void sl_entail::add_vertex()
 *{
 *        shared_ptr<set<int> > eq_class;
 *        while ((eq_class = get_eq_class()) != nullptr) {
 *                Graph::vertex_descriptor vd = boost::add_vertex(g);
 *                g[vd].insert(eq_class->begin(), eq_class->end());
 *                auto it = begin(*eq_class);
 *                for (; it != end(*eq_class); ++it)
 *                        g[graph_bundle][*it] = vd;
 *        }
 *}
 *shared_ptr<set<int> > sl_entail::get_eq_class()
 *{
 *        size_t i, j;
 *        pure = noll_prob->pform->pure;
 *        static vector<bool> visited(pure->size);
 *
 *        i = 0;
 *        while (visited[i]) ;
 *        
 *        if (i == visited.size())
 *                return nullptr;
 *
 *        shared_ptr<set<int> > eq_class = make_shared<set<int> >();
 *        queue<int> q;
 *        q.push(i);
 *        while (!q.empty()) {
 *                i = q.front();
 *                visited[i] = true;
 *                eq_class->insert(i);
 *                for (j = 1; j < pure->size-i; ++j) {
 *                        if (pure->m[i][j] == NOLL_PURE_EQ)
 *                                q.push(i+j);
 *                }
 *                q.pop();
 *        }
 *        return eq_class;
 *}
 *void sl_entail::add_edge()
 *{
 *        noll_space_t* space;
 *        typedef Graph::vertex_descriptor VD;
 *        VD source, target;
 *        for (size_t i = 0; i < pos_formula->space.size(); ++i) {
 *                space = pos_formula->space[i];
 *                switch (space->kind) {
 *                        case NOLL_SPACE_PTO:
 *                                noll_pto_t& pto;
 *                                pto = space->m.pto;
 *                                source = g[graph_bundle][pto.sid];
 *                                target = g[graph_bundle][noll_vector_at(pto.dest, 0)];
 *                                boost::add_edge(source, target, space, g);
 *                                break;
 *                        case NOLL_SPACE_LS:
 *                                if (pos_formula->check_alloc(i) >= 0) {
 *                                        noll_ls_t& ls;
 *                                        ls = space->m.ls;
 *                                        ndir = preds_array[ls.pid]->typ->nDir;
 *                                        source = g[graph_bundle][noll_vector_at(ls.args, 0)];
 *                                        target = g[graph_bundle][noll_vector_at(ls.args, ndir)];
 *                                        boost::add_edge(source, target, space, g);
 *                                }
 *                                break;
 *                }
 *        }
 *}
 */
/*
 *void sl_formula::check_equal(int u, int v)
 *{
 *        Z3_ast eq;
 *        Z3_ast t;
 *        eq = Z3_mk_eq(z3_ctx, pos_formula.var[u], pos_formula.var[v]);
 *        t = Z3_mk_implies(z3_ctx, pos_formula.abstr, eq);
 *        Z3_solver_assert(z3_ctx, z3_solver, t);
 *
 *        switch (Z3_solver_check(z3_ctx, s)) {
 *                case Z3_L_FALSE:
 *                case Z3_L_UNDEF:
 *                case Z3_L_TRUE:
 *        }
 *
 *}
 *void sl_formula::check_unequal(int u, int v)
 *{
 *}
 */
void sl_entail::check_homom()
{
}
