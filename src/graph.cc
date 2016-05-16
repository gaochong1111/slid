#include <queue>
#include <cassert>
#include <algorithm>

#include "graph.h"
#include "slid_sat.h"
#include "sl_sat.h"

using namespace std;

/* --------------------------------------------------------------------------*/
/**
 * @synopsis  graph initialize a graph using abstraction
 *
 * @param f separation logic formula
 */
/* --------------------------------------------------------------------------*/
/*
 *graph::graph(sl_abstr& abs)
 *        : init_flag(false)
 *{
 *        init(abs);
 *}
 */
graph::graph(const graph& g)
{
	cc = g.cc;
	cycle = g.cycle;
	adj_list = g.adj_list;
}
graph& graph::operator=(const graph& g)
{
	if (this == &g)
		return *this;
	cc = g.cc;
	cycle = g.cycle;
	adj_list = g.adj_list;
}
graph::graph(graph&& g) noexcept
{
	cc = g.cc;
	cycle = g.cycle;
	adj_list = g.adj_list;
}
graph& graph::operator=(graph&& g) noexcept
{
	if (this == &g)
		return *this;
	cc = g.cc;
	cycle = g.cycle;
	adj_list = g.adj_list;
}
void graph::init(sl_abstr& abs)
{
	/*create vertex*/
	add_vertex(abs);
	/*create edge*/
	add_edge(abs);

	seek_cc();
	seek_cycle();
}

/*
 *bool graph::init()
 *{
 *        return init_flag;
 *}
 */

/* --------------------------------------------------------------------------*/
/**
 * @synopsis  add_vertex vertex represent the equivalence class of variables
 *
 * @param f
 */
/* --------------------------------------------------------------------------*/
void graph::add_vertex(sl_abstr& abs)
{
	set<int> eq_class;
	vector<set<int>> eq_class_set;
	eq_class_set = sl_sat::get_equivalence_class(abs);
	for (size_t i = 0; i < eq_class_set.size(); ++i) {
		eq_class = eq_class_set[i];	
		/* add one vertex of index i*/
		boost::add_vertex(adj_list);
		/* initialize the property of the ith vertex*/
		adj_list[i].insert(begin(eq_class), end(eq_class));
		/* initialize the property of graph*/
		for (auto it = begin(eq_class); it != end(eq_class); ++it)
			adj_list[boost::graph_bundle][*it] = i;
	}
}

/* --------------------------------------------------------------------------*/
/**
 * @synopsis  add_edge create an edge for none empty spatial atom
 *
 * @param f
 */
/* --------------------------------------------------------------------------*/
void graph::add_edge(sl_abstr& abs)
{
	vector<noll_space_t*>& sp_atoms = abs.get_spatial_atoms();
	noll_space_t* sp_atom;
	size_t source, target, n;
	for (size_t i = 0; i < sp_atoms.size(); ++i) {
		sp_atom = sp_atoms[i];
		switch (sp_atom->kind) {
			case NOLL_SPACE_PTO:
				noll_pto_t* pto;
				pto = &(sp_atom->m.pto);
				source = adj_list[boost::graph_bundle][pto->sid];
				target = adj_list[boost::graph_bundle][noll_vector_at(pto->dest, 0)];
				boost::add_edge(source, target, i, adj_list);
				break;
			case NOLL_SPACE_LS:
				/* the spatial atom may not be empty */
				if (!abs.is_sp_atom_empty(i)) {
					noll_ls_t* ls;
					ls = &(sp_atom->m.ls);
					n = slid_get_hole(noll_vector_at(preds_array, ls->pid));
					source = adj_list[boost::graph_bundle][noll_vector_at(ls->args, 0)];
					target = adj_list[boost::graph_bundle][noll_vector_at(ls->args, n)];
					boost::add_edge(source, target, i, adj_list);
				}
				break;
		}
	}
}
/* --------------------------------------------------------------------------*/
/**
 * @synopsis  get_edge_property 
 *
 * @param u   vertex index u
 * @param v
 *
 * @return    edge property representing spatial atom id 
 * 	      -1 no edge between u and v
 */
/* --------------------------------------------------------------------------*/
int graph::get_edge_property(size_t u, size_t v) const
{
	adjacency_list::out_edge_iterator it1, it2;
	tie(it1, it2) = boost::out_edges(u, adj_list);
	for (; it1 != it2; ++it1) {
		if (v == boost::target(*it1, adj_list))
			return adj_list[*it1];
	}
	return -1;
}
int graph::get_edge_property(edge_descriptor e)
{
	return get_edge_property(source(e), target(e));
}
/* --------------------------------------------------------------------------*/
/**
 * @synopsis  seek_cc calculate the connected components 
 */
/* --------------------------------------------------------------------------*/
void graph::seek_cc()
{
	size_t i, j, k;
	adjacency_list::out_edge_iterator out_it1, out_it2;
	adjacency_list::in_edge_iterator in_it1, in_it2;
	deque<int> q;
	set<int> t;
	size_t num = boost::num_vertices(adj_list);
	vector<int> visited(num);

	for (i = 0; i < visited.size(); ++i)
		visited[i] = 0;

	for (i = 0; i < num; ++i) {
		if (visited[i])
			continue;
		q.push_back(i);
		t.clear();
		while (!q.empty()) {
			j = q.front();
			visited[j] = 1;
			t.insert(j);
			tie(in_it1, in_it2) = boost::in_edges(j, adj_list);
			for (; in_it1 != in_it2; ++in_it1) {
				k = boost::source(*in_it1, adj_list);
				if (!(visited[k]) && (find(begin(q), end(q), k) == end(q)))
					q.push_back(k);
			}
			tie(out_it1, out_it2) = boost::out_edges(j, adj_list);
			for (; out_it1 != out_it2; ++out_it1) {
				k = boost::target(*out_it1, adj_list);
				if (!(visited[k]) && (find(begin(q), end(q), k) == end(q)))
					q.push_back(k);
			}
			q.pop_front();
		}
		cc.push_back(t);
	}
}
/* --------------------------------------------------------------------------*/
/**
 * @synopsis  seek_cycle calculate the cycle of the graph
 */
/* --------------------------------------------------------------------------*/
void graph::seek_cycle()
{
	size_t i, j;
	vector<vector<int>> t;
	adjacency_list::out_edge_iterator it1, it2;
	vector<int> c, t1, s;
	map<int, bool> m;
	for (i = 0; i < cc.size(); ++i) {
		c.assign(begin(cc[i]), end(cc[i]));
		/*
		 *for (j = 0; j < visited.size(); ++j)
		 *        visited[j] = 0;
		 */
		for (j = 0; j < c.size(); ++j)
			m[c[j]] = false;
		t.clear();
		for (j = 0; j < c.size(); ++j) {
			if (m[c[j]])
				continue;
			s.push_back(c[j]);
			while (!s.empty()) {
				t1.clear();
				size_t k = s.back();
				if (!m[k]) {
					tie(it1, it2) = boost::out_edges(k, adj_list);
					for (; it1 != it2; ++it1) {
						size_t tar = boost::target(*it1, adj_list);
						auto it = find(begin(s), end(s), tar);
						if (it != end(s)) {
							t1.insert(end(t1), it, end(s));
							t.push_back(t1);
						}
					}
					m[k] = true;
				}
				tie(it1, it2) = boost::out_edges(k, adj_list);
				for (; it1 != it2; ++it1) {
					size_t tar = boost::target(*it1, adj_list);
					if(!m[tar]) {
						s.push_back(tar);
						break;
					}
				}
				if (it1 == it2)
					s.pop_back();

			}
		}
		cycle.push_back(t);
	}
}
/* --------------------------------------------------------------------------*/
/**
 * @synopsis  dfs 
 *
 * @param v
 * @param c
 * @param s
 * @param visited
 * @param r
 */
/* --------------------------------------------------------------------------*/
/*
 *void graph::dfs(int v, vector<int>& com, vector<int>& s, vector<int>& visited, vector<vector<int>>& r)
 *{
 *        int i, t;
 *        vector<int> c;
 *        adjacency_list::out_edge_iterator it1, it2;
 *        visited[v] = 1;
 *        if ((i = locate(s)) != -1) {
 *                c.insert(end(c), begin(s)+i, end(s)-1); 
 *                r.push_back(c);	
 *        }
 *        tie(it1, it2) = boost::out_edges(com[v], adj_list);
 *        for (; it1 != it2; ++it1) {
 *                t = boost::target(*it1, adj_list);
 *                if(!visited[find(com, t)]) {
 *                        s.push_back(t);
 *                        dfs(t, com, s, visited, r);
 *                        s.pop_back();
 *                }
 *        }
 *}
 *int graph::locate(vector<int>& vec) const
 *{
 *        int k = *(end(vec)-1);
 *        for (int i = vec.size()-2; i >= 0; --i) {
 *                if (k == vec[i])
 *                        return i;
 *        }
 *        return -1;
 *}
 *int graph::find(vector<int>& vec, int k) const
 *{
 *        for (size_t i = 0; i < vec.size(); ++i) {
 *                if (vec[i] == k)
 *                        return i;
 *        }
 *        return -1;
 *}
 */
/* --------------------------------------------------------------------------*/
/**
 * @synopsis  is_dag_like 
 *
 * @return   
 */
/* --------------------------------------------------------------------------*/
bool graph::is_dag_like() const
{
	assert(!cycle.empty());
	int u, v;
	size_t i, j, k;
	adjacency_list::out_edge_iterator it1, it2;

	for (i = 0; i < cycle.size(); ++i) {
		if (cycle[i].size() > 1)
			return false;
		for (j = 0; j < cycle[i].size(); ++j) {
			for (k = 0; k < cycle[i][j].size(); ++k) {
				u = cycle[i][j][k];
				v = (k == cycle[i][j].size()-1) ? cycle[i][j][0] : cycle[i][j][k+1];
				tie(it1, it2) = boost::out_edges(u, adj_list);
				if ((boost::out_degree(u, adj_list) != 1) || (boost::target(*it1, adj_list) != v))
					return false;
			}
		}
	}
	return true;
}

vector<int> graph::get_cc_cycle_num() const
{
	vector<int> res(cc.size());

	for (size_t i = 0; i < cycle.size(); ++i)
		res[i] = cycle[i].size();

	return res;
}

vector<graph::cc_cycle_t>& graph::get_cc_cycle()
{
	return cycle;
}

int graph::which_cc(size_t v) const
{
	for (size_t i = 0; i < cc.size(); ++i) {
		auto it = std::find(begin(cc[i]), end(cc[i]), v);
		if (it != end(cc[i]))
			return i;
	}
	return -1;
}

pair<int, int> graph::get_cycle_coord(size_t v) const
{
	int i = which_cc(v);
	int j;
	for (size_t k = 0; k < cycle[i].size(); ++k) {
		auto it = std::find(begin(cycle[i][k]), end(cycle[i][k]), v);
		if (it != end(cycle[i][k]))
			return make_pair(i, k);
	}
	return make_pair(-1, -1);
}

pair<int, int> graph::get_cycle_coord(edge_descriptor e) const
{
	return get_cycle_coord(boost::source(e, adj_list));
}

bool graph::is_cycle(const pair<int, int>& coord) const
{
	return (coord.first >= 0 && coord.second >= 0);
}

vector<int> graph::get_cycle(const pair<int, int>& coord) const
{
	return cycle[coord.first][coord.second];
}

vector<graph::edge_descriptor> graph::merge_path(vector<graph::edge_descriptor>& path1, vector<graph::edge_descriptor>& path2)
{
	vector<edge_descriptor> res(path1);
	res.insert(end(res), begin(path2), end(path2));
	return res;
}

vector<graph::edge_descriptor> graph::merge_path(vector<graph::edge_descriptor>& path1, vector<int>& c) const
{
	vector<edge_descriptor> res(path1);
	edge_descriptor e = path1[path1.size()-1];
	out_edge_iterator ei, ei_end;
	vector<int>::iterator it, it2;
	size_t v = boost::target(e, adj_list);
	it = std::find(begin(c), end(c), v);
	for (it2 = it; it2 != end(c); ++it2) {
		tie(ei, ei_end) = boost::out_edges(*it2, adj_list);
		res.push_back(*ei);
	}
	for (it2 = begin(c); it2 != it; ++it2) {
		tie(ei, ei_end) = boost::out_edges(*it2, adj_list);
		res.push_back(*ei);
	}
	return res;
}

vector<pair<int, int>> graph::get_cycle_coords() const
{
	vector<pair<int, int>> res;
	for (size_t i = 0; i < cycle.size(); ++i) {
		for (size_t j = 0; j < cycle[i].size(); ++j)
			res.push_back(make_pair(i, j));
	}
	return res;
}
vector<graph::edge_descriptor> graph::get_path(size_t u)
{
	vector<edge_descriptor> res;
	pair<int, int> coord = get_cycle_coord(u);
	if (!is_cycle(coord))
		return res;

	vector<int> c = get_cycle(coord);
	out_edge_iterator ei, ei_end;
	vector<int>::iterator it, it2;
	it = std::find(begin(c), end(c), u);
	for (it2 = it; it2 != end(c); ++it2) {
		tie(ei, ei_end) = boost::out_edges(*it2, adj_list);
		res.push_back(*ei);
	}
	for (it2 = begin(c); it2 != it; ++it2) {
		tie(ei, ei_end) = boost::out_edges(*it2, adj_list);
		res.push_back(*ei);
	}
	return res;
}

vector<graph::edge_descriptor> graph::get_path(size_t u, size_t v) const
{
	assert(u != v);
	vector<edge_descriptor> r;
	
	int i = which_cc(u);
	if (i != which_cc(v))
		return r;

	vector<int> t;
	vector<edge_descriptor> s;
	t.assign(begin(cc[i]), end(cc[i]));
	vector<int> visited(t.size());
	map<int, int> m;
	for (size_t i = 0; i < t.size(); ++i)
		m[t[i]] = i;
	return get_path(u, v, s, visited, m);
}

vector<graph::edge_descriptor> graph::get_path(size_t u, size_t v,
						vector<edge_descriptor>& s, vector<int>& visited,
						map<int, int>& m) const
{
	if (u == v) return s;
	vector<edge_descriptor> res;
	visited[m[u]] = 1;
	out_edge_iterator ei, ei_end;
	tie(ei, ei_end) = boost::out_edges(u, adj_list);
	for (; ei != ei_end; ++ei) {
		size_t targ = boost::target(*ei, adj_list);
		if (!visited[m[targ]]) {
			s.push_back(*ei);
			res = get_path(targ, v, s, visited, m);
			if (!res.empty())
				break;
			s.pop_back();
		}
	}
	return res;
}

pair<graph::edge_iterator, graph::edge_iterator> graph::get_edge()
{
	return boost::edges(adj_list);
}

size_t graph::var_to_ver(size_t vid)
{
	return adj_list[boost::graph_bundle][vid];
}
size_t graph::source(edge_descriptor e)
{
	return boost::source(e, adj_list);
}
size_t graph::target(edge_descriptor e)
{
	return boost::target(e, adj_list);
}
