#ifndef SL_GRAPH_H
#define SL_GRAPH_H

#include <vector>
#include <set>
#include <map>
#include <utility>

#include <boost/config.hpp>
#include <boost/utility.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/graph/graph_traits.hpp>

#include "sl_abstr.h"

class graph {
public:
	typedef std::set<int> vertex_lable;
	typedef size_t edge_lable;
	typedef std::map<int, int> graph_lable;

	typedef boost::adjacency_list<boost::vecS,
				      boost::vecS,
				      boost::bidirectionalS,
				      vertex_lable,
				      edge_lable,
				      graph_lable> adjacency_list;

	typedef std::set<int> cc_t;
	typedef std::vector<int> cycle_t;
	typedef std::vector<cycle_t> cc_cycle_t;
	typedef boost::graph_traits<adjacency_list>::edge_descriptor edge_descriptor;
	typedef boost::graph_traits<adjacency_list>::edge_iterator edge_iterator;
	typedef adjacency_list::out_edge_iterator out_edge_iterator;

	graph() = default;
	graph(const graph&);
	graph& operator=(const graph&);

	graph(graph&&) noexcept;
	graph& operator=(graph&&) noexcept;
	void init(sl_abstr&);

	std::pair<edge_iterator, edge_iterator> get_edge();
	std::vector<edge_descriptor> get_path(size_t, size_t) const;
	std::vector<edge_descriptor> get_path(size_t);

	size_t var_to_ver(size_t);
	size_t source(edge_descriptor);
	size_t target(edge_descriptor);

	std::vector<int> get_cc_cycle_num() const;
	std::vector<cc_cycle_t>& get_cc_cycle();
	int which_cc(size_t) const;
	bool is_dag_like() const;
	int get_edge_property(size_t, size_t) const;
	int get_edge_property(edge_descriptor);

	/* only act right in dag like graph */
	std::pair<int, int> get_cycle_coord(size_t) const;
	std::pair<int, int> get_cycle_coord(edge_descriptor) const;

	bool is_cycle(const std::pair<int, int>&) const;
	std::vector<int> get_cycle(const std::pair<int, int>&) const;
	std::vector<edge_descriptor> get_cycle_edge(std::pair<int, int>&);
	std::vector<edge_descriptor> merge_path(std::vector<edge_descriptor>&, std::vector<int>&) const;
	std::vector<edge_descriptor> merge_path(std::vector<edge_descriptor>&, std::vector<edge_descriptor>&);
	std::vector<std::pair<int, int>> get_cycle_coords() const;
private:
	void add_vertex(sl_abstr&);
	void add_edge(sl_abstr&);
	void seek_cc();
	void seek_cycle();

/*
 *        void dfs(int, std::vector<int>&, std::vector<int>&, std::vector<int>&, std::vector<std::vector<int>>&);
 *
 *        int locate(std::vector<int>&) const;
 *        int find(std::vector<int>&, int) const;
 */

	std::vector<edge_descriptor> get_path(size_t, size_t, std::vector<edge_descriptor>&,
						std::vector<int>&, std::map<int, int>&) const;

	std::vector<cc_t> cc;
	std::vector<cc_cycle_t> cycle;

	adjacency_list adj_list;

};
#endif // sl_graph.h
