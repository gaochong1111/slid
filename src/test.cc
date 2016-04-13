#include <iostream>
#include <set>
#include <memory>
#include <boost/graph/adjacency_list.hpp>

using namespace std;

struct ELable {
	int i;
	void* p;
};


typedef set<int> VLable;
typedef map<int, int> GLable;

typedef boost::adjacency_list<boost::vecS, boost::vecS, boost::bidirectionalS, VLable, ELable , GLable> Graph;

int main()
{
/*
 *        Graph g;
 *        Graph::vertex_descriptor v1 = boost::add_vertex(g), v2;
 *
 *        g[v1].insert(3);
 *        g[boost::graph_bundle][3] = v1;
 *        g[v1].insert(5);
 *        g[boost::graph_bundle][5] = v1;
 *
 *        v2 = boost::add_vertex(g);
 *        g[v2].insert(3);
 *        g[boost::graph_bundle][3] = v2;
 *
 *        for (auto git=begin(g[boost::graph_bundle]); git != end(g[boost::graph_bundle]); ++git) {
 *                cout << "(" << git->first << ",";
 *                cout << git->second << ") ";
 *        }
 *        cout << endl;
 *
 *        ELable e;
 *        e.i = 9;
 *        e.p = NULL;
 *
 *        shared_ptr<int> p = make_shared<int>();
 *        Graph::vertex_iterator vertex_iter, vertex_iter_end, it;
 *        tie(vertex_iter, vertex_iter_end) = boost::vertices(g);
 *        
 *        it = vertex_iter;
 *        boost::add_edge(v1, v2, e, g);
 *
 *        for (; vertex_iter != vertex_iter_end; ++vertex_iter) {
 *                cout << "vertex:" << *vertex_iter << endl;
 *                VLable::iterator iter;
 *                for (iter = begin(g[*vertex_iter]); iter != end(g[*vertex_iter]); ++iter) {
 *                        cout << *iter << endl;
 *                }
 *                Graph::out_edge_iterator edge_iter, edge_iter_end;
 *                tie(edge_iter, edge_iter_end) = boost::out_edges(*vertex_iter, g);
 *                for (; edge_iter != edge_iter_end; ++edge_iter) {
 *                        cout << "edge:" << boost::source(*edge_iter, g) << "-->";
 *                        cout << boost::target(*edge_iter, g) << endl;
 *                        cout << g[*edge_iter].i << endl;
 *                }
 *        }
 */
	Graph g;
	boost::add_vertex(g);
	boost::add_vertex(g);
	boost::add_vertex(g);
	boost::add_vertex(g);
	boost::add_edge(0, 1, g);
	boost::add_edge(0, 3, g);
	boost::add_edge(0, 0, g);
	boost::add_edge(1, 0, g);
	Graph::out_edge_iterator edge_iter, edge_iter_end;
	Graph::in_edge_iterator it1, it2;
	int source, target;
	 tie(edge_iter, edge_iter_end) = boost::out_edges(0, g);
	 for (; edge_iter != edge_iter_end; ++edge_iter) {
		 source = boost::source(*edge_iter, g);
		 target = boost::target(*edge_iter, g);

		 cout << "edge:" << source << "-->";
		 cout << target << endl;
	 }
	 tie(it1, it2) = boost::in_edges(0, g);
	 for (; it1 != it2; ++it1) {
		 source = boost::source(*it1, g);
		 target = boost::target(*it1, g);

		 cout << "edge:" << source << "-->";
		 cout << target << endl;
	 }

	return 0;
}
