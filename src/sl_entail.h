#ifndef SL_ENTAIL_H
#define SL_ENTAIL_H

#include <set>
#include <vector>

#include <boost/config.hpp>
#include <boost/utility.hpp>
#include <boost/graph/adjacency_list.hpp>

#include "noll_form.h"

#include <z3.h>



typedef std::set<int> VLable;
typedef noll_space_t* ELable;
typedef std::map<int, int> GLable;

typedef boost::adjacency_list<boost::vecS,
				boost::vecS,
				boost::directedS,
				VLable,
				ELable,
				GLable> Graph;

/*
class sl_formula {
private:
	sl_sat_t sat_flag;
	vector<noll_space_t*> space;
	vector<Z3_ast> k;
	vector<vector<shared_ptr<IALoc> > > *m;
	Z3_ast abstr;
public:
	enum sl_sat_t {
		SL_SAT,
		SL_UNSAT,
		SL_UNKNOWN
	};
};
*/
class sl_entail {
public:
	enum sl_entail_t {
		SL_ENTAIL_SAT,
		SL_ENTAIL_UNSAT,
	};
	sl_entail();
	void check_entail();
	bool check_entail(shared_ptr<sl_formula>&);
private:
	void add_vertex(Z3_ast, Graph&);
	std::vector<std::set<int>> get_equivalence_class(Z3_ast);

	void add_edge(Z3_ast, Graph&);

	sl_entail_t kind;

	Z3_context z3_ctx;
	std::vector<Z3_ast> var;

	sl_formula pos_formula;

	std::vector<sl_formula> neg_formula;
};

#endif // sl_entail.h
