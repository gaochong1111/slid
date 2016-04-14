#ifndef SL_FORMULA_H
#define SL_FORMULA_H

#include <vector>
#include <memory>

#include <z3.h>

#include "noll_form.h"
#include "slid_sat.h"


typedef slid_in_alloc_loc* IALoc;

extern "C" void test_check_sat(noll_form_t*);

class SLFormula {
public:
	enum sl_sat_t {
		SL_SAT_SAT,
		SL_SAT_UNSAT,
		SL_SAT_UNKNOWN
	};

	SLFormula(noll_form_t*, Z3_context, Z3_sort, Z3_sort, vector<Z3_ast>&);
	sl_sat_t issat();
	bool check_equal(size_t, size_t);
	bool check_unequal(size_t, size_t);
	int check_alloc(size_t);
private:
	void mk_abstr();
	void mk_context(slid_context);
	slid_context mk_slid_context();
	sl_sat_t check_sat(Z3_ast);
	void check_sat();

	noll_form_t* formula;
	Z3_context z3_ctx;
	Z3_sort isort;
	Z3_sort bsort;
	vector<Z3_ast> var;
	vector<noll_space_t*> space;
	vector<Z3_ast> k;
	vector<shared_ptr<vector<IALoc> > > m;
	//Z3_ast pure;
	//Z3_ast space;
	Z3_ast abstr = NULL;
	sl_sat_t kind = SL_SAT_UNKNOWN;
};

#endif //sl_formula.h
