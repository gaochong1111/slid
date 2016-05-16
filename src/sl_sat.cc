#include <queue>

#include "sl_sat.h"
#include "sl_abstr.h"
#include "noll_form.h"
#include "noll_entl.h"

using namespace std;

extern noll_entl_t* noll_prob;


bool sl_sat::check_sat(Z3_context ctx, Z3_ast f)
{
	Z3_solver s;

	s = Z3_mk_solver(ctx);
	Z3_solver_inc_ref(ctx, s);
	Z3_solver_assert(ctx, s, f);

	switch (Z3_solver_check(ctx, s)) {
		case Z3_L_FALSE:
		case Z3_L_UNDEF:
			return false;
		case Z3_L_TRUE:
			return true;
	}
}

vector<set<int>> sl_sat::get_equivalence_class(sl_abstr& abs)
{
	size_t i, j, k;
	Z3_ast eq, a[2];
	sl_context& ctx = abs.get_context();
	Z3_context z3_ctx = ctx.z3_ctx;
	queue<int> q;
	vector<set<int>> res;
	set<int> t;
	size_t lvar_num = ctx.var.size();
	noll_var_array* lvars = noll_prob->pform->lvars;
	vector<int> visited(lvar_num);

	for (i = 0; i < visited.size(); ++i)
		visited[i] = 0;

	for (i = 1; i < lvar_num; ++i) {
		if (visited[i] || (noll_vector_at(lvars, i)->vty->kind != NOLL_TYP_RECORD))
			continue;
		t.clear();
		t.insert(i);
		visited[i] = 1;
		for (j = i + 1; j < lvar_num; ++j) {
			 eq = Z3_mk_eq(z3_ctx, ctx.var[i].node, ctx.var[j].node);
			 a[0] = abs.get_abstr();
			 a[1] = Z3_mk_not(z3_ctx, eq);
			 if ((!check_sat(z3_ctx, Z3_mk_and(z3_ctx, 2, a))) && (visited[j] == 0)) {
				 t.insert(j);
				 visited[j] = 1;
			 }
		}
		res.push_back(t);
	}
	return res;
}


