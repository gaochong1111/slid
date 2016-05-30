#ifndef SL_FORMULA_H
#define SL_FORMULA_H

#include "sl_context.h"
#include "sl_abstr.h"
#include "graph.h"
#include "noll_form.h"

class sl_formula: public sl_abstr, public graph {
public:
	sl_formula() = default;
	sl_formula(noll_form_t*, sl_context&);
	sl_formula(const sl_formula&);
	sl_formula& operator=(const sl_formula&);

	sl_formula(sl_formula&&) noexcept;
	sl_formula& operator=(sl_formula&&) noexcept;	

	void mk_graph();
	//Z3_ast mk_abstr(noll_ls_t*, size_t);


	bool is_static_param(noll_pred_t*, size_t);
};

#endif // sl_formula.h
