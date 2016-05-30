#include "sl_formula.h"
#include "noll_preds.h"

sl_formula::sl_formula(const sl_formula& f0)
: sl_abstr(f0), graph(f0)
{
}
sl_formula::sl_formula(sl_formula&& f0) noexcept
: sl_abstr(f0), graph(f0)
{
}
sl_formula& sl_formula::operator=(sl_formula&& f0) noexcept
{
	if (this == &f0)
		return *this;
	sl_abstr::operator=(f0);
	graph::operator=(f0);

	return *this;
}
sl_formula& sl_formula::operator=(const sl_formula& f0)
{
	if (this == &f0)
		return *this;
	sl_abstr::operator=(f0);
	graph::operator=(f0);

	return *this;
}
sl_formula::sl_formula(noll_form_t* f0, sl_context& c)
:sl_abstr(f0, c)
{
}

void sl_formula::mk_graph()
{
	graph::init(*this);
}



bool sl_formula::is_static_param(noll_pred_t* pred, size_t sid)
{
	if (noll_vector_at(pred->typ->argkind,sid-1) == NOLL_ATYP_BORDER)
		return true;
	return false;
}

/*
 *Z3_ast sl_formula::mk_abstr(noll_ls_t* pred, size_t k)
 *{
 *        return sl_abstr::mk_pred(pred, k);
 *}
 */
