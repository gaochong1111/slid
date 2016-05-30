#include "sl_var.h"

sl_var::sl_var(const sl_var& v)
{
	sid = v.sid;
	/*
	 *type = v.type;
	 *symbol = v.symbol;
	 */
	node = v.node;
}
sl_var::sl_var(sl_var&& v) noexcept
{
	sid = v.sid;
	/*
	 *type = v.type;
	 *symbol = v.symbol;
	 */
	node = v.node;

	v.sid = -1;
	/*
	 *v.type = nullptr;
	 *v.symbol = nullptr;
	 */
	v.node = nullptr;
}

sl_var& sl_var::operator=(const sl_var& v)
{
	if (this == &v)
		return *this;
	sid = v.sid;
	/*
	 *type = v.type;
	 *symbol = v.symbol;
	 */
	node = v.node;
}
sl_var& sl_var::operator=(sl_var&& v) noexcept
{
	if (this == &v)
		return *this;
	sid = v.sid;
	/*
	 *type = v.type;
	 *symbol = v.symbol;
	 */
	node = v.node;

	v.sid = -1;
	/*
	 *v.type = nullptr;
	 *v.symbol = nullptr;
	 */
	v.node = nullptr;

	return *this;
}

sl_var::sl_var(size_t i, Z3_ast ast)
{
	sid = i;
	/*
	 *type = sort;
	 *symbol = sym;
	 */
	node = ast;
}
