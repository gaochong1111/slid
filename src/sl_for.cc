#include "sl_for.h"
#include "slid_sat.h"

sl_for::sl_for(noll_form_t* f)
	: nollf(f)
{
	noll_space_array* t = nullptr;
	slid_mk_space_array(&t, f->space);
	sp_atoms.insert(end(sp_atoms), noll_vector_array(t), noll_vector_array(t) + noll_vector_size(t));
	noll_space_array_delete(t);
}
void sl_for::init(noll_form_t* f)
{
	nollf = f;

	noll_space_array* t = nullptr;
	slid_mk_space_array(&t, f->space);
	sp_atoms.insert(end(sp_atoms), noll_vector_array(t), noll_vector_array(t) + noll_vector_size(t));
	noll_space_array_delete(t);
}

/*
 *sl_for::sl_for(sl_for& f)
 *{
 *        nollf = f.nollf;
 *        sp_atoms = f.sp_atoms;
 *}
 *
 *sl_for& sl_for::operator=(sl_for& f)
 *{
 *        if (this == &f)
 *                return *this;
 *
 *        nollf = f.nollf;
 *        sp_atoms = f.sp_atoms;
 *
 *        return *this;
 *}
 */
