/**************************************************************************
 *
 *  SPEN decision procedure
 *
 *  you can redistribute it and/or modify it under the terms of the GNU
 *  Lesser General Public License as published by the Free Software
 *  Foundation, version 3.
 *
 *  It is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  See the GNU Lesser General Public License version 3.
 *  for more details (enclosed in the file LICENSE).
 *
 **************************************************************************/

/**
 * Lemma representation and checking for the syntactic procedure.
 */

#include <stdbool.h>
#include "noll_lemma.h"
#include "noll.h"               // for NOLL_DEBUG

NOLL_VECTOR_DEFINE (noll_lemma_array, noll_lemma_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_lemma_array **lemma_array;

/**
 * @brief Allocates the global array of lemma and initialize it.
 */
void
noll_lemma_init (void)
{
  assert (preds_array != NULL && noll_vector_size (preds_array) > 0);

  if (lemma_array != NULL)
    return;

  uint_t size = noll_vector_size (preds_array);
  lemma_array =
    (noll_lemma_array **) malloc (sizeof (noll_lemma_array *) * size);
  memset (lemma_array, 0, sizeof (noll_lemma_array *) * size);
  for (uint_t pid = 0; pid < size; pid++)
    {
      lemma_array[pid] = noll_lemma_init_pred (pid);
#ifndef NDEBUG
      fprintf (stdout, "\nLemma init pred-%d (%s): %d\n", pid,
               noll_pred_name (pid), noll_vector_size (lemma_array[pid]));
#endif
    }
}

/* ====================================================================== */
/* Constructors/Destructors */
/* ====================================================================== */

/**
 * @brief Return an empty lemma for predicate @p pid.
 */
noll_lemma_t *
noll_lemma_new (uint_t pid)
{
  const noll_pred_t *pred = noll_pred_getpred (pid);
  noll_lemma_t *lem = (noll_lemma_t *) malloc (sizeof (noll_lemma_t));
  lem->pid = pid;
  lem->kind = NOLL_LEMMA_OTHER;
  lem->rule.vars = noll_var_array_new ();
  for (uint_t i = 0; i <= pred->def->fargs; i++)
    noll_var_array_push (lem->rule.vars, noll_vector_at (pred->def->vars, i));
  lem->rule.fargs = pred->def->fargs;
  lem->rule.pure = NULL;
  lem->rule.pto = NULL;
  lem->rule.nst = NULL;
  lem->rule.rec = NULL;
  return lem;
}

/**
 * @brief Adds to (a copy of) @p bvars, the variables in @p pvars.
 */
void
noll_lemma_add_lvars (noll_lemma_t * lem,
                      noll_var_array * bvars, uint_t bargs,
                      noll_var_array * pvars, uint_t pargs)
{
  assert (lem != NULL);

  /// lem->rule.vars has already a copy of @p bvars
  assert (noll_vector_size (lem->rule.vars) == (bargs + 1));

  /// get from @p pvars variables of different type
  uint_t bi = 0;
  uint_t pi = 0;
  while ((bi <= bargs) && (pi <= pargs))        /// includes nil
    {
      /// check the type
      noll_type_t *typ_bi = noll_var_type (bvars, bi);
      noll_type_t *typ_pi = noll_var_type (pvars, pi);
      assert (typ_bi != NULL);
      assert (typ_pi != NULL);
      if (typ_bi->kind != typ_pi->kind) // TODO: does not work if border!
        {
          // push the variable at pi
          noll_var_t *vi = noll_var_copy (noll_vector_at (pvars, pi));
          char *nname =
            (char *) malloc (sizeof (char) * (strlen (vi->vname) + 3));
          snprintf (nname, strlen (vi->vname) + 3, "%s_%d", vi->vname, pi);     // TODO: be more robust
          free (vi->vname);
          vi->vname = nname;
          noll_var_array_push (lem->rule.vars, vi);
          pi++;
        }
      else
        {
          bi++;
          pi++;
        }
    }

  while (pi <= pargs)           /// includes other parameters
    {
      noll_var_t *vi = noll_var_copy (noll_vector_at (pvars, pi));
      char *nname =
        (char *) malloc (sizeof (char) * (strlen (vi->vname) + 3));
      snprintf (nname, strlen (vi->vname) + 3, "%s_%d", vi->vname, pi); // TODO: be more robust
      free (vi->vname);
      vi->vname = nname;
      noll_var_array_push (lem->rule.vars, vi);
      pi++;
    }
#ifndef NDEBUG
  fprintf (stdout, "\nlemma_add_lvars: returns");
  noll_var_array_fprint (stdout, lem->rule.vars, "vars");
#endif
}


/**
 * @brief Adds to (a copy of) @p pvars, the destination vars in @p pvars.
 */
void
noll_lemma_clone_pending (noll_lemma_t * lem, const noll_pred_t * pred)
{
  assert (lem != NULL);

  /// lem->rule.vars has already a copy of @p pred->def->vars

  /// duplicate only "pending" parameters
  for (uint_t pi = 0; pi < pred->def->fargs; pi++)
    {
      uid_t kind = noll_vector_at (pred->typ->argkind, pi);
      if ((kind < NOLL_ATYP_LPENDING) || (kind > NOLL_ATYP_IPENDING))
        continue;

      noll_var_t *vi = noll_var_copy (noll_vector_at (pred->def->vars, pi + 1));        // shift for 'nil'
      char *nname =
        (char *) malloc (sizeof (char) * (strlen (vi->vname) + 3));
      snprintf (nname, strlen (vi->vname) + 3, "%s_%d", vi->vname, pi); // TODO: be more robust
      free (vi->vname);
      vi->vname = nname;
      noll_var_array_push (lem->rule.vars, vi);
    }
#ifndef NDEBUG
  fprintf (stdout, "\nlemma_clone_lvars: (%d) ", pred->def->fargs);
  noll_var_array_fprint (stdout, pred->def->vars, "\n\tpvars");
  noll_var_array_fprint (stdout, lem->rule.vars, "\n\tlemma.vars");
#endif
}

/**
 * @brief Build the lemma for
 *  @p pid_part(E,r1,B,M,b1,d1,d) /\ r1=nil /\ M=emptybag /\ d1=0 
 *        => @p pid_base(E,M,B,d)
 */
noll_lemma_t *
noll_lemma_new_spec_nil (uid_t pid_base, uid_t pid_part)
{
  assert (pid_base != UNDEFINED_ID);
  assert (pid_part != UNDEFINED_ID);

  const noll_pred_t *pred_base = noll_pred_getpred (pid_base);
  const noll_pred_t *pred_part = noll_pred_getpred (pid_part);
  uint_t fargs_base = pred_base->def->fargs;
  uint_t fargs_part = pred_part->def->fargs;

  noll_lemma_t *lem1 = noll_lemma_new (pid_base);
  lem1->kind = NOLL_LEMMA_INSTANCE;
  // add the pending parameters of pred_part
  noll_lemma_clone_pending (lem1, pred_part);
  lem1->rule.pure = noll_pure_new (noll_vector_size (lem1->rule.vars));
  assert ((fargs_base + 1) <= fargs_part);
  // push equalities for the other parameters
  for (uint_t i = fargs_base + 1; i <= fargs_part; i++)
    {
      noll_type_t *typ_vi = noll_var_type (lem1->rule.vars, i);
      assert (typ_vi != NULL);
      if (typ_vi->kind == NOLL_TYP_RECORD)
        {                       // push (always) r1 (id fargs_base) = nil (id 0)
          noll_pure_add_eq (lem1->rule.pure, i, 0);
          continue;
        }
      noll_dform_t *df = noll_dform_new ();
      if (typ_vi->kind == NOLL_TYP_BAGINT)
        {                       // push b1 = emptybag
          noll_dterm_t *dt_b1 = noll_dterm_new ();
          dt_b1->kind = NOLL_DATA_VAR;
          dt_b1->typ = NOLL_TYP_BAGINT;
          dt_b1->p.sid = i;
          noll_dterm_t *dt_eb = noll_dterm_new ();
          dt_eb->kind = NOLL_DATA_EMPTYBAG;
          dt_eb->typ = NOLL_TYP_BAGINT;

          df->kind = NOLL_DATA_EQ;
          df->typ = NOLL_TYP_BAGINT;
          if (df->p.targs == NULL)
            df->p.targs = noll_dterm_array_new ();
          noll_dterm_array_push (df->p.targs, dt_b1);
          noll_dterm_array_push (df->p.targs, dt_eb);
          noll_pure_add_dform (lem1->rule.pure, df);

        }
      else if (typ_vi->kind == NOLL_TYP_INT)
        {                       // push i1 = 0
          noll_dterm_t *dt_i1 = noll_dterm_new ();
          dt_i1->kind = NOLL_DATA_VAR;
          dt_i1->typ = NOLL_TYP_INT;
          dt_i1->p.sid = i;
          noll_dterm_t *dt_0 = noll_dterm_new ();
          dt_0->kind = NOLL_DATA_INT;
          dt_0->typ = NOLL_TYP_INT;
          dt_0->p.value = 0l;

          df->kind = NOLL_DATA_EQ;
          df->typ = NOLL_TYP_INT;
          if (df->p.targs == NULL)
            df->p.targs = noll_dterm_array_new ();
          noll_dterm_array_push (df->p.targs, dt_i1);
          noll_dterm_array_push (df->p.targs, dt_0);
          noll_pure_add_dform (lem1->rule.pure, df);
        }
      else
        {
          NOLL_DEBUG
            ("lemma_spec_nil: incorrect type of the additional parameter");
        }
    }

  lem1->rule.nst = NULL;
  lem1->rule.rec = noll_space_new ();
  lem1->rule.rec->kind = NOLL_SPACE_SSEP;
  lem1->rule.rec->is_precise = true;
  lem1->rule.rec->m.sep = noll_space_array_new ();
  noll_space_array_reserve (lem1->rule.rec->m.sep, 1);

  /// build @p pid_part(E,r1,B,M,b1,d1,d)
  noll_space_t *p1 = noll_space_new ();
  p1->kind = NOLL_SPACE_LS;
  p1->is_precise = true;
  p1->m.ls.pid = pid_part;
  assert (p1->m.ls.pid != UNDEFINED_ID);
  p1->m.ls.is_loop = false;
  p1->m.ls.sid = UNDEFINED_ID;
  p1->m.ls.args = noll_uid_array_new ();
  noll_uid_array_reserve (p1->m.ls.args, fargs_part);
  /// copy source and border but 
  /// change the "pending" parameters, if any
  for (uint_t posb = 0, posp = 0; (posb + posp) < fargs_part;)
    {
      uid_t kind = noll_vector_at (pred_part->typ->argkind, (posb + posp));
      if ((kind >= NOLL_ATYP_LPENDING) && (kind <= NOLL_ATYP_IPENDING))
        {
          noll_uid_array_push (p1->m.ls.args, fargs_base + posp + 1);
          posp++;
        }
      else
        {
          noll_uid_array_push (p1->m.ls.args, posb + 1);
          posb++;
        }
    }
  noll_space_array_push (lem1->rule.rec->m.sep, p1);

  return lem1;

}

/**
 * @brief Build the lemma for
 *  @p pid(E,E',B,M,M',d,d',dB) * @p pid(E',F,B,M',N,d',z,dB) 
 *        => @p pid(E,F,B,M,N,d,z,dB)
 */
noll_lemma_t *
noll_lemma_new_comp_1 (uid_t pid)
{
  assert (pid != UNDEFINED_ID);

  const noll_pred_t *pred = noll_pred_getpred (pid);
  uint_t fargs = pred->def->fargs;

  noll_lemma_t *lem2 = noll_lemma_new (pid);
  lem2->kind = NOLL_LEMMA_COMP_1;
  // adds to pred->def->vars the copy of the "pending" parameters
  noll_lemma_clone_pending (lem2, pred);
  uint_t largs = noll_vector_size (lem2->rule.vars);
  lem2->rule.pure = NULL;       // no constraint
  lem2->rule.nst = NULL;        // no constraint
  noll_space_t *rec2 = noll_space_new ();
  rec2->kind = NOLL_SPACE_SSEP;
  rec2->is_precise = true;
  rec2->m.sep = noll_space_array_new ();
  noll_space_array_reserve (rec2->m.sep, 2);

  /// Warning: first push predicate from E, then the other

  /// push @p pid(E,E',B,M,M',d,d',dB) in the "recursive" part
  noll_space_t *call1 = noll_space_new ();
  call1->kind = NOLL_SPACE_LS;
  call1->is_precise = true;
  call1->m.ls.pid = pid;
  assert (call1->m.ls.pid != UNDEFINED_ID);
  call1->m.ls.is_loop = false;
  call1->m.ls.sid = UNDEFINED_ID;
  call1->m.ls.args = noll_uid_array_new ();
  // copy source and border but 
  // change the other "pending" parameters, if any
  for (uint_t pos = 0, posp = 0; pos < fargs; pos++)
    {
      uid_t kind = noll_vector_at (pred->typ->argkind, pos);
      if ((kind >= NOLL_ATYP_LPENDING) && (kind <= NOLL_ATYP_IPENDING))
        {
          noll_uid_array_push (call1->m.ls.args, fargs + posp + 1);
          posp++;
        }
      else
        noll_uid_array_push (call1->m.ls.args, pos + 1);
    }
  noll_space_array_push (rec2->m.sep, call1);

  /// push @p pid(E',F,B,M',N,d',z,dB) in the "recursive" part
  noll_space_t *call2 = noll_space_new ();
  call2->kind = NOLL_SPACE_LS;
  call2->is_precise = true;
  call2->m.ls.pid = pid;
  assert (call2->m.ls.pid != UNDEFINED_ID);
  call2->m.ls.is_loop = false;
  call2->m.ls.sid = UNDEFINED_ID;
  call2->m.ls.args = noll_uid_array_new ();
  // copy destination and border but 
  // change the "source" parameters
  for (uint_t pos = 0, posp = 0; pos < fargs; pos++)
    {
      uid_t kind = noll_vector_at (pred->typ->argkind, pos);
      if (kind <= NOLL_ATYP_IROOT)
        {
          noll_uid_array_push (call2->m.ls.args, fargs + posp + 1);
          ++posp;
        }
      else
        noll_uid_array_push (call2->m.ls.args, pos + 1);
    }
  noll_space_array_push (rec2->m.sep, call2);
  lem2->rule.rec = rec2;

  return lem2;
}

/**
 * @brief Build the lemma for
 *  @p pid_part(E,r1,B,M,b1,d1,d) * @p pid_base (r1,b1,d1,d) 
 *        => @p pid_base(E,M,B,d)
 */
noll_lemma_t *
noll_lemma_new_comp_2 (uid_t pid_base, uid_t pid_part)
{
  assert (pid_base != UNDEFINED_ID);
  assert (pid_part != UNDEFINED_ID);

  const noll_pred_t *pred_base = noll_pred_getpred (pid_base);
  const noll_pred_t *pred_part = noll_pred_getpred (pid_part);

  noll_lemma_t *lem2 = noll_lemma_new (pid_base);
  lem2->kind = NOLL_LEMMA_COMP_2;
  // adds to pred_base->def->vars the additional parameters of pred_part->def->vars
  noll_lemma_add_lvars (lem2, pred_base->def->vars, pred_base->def->fargs,
                        pred_part->def->vars, pred_part->def->fargs);
  lem2->rule.pure = NULL;       // no constraint
  lem2->rule.nst = NULL;        // no constraint
  noll_space_t *rec2 = noll_space_new ();
  rec2->kind = NOLL_SPACE_SSEP;
  rec2->is_precise = true;
  rec2->m.sep = noll_space_array_new ();
  noll_space_array_reserve (rec2->m.sep, 2);

  uint_t fargs_base = pred_base->def->fargs;
  uint_t fargs_part = pred_part->def->fargs;
  assert ((fargs_base + 1) <= fargs_part);

  /// Warning: first push predicate from E, then the other

  /// build @p pid_part(E,r1,B,M,b1,d1,d)  
  noll_space_t *p1 = noll_space_new ();
  p1->kind = NOLL_SPACE_LS;
  p1->is_precise = true;
  p1->m.ls.pid = pid_part;
  assert (p1->m.ls.pid != UNDEFINED_ID);
  p1->m.ls.is_loop = false;
  p1->m.ls.sid = UNDEFINED_ID;
  p1->m.ls.args = noll_uid_array_new ();
  // copy source and border but 
  // change the "pending" parameters, if any
  for (uint_t posb = 0, posp = 0; (posb + posp) < fargs_part;)
    {
      uint_t pos = posb + posp;
      uid_t kind = noll_vector_at (pred_part->typ->argkind, posb + posp);
      if ((kind >= NOLL_ATYP_LPENDING) && (kind <= NOLL_ATYP_IPENDING))
        {
          noll_uid_array_push (p1->m.ls.args, fargs_base + posp + 1);
          ++posp;
        }
      else
        {
          noll_uid_array_push (p1->m.ls.args, posb + 1);
          posb++;
        }
    }
  /// push it in the "recursive" part
  noll_space_array_push (rec2->m.sep, p1);

  /// build @p pid_base (r1,b1,d1,d)
  noll_space_t *p2 = noll_space_new ();
  p2->kind = NOLL_SPACE_LS;
  p2->is_precise = true;
  p2->m.ls.pid = pid_base;
  assert (p2->m.ls.pid != UNDEFINED_ID);
  p2->m.ls.is_loop = false;
  p2->m.ls.sid = UNDEFINED_ID;
  p2->m.ls.args = noll_uid_array_new ();
  // change the source arguments
  for (uint_t pos = 0; pos < fargs_base; pos++)
    {
      uid_t kind = noll_vector_at (pred_base->typ->argkind, pos);
      if (kind <= NOLL_ATYP_IROOT)
        noll_uid_array_push (p2->m.ls.args, fargs_base + pos + 1);
      else
        noll_uid_array_push (p2->m.ls.args, pos + 1);
    }
  /// push it in the "recursive" part
  noll_space_array_push (rec2->m.sep, p2);
  lem2->rule.rec = rec2;
  return lem2;
}


// zhilin: compute stronger lemma P'(E,F,M1,B1,M2,B2) => P(E,F,M1,B1,M2,B2)
noll_lemma_t *
noll_lemma_new_comp_3 (uid_t pid_part_str, uid_t pid_part)
{
  assert (pid_part_str != UNDEFINED_ID);
  assert (pid_part != UNDEFINED_ID);

  const noll_pred_t *pred_part_str = noll_pred_getpred (pid_part_str);
  const noll_pred_t *pred_part = noll_pred_getpred (pid_part);

  noll_lemma_t *lem2 = noll_lemma_new (pid_part);
  lem2->kind = NOLL_LEMMA_STRONGER;
  lem2->rule.pure = NULL;       // no constraint
  lem2->rule.nst = NULL;        // no constraint

  noll_space_t *rec2 = noll_space_new ();
  rec2->kind = NOLL_SPACE_SSEP;
  rec2->is_precise = true;
  rec2->m.sep = noll_space_array_new ();
  noll_space_array_reserve (rec2->m.sep, 1);

  uint_t fargs_part_str = pred_part_str->def->fargs;
  uint_t fargs_part = pred_part->def->fargs;
  assert (fargs_part_str == fargs_part);

  // build P'(E,F,M1,B1,M2,B2)
  noll_space_t *p1 = noll_space_new ();
  p1->kind = NOLL_SPACE_LS;
  p1->is_precise = true;
  p1->m.ls.pid = pid_part_str;
  assert (p1->m.ls.pid != UNDEFINED_ID);
  p1->m.ls.is_loop = false;
  p1->m.ls.sid = UNDEFINED_ID;
  p1->m.ls.args = noll_uid_array_new ();

  // copy the parameters of P, which are already in lem2, to P'
  for (uint_t pos = 0; pos < fargs_part;)
    {
      noll_uid_array_push (p1->m.ls.args, pos + 1);
      pos++;
    }

  noll_space_array_push (rec2->m.sep, p1);
  lem2->rule.rec = rec2;
  return lem2;
}



/** zhilin:
 * @brief Build the lemma for
 *  @p pid_hole_strong(E,E',B,M,M',d,d',dB) * @p pid_hole(E',F,B,M',N,d',z,dB)
 *        => @p pid_hole(E,F,B,M,N,d,z,dB)
 */

noll_lemma_t *
noll_lemma_new_comp_4 (uid_t pid_hole_strong, uid_t pid_hole)
{
  assert (pid_hole != UNDEFINED_ID);
  assert (pid_hole_strong != UNDEFINED_ID);

  const noll_pred_t *pred_hole = noll_pred_getpred (pid_hole);
  uint_t fargs_hole = pred_hole->def->fargs;

  const noll_pred_t *pred_hole_strong = noll_pred_getpred (pid_hole_strong);
  uint_t fargs_hole_strong = pred_hole_strong->def->fargs;

  assert (fargs_hole == fargs_hole_strong);

  noll_lemma_t *lem2 = noll_lemma_new (pid_hole);
  lem2->kind = NOLL_LEMMA_COMP_1S;
  // adds to pred_hole->def->vars the copy of the "pending" parameters
  noll_lemma_clone_pending (lem2, pred_hole);
  uint_t largs = noll_vector_size (lem2->rule.vars);
  lem2->rule.pure = NULL;       // no constraint
  lem2->rule.nst = NULL;        // no constraint
  noll_space_t *rec2 = noll_space_new ();
  rec2->kind = NOLL_SPACE_SSEP;
  rec2->is_precise = true;
  rec2->m.sep = noll_space_array_new ();
  noll_space_array_reserve (rec2->m.sep, 2);

  /// Warning: first push predicate from E, then the other

  /// push @p pid_hole_strong(E,E',B,M,M',d,d',dB) in the "recursive" part
  noll_space_t *call1 = noll_space_new ();
  call1->kind = NOLL_SPACE_LS;
  call1->is_precise = true;
  call1->m.ls.pid = pid_hole_strong;
  assert (call1->m.ls.pid != UNDEFINED_ID);
  call1->m.ls.is_loop = false;
  call1->m.ls.sid = UNDEFINED_ID;
  call1->m.ls.args = noll_uid_array_new ();
  // copy source and border but
  // change the other "pending" parameters, if any
  for (uint_t pos = 0, posp = 0; pos < fargs_hole; pos++)
    {
      uid_t kind = noll_vector_at (pred_hole->typ->argkind, pos);
      if ((kind >= NOLL_ATYP_LPENDING) && (kind <= NOLL_ATYP_IPENDING))
        {
          noll_uid_array_push (call1->m.ls.args, fargs_hole + posp + 1);
          posp++;
        }
      else
        noll_uid_array_push (call1->m.ls.args, pos + 1);
    }
  noll_space_array_push (rec2->m.sep, call1);

  /// push @p pid_hole(E',F,B,M',N,d',z,dB) in the "recursive" part
  noll_space_t *call2 = noll_space_new ();
  call2->kind = NOLL_SPACE_LS;
  call2->is_precise = true;
  call2->m.ls.pid = pid_hole;
  assert (call2->m.ls.pid != UNDEFINED_ID);
  call2->m.ls.is_loop = false;
  call2->m.ls.sid = UNDEFINED_ID;
  call2->m.ls.args = noll_uid_array_new ();
  // copy destination and border but
  // change the "source" parameters
  for (uint_t pos = 0, posp = 0; pos < fargs_hole; pos++)
    {
      uid_t kind = noll_vector_at (pred_hole->typ->argkind, pos);
      if (kind <= NOLL_ATYP_IROOT)
        {
          noll_uid_array_push (call2->m.ls.args, fargs_hole + posp + 1);
          ++posp;
        }
      else
        noll_uid_array_push (call2->m.ls.args, pos + 1);
    }
  noll_space_array_push (rec2->m.sep, call2);
  lem2->rule.rec = rec2;

  return lem2;
}

/**
 * @brief Return the set of lemma for the predicate ls(eg).
 */
noll_lemma_array *
noll_lemma_init_lseg (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 1);

  /// generate composition lemma for lseg
  noll_lemma_t *lem = noll_lemma_new_comp_1 (pid);
  // push lemma
  noll_lemma_array_push (res, lem);
  return res;
}

/**
 * @brief Return the set of lemma for the predicate list(E).
 */
noll_lemma_array *
noll_lemma_init_list (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 2);

  // TODO: find the "partial" RD of pid using typing
  uid_t pid_lsh = noll_pred_array_find ("ls");
  assert (pid_lsh != UNDEFINED_ID);

  /// first lemma:
  ///   lshole(E,r1) /\ r1=nil => list(E)
  noll_lemma_t *lem1 = noll_lemma_new_spec_nil (pid, pid_lsh);
  // push lemma
  noll_lemma_array_push (res, lem1);

  /// second lemma:
  ///   lshole(E,r1) * list(r1) => list(E)
  noll_lemma_t *lem2 = noll_lemma_new_comp_2 (pid, pid_lsh);
  // push lemma
  noll_lemma_array_push (res, lem2);

  return res;
}

/**
 * @brief Return the set of lemma for the predicate avl(E,M,H).
 * zhilin: add the lemma ubavlhole * avl => avl
 */
noll_lemma_array *
noll_lemma_init_avl (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 4);

  // TODO: find the "partial" RD of pid using typing
  uid_t pid_avlh = noll_pred_array_find ("avlhole");
  assert (pid_avlh != UNDEFINED_ID);

  /// first lemma:
  ///   avlhole(E,r1,M,b1,H,h1) /\ r1=nil /\ b1=emptybag /\ h1=0 => avl(E,M,H)
  noll_lemma_t *lem1 = noll_lemma_new_spec_nil (pid, pid_avlh);
  // push lemma
  noll_lemma_array_push (res, lem1);

  /// second lemma:
  ///   avlhole(E,r1,M,b1,H,h1) * avl(r1,b1,h1) => avl(E,M,H)
  noll_lemma_t *lem2 = noll_lemma_new_comp_2 (pid, pid_avlh);
  // push lemma
  noll_lemma_array_push (res, lem2);

  /// zhilin: third lemma:
  ///   bavlhole(E,r1,M,b1,H,h1) * avl(r1,b1,h1) => avl(E,M,H)
  uid_t pid_bavlh = noll_pred_array_find ("bavlhole");
  assert (pid_bavlh != UNDEFINED_ID);
  noll_lemma_t *lem3 = noll_lemma_new_comp_2 (pid, pid_bavlh);
  lem3->kind = NOLL_LEMMA_COMP_2S;      /// ms: to identify stronger + comp
  // push lemma
  noll_lemma_array_push (res, lem3);

  /// zhilin: third lemma:
  ///   ubavlhole(E,r1,M,b1,H,h1) * avl(r1,b1,h1) => avl(E,M,H)
  uid_t pid_ubavlh = noll_pred_array_find ("ubavlhole");
  assert (pid_ubavlh != UNDEFINED_ID);
  noll_lemma_t *lem4 = noll_lemma_new_comp_2 (pid, pid_ubavlh);
  lem4->kind = NOLL_LEMMA_COMP_2S;      /// ms: to identify stronger + comp
  // push lemma
  noll_lemma_array_push (res, lem4);

  return res;
}

/**
 * @brief Return the set of lemma for the predicate avlh(ole).
 * zhilin: add the stronger lemma for avlhole.
 */
noll_lemma_array *
noll_lemma_init_avlhole (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 3);

  /// first lemma: generate composition lemma for avlhole
  noll_lemma_t *lem1 = noll_lemma_new_comp_1 (pid);
  // push lemma
  noll_lemma_array_push (res, lem1);

  /// second lemma: stronger lemma:
  ///   bavlhole(...) => avlhole(...)
  uid_t pid_bavlh = noll_pred_array_find ("bavlhole");
  assert (pid_bavlh != UNDEFINED_ID);
  noll_lemma_t *lem2 = noll_lemma_new_comp_3 (pid_bavlh, pid);
  // push lemma
  noll_lemma_array_push (res, lem2);

  /// third lemma: stronger lemma:
  ///   ubavlhole(...) => avlhole(...)
  uid_t pid_ubavlh = noll_pred_array_find ("ubavlhole");
  assert (pid_ubavlh != UNDEFINED_ID);
  noll_lemma_t *lem3 = noll_lemma_new_comp_3 (pid_ubavlh, pid);
  // push lemma
  noll_lemma_array_push (res, lem3);

  return res;
}


/**
 * @brief Return the set of lemma for the predicate rbt(E,M,H).
 * zhilin: add the lemma brrbtlhole * rbt => rbt and rbrbtlhole * rbt => rbt
 */
noll_lemma_array *
noll_lemma_init_rbt (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 4);

  // TODO: find the "partial" RD of pid using typing
  uid_t pid_rbth = noll_pred_array_find ("rbthole");
  assert (pid_rbth != UNDEFINED_ID);

  /// first lemma:
  ///   rbthole(E,r1,M,b1,H,h1) /\ r1=nil /\ b1=emptybag /\ h1=0 => rbt(E,M,H)
  noll_lemma_t *lem1 = noll_lemma_new_spec_nil (pid, pid_rbth);
  // push lemma
  noll_lemma_array_push (res, lem1);

  /// second lemma:
  ///   rbthole(E,r1,M,b1,H,h1) * rbt(r1,b1,h1) => rbt(E,M,H)
  noll_lemma_t *lem2 = noll_lemma_new_comp_2 (pid, pid_rbth);
  // push lemma
  noll_lemma_array_push (res, lem2);

  /// zhilin: third lemma:
  ///   brrbthole(E,r1,M,b1,H,h1) * rbt(r1,b1,h1) => rbt(E,M,H)
  uid_t pid_brrbth = noll_pred_array_find ("brrbthole");
  if (pid_brrbth != UNDEFINED_ID)
    {
      noll_lemma_t *lem3 = noll_lemma_new_comp_2 (pid, pid_brrbth);
      lem3->kind = NOLL_LEMMA_COMP_2S;
      // push lemma
      noll_lemma_array_push (res, lem3);
    }

  /// zhilin: fourth lemma:
  ///   brrbthole(E,r1,M,b1,H,h1) * rbt(r1,b1,h1) => rbt(E,M,H)
  uid_t pid_rbrbth = noll_pred_array_find ("rbrbthole");
  if (pid_rbrbth != UNDEFINED_ID)
    {
      noll_lemma_t *lem4 = noll_lemma_new_comp_2 (pid, pid_rbrbth);
      lem4->kind = NOLL_LEMMA_COMP_2S;
      // push lemma
      noll_lemma_array_push (res, lem4);
    }

  return res;
}

/**
 * @brief Return the set of lemma for the predicate rbth(ole).
 * zhilin: add the stronger lemma for rbthole.
 */
noll_lemma_array *
noll_lemma_init_rbthole (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 5);

  /// first lemma: generate composition lemma for bsthole
  noll_lemma_t *lem1 = noll_lemma_new_comp_1 (pid);
  // push lemma
  noll_lemma_array_push (res, lem1);

  uid_t pid_brrbth = noll_pred_array_find ("brrbthole");
  if (pid_brrbth != UNDEFINED_ID)
    {
      /// second lemma: stronger lemma:
      ///   brrbthole(...) => rbthole(...)
      noll_lemma_t *lem2 = noll_lemma_new_comp_3 (pid_brrbth, pid);
      // push lemma
      noll_lemma_array_push (res, lem2);

      /// fifth lemma:
      ///   brrbthole(...) * rbthole => rbthole(...)
      noll_lemma_t *lem5 = noll_lemma_new_comp_4 (pid_brrbth, pid);
      lem5->kind = NOLL_LEMMA_COMP_1S;
      // push lemma
      noll_lemma_array_push (res, lem5);
    }

  uid_t pid_rbrbth = noll_pred_array_find ("rbrbthole");
  if (pid_rbrbth != UNDEFINED_ID)
    {
      /// third lemma: stronger lemma:
      ///   rbrbthole(...) => rbthole(...)
      noll_lemma_t *lem3 = noll_lemma_new_comp_3 (pid_rbrbth, pid);
      // push lemma
      noll_lemma_array_push (res, lem3);

      /// fourth lemma:
      ///   rbrbthole(...) * rbthole => rbthole(...)
      noll_lemma_t *lem4 = noll_lemma_new_comp_4 (pid_rbrbth, pid);
      lem4->kind = NOLL_LEMMA_COMP_1S;
      // push lemma
      noll_lemma_array_push (res, lem4);
    }

  return res;
}


/**
 * @brief Return the set of lemma for the predicate bst.
 */
noll_lemma_array *
noll_lemma_init_bst (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 2);

  // TODO: find the "partial" RD of pid using typing
  uid_t pid_bsth = noll_pred_array_find ("bsthole");
  assert (pid_bsth != UNDEFINED_ID);

  /// first lemma:
  ///   bsthole(E,r1,M,b1) /\ r1=nil /\ b1=emptybag => bst(E,M)
  noll_lemma_t *lem1 = noll_lemma_new_spec_nil (pid, pid_bsth);
  // push lemma
  noll_lemma_array_push (res, lem1);

  /// second lemma:
  ///   bsthole(E,r1,M,b1) * bst(r1,b1) => bst(E,M)
  noll_lemma_t *lem2 = noll_lemma_new_comp_2 (pid, pid_bsth);
  // push lemma
  noll_lemma_array_push (res, lem2);

  return res;
}

/**
 * @brief Return the set of lemma for the predicate bsth(ole).
 */
noll_lemma_array *
noll_lemma_init_bsthole (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 1);

  /// generate composition lemma for bsthole
  noll_lemma_t *lem = noll_lemma_new_comp_1 (pid);
  // push lemma
  noll_lemma_array_push (res, lem);
  return res;
}


/**
 * @brief Return the set of lemma for the predicate slist.
 */
noll_lemma_array *
noll_lemma_init_slist (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 2);

  // TODO: find the "partial" RD of pid using typing
  uid_t pid_sls = noll_pred_array_find ("sls");
  assert (pid_sls != UNDEFINED_ID);

  /// first lemma:
  ///   sls(E,r1,M,b1) /\ r1=nil /\ b1=emptybag => slist(E,M)
  noll_lemma_t *lem1 = noll_lemma_new_spec_nil (pid, pid_sls);
  // push lemma
  noll_lemma_array_push (res, lem1);

  /// second lemma:
  ///   sls(E,r1,M,b1) * slist(r1,b1) => slist(E,M)
  noll_lemma_t *lem2 = noll_lemma_new_comp_2 (pid, pid_sls);
  // push lemma
  noll_lemma_array_push (res, lem2);

  return res;
}

/**
 * @brief Return the set of lemma for the predicate sls(eg).
 */
noll_lemma_array *
noll_lemma_init_slseg (uint_t pid)
{
  noll_lemma_array *res = noll_lemma_array_new ();
  noll_lemma_array_reserve (res, 1);

  /// generate composition lemma for bsthole
  noll_lemma_t *lem = noll_lemma_new_comp_1 (pid);
  // push lemma
  noll_lemma_array_push (res, lem);
  return res;
}

/**
 * @brief Return the set of lemma for the predicate @p pid.
 */
noll_lemma_array *
noll_lemma_init_pred (uid_t pid)
{
  assert (pid != UNDEFINED_ID);

  if (lemma_array == NULL)
    noll_lemma_init ();

  noll_lemma_array *lemma_pid = noll_lemma_getpred (pid);

  if (lemma_pid != NULL)
    return lemma_pid;

  noll_lemma_array *res = NULL;

  // zhilin: add stronger lemma for avl and avlhole, rbt and rbthole
  if (!strcmp ("avl", noll_pred_name (pid)))
    {
      res = noll_lemma_init_avl (pid);
    }
  else if (!strcmp ("avlhole", noll_pred_name (pid)))
    {
      res = noll_lemma_init_avlhole (pid);
    }
  else if (!strcmp ("rbt", noll_pred_name (pid)))
    {
      res = noll_lemma_init_rbt (pid);
    }
  else if (!strcmp ("rbthole", noll_pred_name (pid)))
    {
      res = noll_lemma_init_rbthole (pid);
    }
  else
    {
      res = noll_lemma_array_new ();
      noll_lemma_array_reserve (res, 2);
      const noll_pred_t *pred = noll_pred_getpred (pid);

      // WARNING: we suppose that RD set is compositional
      // for a full RD, the compositional RD is pid + 1
      if (pred->typ->isUnaryLoc == true)
        {
          /// if unary then generate comp_2 and spec_nil
          // TODO: find the "partial" RD of pid using typing
          uid_t pid_hole = pid + 1;
          assert (pid_hole < noll_vector_size (preds_array));

          /// first lemma:
          ///   phole(E,r1,M,b1,H,h1) /\ r1=nil /\ b1=emptybag /\ h1=0 => p(E,M,H)
          noll_lemma_t *lem1 = noll_lemma_new_spec_nil (pid, pid_hole);
          noll_lemma_array_push (res, lem1);

          /// second lemma:
          ///   phole(E,r1,M,b1,H,h1) * p(r1,b1,h1) => p(E,M,H)
          noll_lemma_t *lem2 = noll_lemma_new_comp_2 (pid, pid_hole);
          noll_lemma_array_push (res, lem2);
        }
      else
        {
          /// otherwise generate comp_1
          noll_lemma_t *lem1 = noll_lemma_new_comp_1 (pid);
          noll_lemma_array_push (res, lem1);
        }
    }
  return res;
}

/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

/**
 * @brief Get the lemma associated with @p pid.
 */
noll_lemma_array *
noll_lemma_getpred (uid_t pid)
{
  assert (pid < noll_vector_size (preds_array));
  return lemma_array[pid];
}

/**
 * @brief Get the @p n-th space formula.
 */
noll_space_t *
noll_lemma_getspace (noll_lemma_t * l, uid_t n)
{
  if (2 <= n || n >= noll_vector_size (l->rule.rec->m.sep))
    return NULL;
  return noll_vector_at (l->rule.rec->m.sep, n);
}

/**
 * @brief Get the kind of lemma 
 */
noll_lemma_e
noll_lemma_get_kind (noll_lemma_t * l)
{
  if (l == NULL)
    return NOLL_LEMMA_OTHER;
  return l->kind;
}

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

/**
 * @brief Print the global array of lemmas.
 */
void
noll_lemma_array_fprint (FILE * f)
{
  assert (f != NULL);

  if (lemma_array == NULL)
    {
      fprintf (f, "(lemma_array) []");
      return;
    }
  for (uint_t pi = 0; pi < noll_vector_size (preds_array); pi++)
    {
      fprintf (f, "%s -> [", noll_pred_name (pi));
      noll_lemma_array *lem_pid = lemma_array[pi];
      if (lem_pid != NULL)
        {
          for (uint_t li = 0; li < noll_vector_size (lem_pid); li++)
            {
              noll_lemma_fprint (f, noll_vector_at (lem_pid, li));
              fprintf (f, "\n");
            }
        }
      fprintf (f, "\t]\n");
    }
}

void
noll_lemma_fprint (FILE * f, noll_lemma_t * l)
{
  assert (NULL != f);

  if (l == NULL)
    {
      fprintf (f, "(lemma) []");
      return;
    }
  const noll_pred_t *prhs = noll_pred_getpred (l->pid);
  fprintf (f, "(lemma) %s (", prhs->pname);
  noll_var_array_fprint (f, l->rule.vars, "all ");
  fprintf (f, ")\n <== \n");


  if (l->rule.pure != NULL)
    {
      noll_pure_fprint (f, l->rule.vars, l->rule.pure);
      fprintf (f, " & \n");
    }
  if (l->rule.nst != NULL)
    {
      noll_space_fprint (f, l->rule.vars, NULL, l->rule.nst);
      fprintf (f, " * \n");
    }
  if (l->rule.rec != NULL)
    {
      noll_space_fprint (f, l->rule.vars, NULL, l->rule.rec);
    }
}

/**
 * @brief Print the lemma kind.
 */
void
noll_lemma_kind_fprint (FILE * f, noll_lemma_e kind)
{
  assert (f != NULL);
  switch (kind)
    {
    case NOLL_LEMMA_COMP_1:
      fprintf (f, "COMPOSITION");
      break;
    case NOLL_LEMMA_COMP_1S:
      fprintf (f, "STRONGER + COMPOSITION");
      break;
    case NOLL_LEMMA_COMP_2:
      fprintf (f, "COMPLETION");
      break;
    case NOLL_LEMMA_COMP_2S:
      fprintf (f, "STRONGER + COMPLETION");
      break;
    case NOLL_LEMMA_INSTANCE:
      fprintf (f, "INSTANTIATION");
      break;
    case NOLL_LEMMA_STRONGER:
      fprintf (f, "STRONGER");
      break;
    default:
      fprintf (f, "UNKNOWN");
      break;
    }
}
