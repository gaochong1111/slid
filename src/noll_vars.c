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
 * Variables for NOLL.
 */

#include "noll_vars.h"

NOLL_VECTOR_DEFINE (noll_var_array, noll_var_t *);

/* ====================================================================== */
/* Constructors/destructors */

/* ====================================================================== */

noll_var_t *
noll_var_new (const char *name, noll_type_t * ty, noll_scope_e s)
{
  noll_var_t *v = (noll_var_t *) malloc (sizeof (noll_var_t));
  v->vname = strdup (name);
  v->vty = ty;
  v->scope = s;
  return v;
}

void
noll_var_free (noll_var_t * a)
{
  if (!a)
    return;
  if (a->vname)
    free (a->vname);
  if (a->vty)
    noll_type_free (a->vty);
  free (a);
}

noll_var_t *
noll_var_copy (noll_var_t * a)
{
  assert (a != NULL);
  noll_var_t *r = (noll_var_t *) malloc (sizeof (noll_var_t));
  r->vid = a->vid;
  r->vname = strdup (a->vname);
  r->vty = noll_type_clone (a->vty);
  r->scope = a->scope;
  return r;
}

noll_var_array *
noll_var_array_make (uid_t sz)
{
  noll_var_array *a = noll_var_array_new ();
  if (sz > 0)
    noll_var_array_reserve (a, sz);
  return a;
}

void
noll_var_register (noll_var_array * a, const char *name, noll_type_t * ty,
                   noll_scope_e scope)
{
  assert (NULL != ty);
  assert (noll_type_is_vartype (ty) == true);

  noll_var_t *v = noll_var_new (name, ty, scope);
  v->scope = scope;
  noll_var_array_push (a, v);
  v->vid = noll_vector_size (a) - 1;
  return;
}

uid_t
noll_var_array_find_local (noll_var_array * a, const char *name)
{
  if (a && (noll_vector_size (a) > 0))
    {
      uid_t sz = noll_vector_size (a);
      for (uid_t i = 0; i < sz; i++)
        if (noll_vector_at (a, i) && !strcmp (name,
                                              noll_vector_at (a, i)->vname))
          return i;
    }
  return UNDEFINED_ID;
}

/** Used to obtain the name of a variable from an identifier.
 * @param a   local environment, if NULL search in global environment
 * @param vid variable identifier
 */
char *
noll_var_name (noll_var_array * a, uid_t vid, noll_typ_t ty)
{
  if (&ty != &ty)
    {
      assert (0);               // just to avoid an "unused parameter warning"
    }

  if (a == NULL)
    return "unknown";
  if (vid == VNIL_ID)
    {
      return "nil";
    }
  if (vid >= noll_vector_size (a))
    {
      printf
        ("noll_var_name: called with identifier %d not in the local environment.\n",
         vid);
      return "unknown";
    }
  return (noll_vector_at (a, vid))->vname;
}


noll_type_t *
noll_var_type (noll_var_array * a, uid_t vid)
{
  assert (a);
  //if (vid == VNIL_ID)
  //  return NOLL_TYP_VOID;
  if (vid != VNIL_ID && vid >= noll_vector_size (a))
    {
      fprintf (stdout,
               "Error: incorrect id (%d > %d) for location variable.\n", vid,
               noll_vector_size (a));
      return NULL;
    }
  noll_var_t *v = noll_vector_at (a, vid);
  noll_type_t *ty = v->vty;
  return ty;
}

uid_t
noll_var_record (noll_var_array * a, uid_t vid)
{
  noll_type_t *ty = noll_var_type (a, vid);
  if ((ty == NULL) || (ty->kind != NOLL_TYP_RECORD) || (ty->args == NULL))
    {
      /// NEW: do not signal an error because of Int and BagInt types
      return UNDEFINED_ID;
    }
#ifndef NDEBUG
  //fprintf (stdout, "noll_var_record: var %s, tid = %d\n", v->vname, ty->kind);
  //fflush(stdout);
#endif
  uid_t tid = noll_vector_at (ty->args, 0);
  if ((tid >= noll_vector_size (records_array))
      || (noll_vector_at (records_array, tid) == NULL))
    {
      fprintf (stdout, "Unknown record type for location variable %d.\n",
               vid);
      return UNDEFINED_ID;
    }
  return tid;
}


void
noll_var_array_fprint (FILE * f, noll_var_array * a, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  fflush (f);
  if (!a)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uid_t length_a = noll_vector_size (a);
  for (uid_t i = 0; i < length_a; i++)
    {
      noll_var_t *vi = noll_vector_at (a, i);
      assert (vi != NULL);
      noll_type_t *ti = vi->vty;
      if (vi->scope == NOLL_SCOPE_LOCAL)
        fprintf (f, "?");
      else
        fprintf (f, " ");
      fprintf (f, "%s:", vi->vname);
      noll_type_fprint (f, ti);
      fprintf (f, ", ");
    }
  fprintf (f, " - ]");
  fflush (f);
}
