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
 * Type system for NOLL.
 */

#include "noll_types.h"

NOLL_VECTOR_DEFINE (noll_uid_array, uid_t);

NOLL_VECTOR_DEFINE (noll_uint_array, uint_t);

NOLL_VECTOR_DEFINE (noll_type_array, noll_type_t *);

NOLL_VECTOR_DEFINE (noll_record_array, noll_record_t *);

NOLL_VECTOR_DEFINE (noll_field_array, noll_field_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_record_array *records_array;
noll_field_array *fields_array;

/* Initialize global arrays of records and fields */
void
noll_record_init ()
{
  records_array = noll_record_array_new ();
  noll_record_array_reserve (records_array, 4);

  /* initialize with void* */
  noll_record_register ("void");
}

void
noll_field_init ()
{
  fields_array = noll_field_array_new ();
  noll_field_array_reserve (fields_array, 4);
}

/* ====================================================================== */
/* Constructors/destructors */

/* ====================================================================== */

noll_record_t *
noll_record_new (const char *name, noll_uid_array * flds)
{
  noll_record_t *r = (noll_record_t *) malloc (sizeof (noll_record_t));
  r->name = strdup (name);
  if (flds != NULL)
    r->flds = flds;
  else
    r->flds = noll_uid_array_new ();
  // there shall be one cell to store the record identifier
  if (noll_vector_size (r->flds) < 1)
    noll_uid_array_reserve (r->flds, 1);
  return r;
}

/**
 * Register a record.
 * Warning: does not test that the name already exists !
 */
noll_type_t *
noll_record_register (const char *name)
{
  // type expression for the result
  noll_type_t *ty = noll_mk_type_record (UNDEFINED_ID);
  // build the record
  noll_record_t *r = noll_record_new (name, NULL);
  // add to the global array
  noll_record_array_push (records_array, r);
  r->rid = noll_vector_size (records_array) - 1;
  // the index of the added record is last element of the array
  noll_vector_at (ty->args, 0) = r->rid;
  return ty;
}

/**
 * Find a record using its name.
 * @return a type built with this record or NULL if not find
 */
noll_type_t *
noll_record_find (const char *name)
{
  noll_type_t *ty = NULL;
  for (uint_t i = 0; i < noll_vector_size (records_array); i++)
    {
      noll_record_t *r = noll_vector_at (records_array, i);
      if (strcmp (r->name, name) == 0)
        {
          ty = noll_mk_type_record (UNDEFINED_ID);
          noll_vector_at (ty->args, 0) = r->rid;
        }
    }
  return ty;
}

noll_field_t *
noll_field_new (const char *name, uid_t ty_src, uid_t ty_dst)
{
  noll_field_t *f = (noll_field_t *) malloc (sizeof (noll_field_t));
  f->name = strdup (name);
  f->src_r = ty_src;
  f->pto_r = ty_dst;
  f->pto_ty = (ty_dst == UNDEFINED_ID) ? NOLL_TYP_INT : NOLL_TYP_RECORD;
  return f;
}

noll_type_t *
noll_field_register (const char *name, noll_type_t * ty)
{
  // type expression for the result is ty
  // extract informations about the field
  uid_t src = UNDEFINED_ID;
  uid_t dst = UNDEFINED_ID;
  if (!ty || ty->kind != NOLL_TYP_FIELD || ty->args == NULL
      || (noll_vector_size (ty->args) != 2))
    {
      // TODO: make error message
      printf ("Field declaration `%s': typing error.\n", name);
      return NULL;
    }
  // set src and dest
  src = noll_is_record (noll_vector_at (ty->args, 0));
  dst = noll_is_record (noll_vector_at (ty->args, 1));
  // create the field
  noll_field_t *f = noll_field_new (name, src, dst);
  // push the field
  noll_field_array_push (fields_array, f);
  f->fid = noll_vector_size (fields_array) - 1;
  // register the field in the src set of fields
  noll_record_t *r_src = noll_vector_at (records_array, src);
  noll_uid_array_push (r_src->flds, f->fid);
  // set order/pid to max
  f->order = UNDEFINED_ID;
  f->pid = UNDEFINED_ID;

  return ty;
}

uid_t
noll_field_array_find (const char *name)
{
  uid_t sz = noll_vector_size (fields_array);
  for (uid_t i = 0; i < sz; i++)
    if (!strcmp (name, noll_field_name (i)))
      return i;
  return UNDEFINED_ID;
}

noll_type_t *
noll_mk_type_bool ()
{
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = NOLL_TYP_BOOL;
  ret->args = noll_uid_array_new ();
  return ret;
}

noll_type_t *
noll_mk_type_int ()
{
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = NOLL_TYP_INT;
  ret->args = noll_uid_array_new ();
  return ret;
}

noll_type_t *
noll_mk_type_bagint ()
{
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = NOLL_TYP_BAGINT;
  ret->args = noll_uid_array_new ();
  return ret;
}

noll_type_t *
noll_mk_type_field (noll_type_t * src, noll_type_t * dst)
{
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = NOLL_TYP_FIELD;
  ret->args = noll_uid_array_new ();
  noll_uid_array_reserve (ret->args, 2);
  noll_uid_array_push (ret->args, noll_type_get_record (src));
  noll_uid_array_push (ret->args, noll_type_get_record (dst));
  return ret;
}

noll_type_t *
noll_mk_type_record (uid_t rid)
{
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = NOLL_TYP_RECORD;
  ret->args = noll_uid_array_new ();
  noll_uid_array_reserve (ret->args, 1);
  noll_uid_array_push (ret->args, rid);
  return ret;
}

noll_type_t *
noll_mk_type_setloc ()
{
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = NOLL_TYP_SETLOC;
  ret->args = noll_uid_array_new ();
  return ret;
}

noll_type_t *
noll_mk_type_setref (uid_t ty)
{
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = NOLL_TYP_SETREF;
  ret->args = noll_uid_array_new ();
  noll_uid_array_reserve (ret->args, 1);
  noll_uid_array_push (ret->args, ty);
  return ret;
}

noll_type_t *
noll_mk_type_space ()
{
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = NOLL_TYP_SPACE;
  ret->args = noll_uid_array_new ();
  return ret;
}

noll_type_t *
noll_type_clone (noll_type_t * a)
{
  if (!a)
    return a;
  noll_type_t *ret = (noll_type_t *) malloc (sizeof (struct noll_type_t));
  ret->kind = a->kind;
  ret->args = noll_uid_array_new ();
  noll_uid_array_copy (ret->args, a->args);
  return ret;
}

void
noll_type_free (noll_type_t * a)
{
  if (!a)
    return;
  if (a->args)
    noll_uid_array_delete (a->args);
  free (a);
}

void
noll_type_fprint (FILE * f, noll_type_t * a)
{
  if (a == NULL)
    fprintf (f, "(null)");
  switch (a->kind)
    {
    case NOLL_TYP_BOOL:
      fprintf (f, "Bool");
      break;
    case NOLL_TYP_INT:
      fprintf (f, "Int");
      break;
    case NOLL_TYP_BAGINT:
      fprintf (f, "BagInt");
      break;
    case NOLL_TYP_RECORD:
      fprintf (f, "%s", noll_record_name (noll_vector_at (a->args, 0)));
      break;
    case NOLL_TYP_SETLOC:
      fprintf (f, "SetLoc");
      break;
    case NOLL_TYP_FIELD:
      fprintf (f, "Field");
      break;
    case NOLL_TYP_SETREF:
      fprintf (f, "SetRef");
      break;
    case NOLL_TYP_SPACE:
      fprintf (f, "Space");
      break;
    default:
      fprintf (f, "(unknown)");
      break;
    }
}

/* ====================================================================== */
/* Other methods */

/* ====================================================================== */

bool
noll_type_is_vartype (noll_type_t * t)
{
  assert (NULL != t);
  /// depends on logic  // TODO NEW
  if ((t->kind >= NOLL_TYP_INT) && (t->kind <= NOLL_TYP_SETLOC))
    return true;
  return false;
}

bool
noll_type_is_fldtype (noll_type_t * t)
{
  assert (NULL != t);
  /// depends on logic  // TODO NEW
  if ((t->kind == NOLL_TYP_INT) || (t->kind == NOLL_TYP_RECORD))
    return true;
  return false;
}

bool
noll_type_match (noll_type_t * fty, noll_type_t * aty)
{
  assert (fty != NULL);
#ifndef NDEBUG
  printf ("noll_type_match: fty=%d, atyp=%d\n",
          fty->kind, (aty == NULL) ? NOLL_TYP_VOID : aty->kind);
#endif
  bool res = true;
  if (aty == NULL)              /// void
    res = (fty->kind == NOLL_TYP_RECORD) ? true : false;
  else if ((aty->kind == NOLL_TYP_RECORD) && (fty->kind == NOLL_TYP_RECORD))
    {
      uid_t fty_r = noll_vector_at (fty->args, 0);
      uid_t aty_r = noll_vector_at (aty->args, 0);
#ifndef NDEBUG
      printf ("noll_type_match: fty=rec-%d, atyp=rec-%d\n", fty_r, aty_r);
#endif
      /// void is also encoded by aty_r == 0
      res = ((aty_r == NOLL_TYP_VOID) || (aty_r == fty_r)) ? true : false;
    }
  else
    res = (fty->kind == aty->kind) ? true : false;
  return res;
}

uid_t
noll_is_record (uid_t rid)
{
  return (rid < noll_vector_size (records_array)) ? rid : UNDEFINED_ID;
}

uid_t
noll_type_get_record (noll_type_t * ty)
{
  if (NULL == ty)
    return 0;                   /// void
  if (ty->kind == NOLL_TYP_RECORD)
    return noll_vector_at (ty->args, 0);
  return UNDEFINED_ID;
}

char *
noll_field_name (uid_t fid)
{
  if (fid >= noll_vector_size (fields_array))
    {
      printf
        ("noll_field_name: called with identifier %d not in the global environment.\n",
         fid);
      return "unknown";
    }
  return noll_vector_at (fields_array, fid)->name;
}

char *
noll_record_name (uid_t rid)
{
  if (rid >= noll_vector_size (records_array))
    {
      printf
        ("noll_record_name: called with identifier %d not in the global environment.\n",
         rid);
      return "unknown";
    }
  return noll_vector_at (records_array, rid)->name;
}

/**
 * Ordering using the ordering of predicates.
 */
bool
noll_field_lt (uid_t lhs, uid_t rhs)
{

  assert (lhs < noll_vector_size (fields_array));
  assert (rhs < noll_vector_size (fields_array));

  noll_field_t *fl = noll_vector_at (fields_array, lhs);
  noll_field_t *fr = noll_vector_at (fields_array, rhs);

  assert (fl->order != UNDEFINED_ID);
  assert (fr->order != UNDEFINED_ID);
  assert (fl->order != fr->order);

  return (fl->order < fr->order);
}


/* ====================================================================== */
/* Printing */
/* ====================================================================== */


void
noll_fields_array_fprint (FILE * f, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  if (!fields_array)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uint_t length = noll_vector_size (fields_array);
  for (uint_t i = 0; i < length; i++)
    {
      noll_field_t *fi = noll_vector_at (fields_array, i);
      fprintf (f, " %s:%s->%s (%d-th, in pid-%d),",
               fi->name, noll_record_name (fi->src_r),
               (fi->pto_ty == NOLL_TYP_RECORD) ?
               noll_record_name (fi->pto_r) : "data", fi->order, fi->pid);
    }
  fprintf (f, " - ]");
}

void
noll_records_array_fprint (FILE * f, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  if (!records_array)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uint_t length = noll_vector_size (records_array);
  for (uint_t i = 0; i < length; i++)
    {
      noll_record_t *ri = noll_vector_at (records_array, i);
      fprintf (f, " %s (", noll_record_name (i));
      if (!ri->flds)
        {
          fprintf (f, "null),");
          continue;
        }
      uint_t length_fld = noll_vector_size (ri->flds);
      for (uint_t j = 0; j < length_fld; j++)
        {
          fprintf (f, "%s;", noll_field_name (noll_vector_at (ri->flds, j)));
        }
      fprintf (f, "),");
    }
  fprintf (f, " - ]");
}
