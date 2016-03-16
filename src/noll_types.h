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

#ifndef _NOLL_TYPES_H_
#define _NOLL_TYPES_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "noll_vector.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Identifiers type */
  typedef uid_t uid_t;

/** Constant used to signal an undefined identifier */
#define UNDEFINED_ID UINT32_MAX

/** Vector of identifiers */
    NOLL_VECTOR_DECLARE (noll_uid_array, uid_t);

/** Vector of integers */
    NOLL_VECTOR_DECLARE (noll_uint_array, uint_t);

/** Basic types used in NOLL */
  typedef enum
  {
    NOLL_TYP_BOOL = 0,
    NOLL_TYP_INT,
    NOLL_TYP_BAGINT,
    NOLL_TYP_RECORD,
    NOLL_TYP_SETLOC,
    NOLL_TYP_FIELD,
    NOLL_TYP_SETREF,
    NOLL_TYP_SPACE,
    NOLL_TYP_OTHER
  } noll_typ_t;

/** Type expression.
 */
  typedef struct noll_type_t
  {
    noll_typ_t kind;
    noll_uid_array *args;       // type arguments, including the record index
  } noll_type_t;

/** Type of the global array of records. */
    NOLL_VECTOR_DECLARE (noll_type_array, noll_type_t *);

/** Record information:
 * - the name of the record declared in the program
 * - the list of reference fields
 */
  typedef struct noll_record_t
  {
    char *name;                 // declaration name
    uid_t rid;                  // record identifier, 0 for void*
    noll_uid_array *flds;       // fields of this record
  } noll_record_t;

#define NOLL_TYP_VOID 0

/** Type of the global array of records. */
    NOLL_VECTOR_DECLARE (noll_record_array, noll_record_t *);

/** Kind of fields wrt their use in predicate definitions.
 */
  typedef enum
  {
    NOLL_PFLD_NONE = 0,
    NOLL_PFLD_BCKBONE,          /* F^0 */
    NOLL_PFLD_INNER,            /* F^1 */
    NOLL_PFLD_NULL,             /* F^2 needed? */
    NOLL_PFLD_BORDER,           /* F^2 */
    NOLL_PFLD_NESTED,
    NOLL_PFLD_DATA
  } noll_field_e;

/** Field information:
 * - the name of the field declared in the program
 * - the source record
 * - the target record / UNDEFINED_ID for data fields
 */
  typedef struct noll_field_t
  {
    char *name;                 // declaration name
    uid_t fid;                  // field identifier
    uid_t src_r;                // identifier of the source record
    uid_t pto_r;                // identifier of the target record / or UNDEFINED_ID for data
    noll_typ_t pto_ty;          // kind of type for pto
    uid_t order;                // order number wrt use in predicates
    uid_t pid;                  // predicate where the fields is used in the matrix
    noll_field_e kind;          // kind of the field wrt predicate pid
  } noll_field_t;


/** Type of the global array of fields.
 */
    NOLL_VECTOR_DECLARE (noll_field_array, noll_field_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

  extern noll_record_array *records_array;
  extern noll_field_array *fields_array;

/* Initialize global arrays of records and fields */
  void noll_record_init (void);
  void noll_field_init (void);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

  noll_record_t *noll_record_new (const char *name, noll_uid_array * flds);
  noll_type_t *noll_record_register (const char *name);
/* Declares a record and put it in the global array.
 * Returns the entry in the global array.
 */
  noll_type_t *noll_record_find (const char *name);


  noll_field_t *noll_field_new (const char *name, uid_t ty_src, uid_t ty_dst);
// uid_t noll_field_array_add (const char* name, uid_t ty_src, uid_t ty_dst);
  noll_type_t *noll_field_register (const char *name, noll_type_t * t);
/* Declared a filed and put it in the global array. */
  uid_t noll_field_array_find (const char *name);
/* Returns the id of the field with the given name. */

  noll_type_t *noll_mk_type_bool (void);
  noll_type_t *noll_mk_type_int (void);
  noll_type_t *noll_mk_type_bagint (void);
  noll_type_t *noll_mk_type_field (noll_type_t * src, noll_type_t * dest);
  noll_type_t *noll_mk_type_record (uid_t rid);
  noll_type_t *noll_mk_type_setloc (void);
  noll_type_t *noll_mk_type_setref (uid_t ty);
  noll_type_t *noll_mk_type_space (void);
/* Constructors for the predefined types. */
  noll_type_t *noll_type_clone (noll_type_t * a);
  void noll_type_free (noll_type_t * a);
  void noll_type_fprint (FILE * f, noll_type_t * a);

/* ====================================================================== */
/* Other methods */
/* ====================================================================== */

  bool noll_type_is_vartype (noll_type_t * t);
/* True if type may be used for a variable */

  bool noll_type_is_fldtype (noll_type_t * t);
/* True if type may be used for co-domain of a field */

  bool noll_type_match (noll_type_t * fty, noll_type_t * aty);
/* True if a value of type @p aty may be assigned to @p fty */

  uid_t noll_is_record (uid_t rid);
/* Returns rid if the argument is a valid record index, otherwise UNDEFINED_ID */

  uid_t noll_type_get_record (noll_type_t * t);
/* Returns record identifier if the type is a record, otherwise UNDEFINED_ID */

// searching

// inserting

  char *noll_field_name (uid_t fid);
  char *noll_record_name (uid_t rid);
/* Accessors */

  bool noll_field_lt (uid_t lhs, uid_t rhs);
/* Ordering */

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

  void noll_fields_array_fprint (FILE * f, const char *msg);
  void noll_records_array_fprint (FILE * f, const char *msg);
/* Print the global arrays. */

#ifdef __cplusplus
}
#endif

#endif                          /* _NOL_TYPES_H_ */
