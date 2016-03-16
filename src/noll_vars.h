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

#ifndef _NOLL_VARS_H_
#define _NOLL_VARS_H_

#ifdef __cplusplus
extern "C"
{
#endif

#include <stdlib.h>
#include <limits.h>

#include "noll_types.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

#define VNIL_ID UNDEFINED_ID

/**
 * Visibility flag values
 */
  typedef enum
  {
    NOLL_SCOPE_LOCAL = 0, NOLL_SCOPE_GLOBAL, NOLL_SCOPE_OTHER
  } noll_scope_e;

/** Variable information for both locations and set of locations variables:
 * - the name of the variable in the program
 * - the type(s) of the variable
 * - flag for local or global
 */
  typedef struct noll_var_t
  {
    char *vname;                // declaration name
    uid_t vid;                  // variable identifier
    noll_type_t *vty;           // type
    noll_scope_e scope;         // visibility
  } noll_var_t;

/** Type of the global array of variables. */
    NOLL_VECTOR_DECLARE (noll_var_array, noll_var_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

/*
 * Global variables are stored within the formulae,
 * in fields lvars and svars of noll_form_t.
 * They have the flag scope set to NOLL_SCOPE_GLOBAL.
 */

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */
  noll_var_t *noll_var_new (const char *name, noll_type_t * vty,
                            noll_scope_e s);
/* Build a variable record. */
  void noll_var_free (noll_var_t * a);
/* Free a variable record. */
  noll_var_t *noll_var_copy (noll_var_t * a);
/* Makes a copy of the variable. */

  noll_var_array *noll_var_array_make (uint_t sz);
/* Allocate an array of size variables.
 The variables are initialized with NULL pointers. */

/* ====================================================================== */
/* Other methods */
/* ====================================================================== */

  void noll_var_register (noll_var_array * a, const char *name,
                          noll_type_t * ty, noll_scope_e s);
/* Add a variable declaration to the array a. */

  uint_t noll_var_array_find_local (noll_var_array * a, const char *name);
/* Search the position of the variable name in the local array a. */

  char *noll_var_name (noll_var_array * a, uid_t vid, noll_typ_t ty);
  uint_t noll_var_record (noll_var_array * a, uid_t vid);
  noll_type_t *noll_var_type (noll_var_array * a, uid_t vid);
/* Accessors */

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

  void noll_var_array_fprint (FILE * f, noll_var_array * a, const char *msg);
/* Print the array a. */

#ifdef __cplusplus
}
#endif

#endif                          /* _NOLL_VARS_H_ */
