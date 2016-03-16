/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2012-2013                                               */
/*    LIAFA (University of Paris Diderot and CNRS)                        */
/*                                                                        */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 3.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 3.                  */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

#ifndef _NOLL2BOOL_H
#define _NOLL2BOOL_H

#include "noll_vars.h"
#include "noll_types.h"
#include "noll_form.h"
#include "noll_preds.h"

/* ====================================================================== */
/* Writing the boolean abstraction */
/* ====================================================================== */

void write_bool_abstr (noll_form_t * form, char *fname, int *nbv, int *nbc);
/* writes the boolean abstraction of "form" in the file "fname" */

int bool_abstr_pure (noll_form_t * form, FILE * out);
/* writes the boolean abstraction of the pure part of "form": F(\Pi) and F_{eq} */

int bool_abstr_space (noll_form_t * form, FILE * out);
/* writes the boolean abstraction of the spatial part of "form": F(\Sigma) */

int bool_abstr_membership (noll_form_t * form, FILE * out);
/* writes the boolean abstraction of the membership constraints of "form": F_\in */

int bool_abstr_det (noll_form_t * form, FILE * out);
/* writes the boolean abstraction of the determinism constraints of "form": F_det */

int bool_abstr_share (noll_form_t * form, FILE * out);
/* writes the boolean abstraction of the sharing constraints of "form": F(\Lambda) */

int get_pred_of_svar (uid_t svar);
/* returns the predicate id to which svar is bound, if any (-1 otherwise) */

int type_in_predicate_of_svar (uid_t type, uid_t svar);
/* tests if type is a type in the predicate bounded to the variable svar */

/* ====================================================================== */
/* Calling Minisat and adding constraints */
/* ====================================================================== */

int test_in_equality (uid_t x, uid_t y, noll_pure_op_t oper, int nbv, int nbc,
                      char *file);
/* Returns 1 if the boolean abstraction implies [x oper y]
 * returns 0, otherwise.
 * Using the boolean abstraction in the file "file",
 * initialized before calling this function */

int test_satisfiability (int nbv, int nbc, char *file);
/* Returns 1 if form is satisfiable using
 * the file "file" which contains the boolean abstraction */

void normalize (noll_form_t * form, char *file);
/* Updates form to its normal form and
 * put in the file "file" the boolean abstraction */

void normalize_incremental (noll_form_t * form, char *file);
/* The same as "normalize" except that it uses
 * incremental minisat */

#endif /* _NOLL2BOOL */
