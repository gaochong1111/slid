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

#ifndef NOLL_LEMMA_H_
#define NOLL_LEMMA_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include <stdio.h>
#include "noll_preds.h"
#include "noll_graph.h"


/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

  typedef enum
  {
    NOLL_LEMMA_COMP_1 = 0,      /// P * P => P
    NOLL_LEMMA_COMP_1S,         /// P' * P => P with P' stronger than P
    NOLL_LEMMA_COMP_2,          /// P' * P => P
    NOLL_LEMMA_COMP_2S,         /// P'' * P => P with P' stronger than P'
    NOLL_LEMMA_INSTANCE,        /// P'(E,cst) => P (E)
    NOLL_LEMMA_STRONGER,        /// P' => P
    NOLL_LEMMA_OTHER
  } noll_lemma_e;

/**
 * Represents a lemma of the form
 * P1(args1) [* P2(args2)] [/\ pure] ==> P(args)
 */
  typedef struct noll_lemma_s
  {
    uint_t pid;                 /// predicate identifier P
    noll_lemma_e kind;
    noll_pred_rule_t rule;      /// remainder of the lemma stores as follows:
    /// rule->vars = args o (args1 U args2 \ args3)
    /// rule->pure = pure
    /// rule->pto = NULL
    /// rule->nst = NULL
    /// rule->rec = P1(args1) [* P2(args2)] 
  } noll_lemma_t;

    NOLL_VECTOR_DECLARE (noll_lemma_array, noll_lemma_t *);

  /* ====================================================================== */
  /* Globals */
  /* ====================================================================== */

  extern noll_lemma_array **lemma_array;        // lemma set indexed by the predicate entailed P

  void noll_lemma_init (void);
  /* Initialize the global arrays of lemmas, after the initialization of predicates */

  noll_lemma_array *noll_lemma_init_pred (uid_t pid);
  /* Initialize the global arrays of lemmas for entry @p pid */

  /* ====================================================================== */
  /* Getters/Setters */
  /* ====================================================================== */

  noll_lemma_array *noll_lemma_getpred (uid_t pid);
  /* Get the lemma associated with @p pid */

  noll_space_t *noll_lemma_getspace (noll_lemma_t * l, uid_t n);
  /* Get the @p n-th space formula */

  noll_lemma_e noll_lemma_get_kind (noll_lemma_t * l);
  /* Get the kind of lemma */

  /* ====================================================================== */
  /* Printing */
  /* ====================================================================== */

  void noll_lemma_array_fprint (FILE * f);
  /* Print the global array of lemma. */

  void noll_lemma_fprint (FILE * f, noll_lemma_t * l);
  /* Print the lemma. */

  void noll_lemma_kind_fprint (FILE * f, noll_lemma_e kind);
  /* Print the lemma kind. */

#ifdef	__cplusplus
}
#endif

#endif                          /* _NOLL_LEMMA_H_ */
