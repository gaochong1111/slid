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
 * Defines the problem for the decision procedure.
 */

#ifndef NOLL_ENTL_H_
#define NOLL_ENTL_H_

#include <stdio.h>
#include "noll_form.h"
#include "noll2sat.h"
#include "noll_norm.h"
#include "noll_sat.h"
#include "noll_graph.h"
#include "noll_hom.h"


/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Entailment problems
 *          phi ==> (\/_j psi_j)    valid
 *  read from the input file in the form
 *          phi /\ ! (\/_j psi_j)   unsat
 *  more precisely in SMTLIB2 format
 *          assert (phi)
 *          ;; for all j
 *          assert (not (psi_j))
 *          check-sat
 *
 *  Additional informations for this entailment solving are
 *  stored as:
 *  - boolean abstract of positive/negative formulae
 *  - abstract graphs of positive/negative formulae
 */

typedef struct noll_entl_t
{
  char *smt_fname;              // smt file with entailment
  char *output_fname;           // output file with proof
  noll_logic_t logic;           // theory used in formulas
  noll_form_t *pform;           // positive formula phi
  noll_form_array *nform;       // array of negative formulae psi
  noll_form_kind_t cmd;         // command given: check-sat (default),
  //                check-unsat

  noll_sat_t *pabstr;           // abstraction of the positive formula
  noll_sat_array *nabstr;       // abstraction of the negative formulae

  noll_graph_t *pgraph;         // graph for positive formula
  noll_graph_array *ngraph;     // graphs for negative formulae

  noll_hom_t *hom;              // homomorphism found
} noll_entl_t;

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

extern noll_entl_t *noll_prob;  // problem of entailment in noll

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Initialization/Deallocation of formulas */
void noll_entl_init (void);
void noll_entl_free (void);

/* ====================================================================== */
/* Getters */
/* ====================================================================== */

noll_form_t *noll_entl_get_pform (void);
/* Get positive formula */
noll_form_t *noll_entl_get_nform_last (void);
/* Get last negative formulae */
noll_form_array *noll_entl_get_nform (void);
/* Get all the set of negative formulae */

/* ====================================================================== */
/* Setters */
/* ====================================================================== */

void noll_entl_set_fname (char *fname);
/* Set source file information */
void noll_entl_set_foutput (char *fname);
/* Set output file information */
void noll_entl_set_cmd (noll_form_kind_t pb);

/* ====================================================================== */
/* Predicates */
/* ====================================================================== */

int noll_entl_is_sat (void);
/* Test if it is a satisfiability problem, i.e., empty negative formulas  */

/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void noll_entl_fprint (FILE * f);

/* ====================================================================== */
/* Solver */
/* ====================================================================== */

int noll_entl_type (void);
/* Type the predicates, fields, formulas in noll_prob */

int noll_entl_normalize (void);
/* Normalize the formulae in noll_prob */

int noll_entl_to_graph (void);
/* Translate to graph representation all formulae in noll_prob */

int noll_entl_to_homomorphism (void);
/* Build the homomorphism for this entailment problem */

int noll_entl_solve (void);
/* Check the global problem in noll_prob */

int noll_share_check (noll_var_array * lvars, noll_var_array * svars,
                      noll_share_array * lambda1, noll_share_array * lambda2);
/* Check satisfiability (if one of formula is NULL)
 * or entailment (lambda1 => lambda2) of share formulas */

#endif /* NOLL_ENTL_H_ */
