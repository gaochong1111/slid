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

#include <sys/time.h>
#include <stdio.h>

#include "noll.h"
#include "noll_option.h"
#include "noll_form.h"
#include "noll_entl.h"
#include "slid_sat.h"


extern int solve_entail(void);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_entl_t *noll_prob;         // problem of entailment in noll

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Initialization/Deallocation of problem */
void
noll_entl_init (void)
{
  noll_prob = (noll_entl_t *) malloc (sizeof (noll_entl_t));
  // init file name
  noll_prob->smt_fname = NULL;
  noll_prob->output_fname = NULL;

  // init positive formula
  noll_prob->pform = noll_form_new ();

  // init negative formulae array
  noll_prob->nform = noll_form_array_new ();
  // if empty aray, then SAT problem, else ENTAILMENT problem

  noll_prob->pred_t = NOLL_PRED_LIN;
  // init command
  noll_prob->cmd = NOLL_FORM_SAT;       // by default value


}


void
noll_entl_free (void)
{
  assert (noll_prob != NULL);
  // this procedure shall be called only once
  if (noll_prob->smt_fname != NULL)
  {
    free (noll_prob->smt_fname);
    noll_prob->smt_fname = NULL;
  }
  if (noll_prob->pform != NULL)
  {
    noll_form_free (noll_prob->pform);
    noll_prob->pform = NULL;
  }
  if (noll_prob->nform != NULL)
  {
    noll_form_array_delete (noll_prob->nform);
    noll_prob->nform = NULL;
  }

  free (noll_prob);
}

/* ====================================================================== */
/* Getters */
/* ====================================================================== */

noll_form_t *
noll_entl_get_pform ()
{
  assert (noll_prob != NULL);
  return noll_prob->pform;
}

noll_form_t *
noll_entl_get_nform_last ()
{
  assert (noll_prob != NULL);
  assert (noll_prob->nform != NULL);
  if (noll_vector_empty (noll_prob->nform))
    noll_form_array_push (noll_prob->nform, noll_form_new ());

  return noll_vector_last (noll_prob->nform);
}

noll_form_array *
noll_entl_get_nform ()
{
  assert (noll_prob != NULL);
  return noll_prob->nform;
}

/* ====================================================================== */
/* Setters */
/* ====================================================================== */

void
noll_entl_set_fname (char *fname)
{
  assert (noll_prob->smt_fname == NULL);
  noll_prob->smt_fname = strdup (fname);
}

void
noll_entl_set_foutput (char *fname)
{
  assert (noll_prob->output_fname == NULL);
  noll_prob->output_fname = strdup (fname);
}

void
noll_entl_set_cmd (noll_form_kind_t pb)
{
  noll_prob->cmd = pb;
}


/* ====================================================================== */
/* Predicates */
/* ====================================================================== */
int
noll_entl_is_sat (void)
{
  assert (noll_prob != NULL);

  if (noll_prob->nform == NULL || noll_vector_empty (noll_prob->nform))
    return 1;
  return 0;
}


/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void
noll_entl_fprint (FILE * f)
{
  assert (f != NULL);

  if (noll_prob == NULL)
  {
    fprintf (f, "*** (entailment) null\n");
    return;
  }

  fprintf (f, "*** (source %s) check-%s on:\n", noll_prob->smt_fname,
           (noll_prob->cmd == NOLL_FORM_SAT) ? "sat" : "unsat");

  noll_records_array_fprint (f, "records:");
  noll_fields_array_fprint (f, "fields:");

  if (noll_prob->pred_t == NOLL_PRED_TREE)
  {
    fprintf(f, "\npredicate type: tree predicate.\n");
  }
  else
  {
    fprintf(f, "\npredicate type: linear predicate.\n");
  }


  noll_pred_array_fprint (f, preds_array, "predicates");

  fprintf (f, "\nFormula 1: ");
  noll_form_fprint (f, noll_prob->pform);
  fflush (f);
  fprintf (f, "\nFormulae 0: ");
  for (size_t i = 0; i < noll_vector_size (noll_prob->nform); i++)
  {
    fprintf (f, "\n\\/ (0-%zu): ", i);
    noll_form_fprint (f, noll_vector_at (noll_prob->nform, i));
  }
  fflush (stdout);
}

/* ====================================================================== */
/* Solver */
/* ====================================================================== */


/**
 * Type the predicates, fields, formulas in noll_prob.
 * @return 1 if typing is ok
 */
int
noll_entl_type (void)
{
  /*
   * Type predicate definitions,
   * it has side effects on the typing infos on preds_array
   */
  if (noll_pred_type () == 0)
    return 0;



  /*
   * Order fields,
   * it has side effects on the fields_array, adds ordering infos
   */
  if (noll_field_order () == 0)
    return 0;

  /*
   * Type formulas inside the problem.
   */
  if (noll_form_type (noll_prob->pform) == 0)
    return 0;

  for (uint_t i = 0; i < noll_vector_size (noll_prob->nform); i++)
    if (noll_form_type (noll_vector_at (noll_prob->nform, i)) == 0)
    {
#ifndef NDEBUG
      fprintf (stdout, "*** noll_entl_type: type error in %d nform.\n", i);
      fflush (stdout);
#endif
      return 0;
    }

  return 1;
}


/**
 * compute the difference between two times.
 *
 * @return 1 if the difference is negative, otherwise 0.
 */
int
time_difference (struct timeval *result, struct timeval *t2,
                 struct timeval *t1)
{
  long int diff = (t2->tv_usec + 1000000 * t2->tv_sec)
    - (t1->tv_usec + 1000000 * t1->tv_sec);
  result->tv_sec = diff / 1000000;
  result->tv_usec = diff % 1000000;

  return (int) (diff < 0);
}


/**
 * Return status of the noll_prob->cmd for the formula
 *    pform /\ not(\/ nform_i)
 * by looking at the entailment
 *    pform ==> \/ nform_i
 *
 * @return 1 if satisfiable, (i.e. invalid entailment)
 *         0 if not satisfiable (i.e., valid entailment)
 *
 */
int
noll_entl_solve (void)
{
  int res = 0;


  // check the predicate type
  for (uint_t pid = 0;
       pid < noll_vector_size (preds_array); pid++)
  {
    noll_pred_t *p = noll_vector_at (preds_array, pid);
    size_t size = (p->def->rec_rules == NULL) ? 0 : noll_vector_size (p->def->rec_rules);
    noll_space_t* pcall = NULL;
    if (size > 0) {
      pcall = noll_vector_at (p->def->rec_rules, 0)->rec;
      size_t pcall_num = noll_vector_size (pcall->m.sep);
      if (pcall_num > 1)
      {
        noll_prob->pred_t = NOLL_PRED_TREE;
        break;
      }
    }
  }

  if (noll_prob->pred_t == NOLL_PRED_TREE)
  {
    // tree predicate
    //#ifndef NDEBUG
    noll_entl_fprint (stdout);
    fflush (stdout);
    //#endif
  }
  else{
    // linear predicate
    noll_entl_type ();

    struct timeval tvBegin, tvEnd, tvDiff;

    // begin timer
    gettimeofday (&tvBegin, NULL);

    if (noll_entl_is_sat ()) {
      res = slid_sat_check(noll_prob->pform);
    } else {
      // solve entail problem
      res = solve_entail();
    }
    //return noll_sat_solve (noll_prob->pform);

    gettimeofday (&tvEnd, NULL);
    time_difference (&tvDiff, &tvEnd, &tvBegin);
    printf ("\nTotal time (sec): %ld.%06ld\n\n", (long int) tvDiff.tv_sec,
            (long int) tvDiff.tv_usec);
  }
  return res;
}
