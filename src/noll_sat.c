/**************************************************************************/
/*                                                                        */
/*  SPEN decision procedure                                               */
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

/*
 * Sat checking and diagnosis
 */
#include "noll_sat.h"
#include "noll_entl.h"
#include "noll_option.h"

#include "slid_sat.h"

/* ====================================================================== */
/* Utilities */
/* ====================================================================== */

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

/* ====================================================================== */
/* Sat diagnosis */
/* ====================================================================== */

/*void
noll_sat_diag_unsat (noll_form_t * form, noll_sat_t * fsat)
{

}
*/
/*void
noll_sat_diag_sat (noll_form_t * form, noll_sat_t * fsat)
{

}*/

/* ====================================================================== */
/* Sat checking */
/* ====================================================================== */

/**
 * Type the predicates, fields, formulas in noll_prob.
 * @return 1 if typing is ok
 */
int
noll_sat_type (void)
{
  /*
   * Type predicate definitions,
   * it has side effects on the typing infos on preds_array
   */
  if (noll_pred_type () == 0)
    return 0;

  /*
   * Order fields,
   * it has side effects on the fields_array, adds oredeing infos
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


int
noll_sat_solve (noll_form_t * form)
{
  /* check that form is exactly the positive formula */
  assert (noll_prob->pform == form);

  /*
   * Special case: null or unsat input formula
   */
  if (form == NULL || form->kind == NOLL_FORM_UNSAT)
  {
    if (noll_option_get_verb () > 0)
      fprintf (stdout, " unsat formula!\n");
    if (noll_option_is_diag ())
      fprintf (stdout, "[diag] unsat at input!\n");
    return 0;
  }

  struct timeval tvBegin, tvEnd, tvDiff;

  gettimeofday (&tvBegin, NULL);

  if (noll_option_get_verb () > 0)
    fprintf (stdout, "  > typing formula\n");

  noll_sat_type ();

#ifndef NDEBUG
  fprintf (stdout, "\n*** noll_sat_solve: after typing problem:\n");
  noll_records_array_fprint (stdout, "records:");
  noll_fields_array_fprint (stdout, "fields:");
  noll_pred_array_fprint (stdout, preds_array, "predicates:");
  fflush (stdout);
#endif

  // apply check sat
  slid_sat_check(form);


check_end:

  gettimeofday (&tvEnd, NULL);
  time_difference (&tvDiff, &tvEnd, &tvBegin);
  printf ("\nTotal time (sec): %ld.%06ld\n\n", (long int) tvDiff.tv_sec,
          (long int) tvDiff.tv_usec);

  int res = 1;
  if (form->kind == NOLL_FORM_UNSAT)
  {
    if (noll_option_get_verb () > 0)
      fprintf (stdout, " unsat formula!\n");
    /* if (noll_option_is_diag ())
       noll_sat_diag_unsat (form, noll_prob->pabstr);*/
    res = 0;
  }
  else
  {
    // else, form->kind is sat
    if (noll_option_get_verb () > 0)
      fprintf (stdout, " sat formula!\n");
    /*if (noll_option_is_diag ())
      noll_sat_diag_sat (form, noll_prob->pabstr);*/
  }

  return res;
}
