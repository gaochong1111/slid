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
#include "noll2graph.h"

//#include "slid_sat.h"
extern void test_check_sat(noll_form_t*);

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

void
noll_sat_diag_unsat (noll_form_t * form, noll_sat_t * fsat)
{
  assert (form != NULL);
  assert (fsat != NULL);
  assert (form == noll_prob->pform);
  assert (form == fsat->form);

  /// file containing the boolean abstraction fsat->file, is closed
  assert (fsat->file == NULL);
  FILE *foutput = fopen ((noll_prob->output_fname == NULL) ? "unsat-out.txt" :
                         noll_prob->output_fname, "a");
  assert (foutput != NULL);

  /// file with proof is in drup_fname with fname=fsat->fname
  assert (fsat->fname != NULL);
  char fnameDRUP[1024];
  fnameDRUP[0] = '\0';
  sprintf (fnameDRUP, "drup_%s", fsat->fname);
  FILE *fDRUP = fopen (fnameDRUP, "r");
  assert (fDRUP != NULL);
  char *line = NULL;
  size_t lineLen = 0;
  while (getline (&line, &lineLen, fDRUP) != -1)
    {
      if (line[0] != 'd')
        continue;
      fprintf (foutput, "(");
      /// read disjuncts from line+2 until 0
      int d = 0;
      size_t offset = 2;
      while (offset < strlen (line))
        {
          if (line[offset] == '-')
            d = -1;
          else if (line[offset] <= '9' && line[offset] >= '1')
            d = d * 10 + (line[offset] - '0');
          else if (line[offset] == ' ' && d != 0)
            {
              uint_t bvar = (d < 0) ? -d : d;
              /// end of some term, lookup in tables
              uint_t vi = 0;
              uint_t vj = 0;
              noll_sat_space_t *fspace = NULL;
              if (noll2sat_get_sat_pure (fsat, bvar, &vi, &vj) != -1)
                {
                  fprintf (foutput, "%s %s %s",
                           noll_var_name (form->lvars, vi, NOLL_TYP_RECORD),
                           (d < 0) ? "<>" : "=",
                           noll_var_name (form->lvars, vj, NOLL_TYP_RECORD));
                }
              else if ((fspace = noll2sat_get_sat_space (fsat, bvar)) != NULL)
                {
                  if (fspace->forig->kind == NOLL_SPACE_LS && d < 0)
                    {
                      /// negative predicate means empty list segment
                      fprintf (foutput, "%s = %s",
                               noll_var_name (form->lvars,
                                              noll_vector_at (fspace->forig->
                                                              m.ls.args, 0),
                                              NOLL_TYP_RECORD),
                               noll_var_name (form->lvars,
                                              noll_vector_at (fspace->forig->
                                                              m.ls.args, 1),
                                              NOLL_TYP_RECORD));
                    }
                  else
                    noll_space_fprint (foutput, form->lvars, form->svars,
                                       fspace->forig);
                }
              else
                {
                  fprintf (foutput, "ERROR: %d", d);
                }
              fprintf (foutput, " %s ",
                       (line[offset + 1] == '0') ? "" : " or ");
              d = 0;
            }
          offset++;
        }
      fprintf (foutput, ")\n * ");
    }
  fprintf (foutput, "emp\n");
  fclose (foutput);
}

void
noll_sat_diag_sat (noll_form_t * form, noll_sat_t * fsat)
{
  assert (form != NULL);
  assert (fsat != NULL);
  assert (form == noll_prob->pform);
  assert (form == fsat->form);

  if (fsat != fsat || form != form)
    assert (0);                 // to remove warning on unused parameter

  if (noll_option_get_verb () > 0)
    fprintf (stdout, "[diag] sat: \n");

  /*
   * Get the simplified form of the formulaby computing the graph
   */
  if (noll_option_get_verb () > 0)
    fprintf (stdout, "    o graph of the formula: ...\n");
  noll_prob->pgraph = noll_graph_of_form (noll_prob->pform, false);

  if (noll_option_is_diag () == true)
    {
      // in SL
      noll_graph_fprint_sl ((noll_prob->output_fname == NULL) ?
                            "sat-out.txt" : noll_prob->output_fname,
                            noll_prob->pgraph);
      // as graph
      noll_graph_fprint_dot ("sat-graph.dot", noll_prob->pgraph);
      if (noll_option_get_verb () > 0)
        {
          fprintf (stdout,
                   "      file sat-graph.dot: (%d nodes, %d spatial edges)\n",
                   noll_prob->pgraph->nodes_size,
                   noll_vector_size (noll_prob->pgraph->edges));
        }
    }
}

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

/**
 * Free memory allocated for sat checking
 */
void
noll_sat_free_aux (noll_form_t * form)
{
  assert (noll_prob != NULL);
  assert (noll_prob->pform == form);

  if (form != form)
    assert (0);                 // to remove warning on unused parameter

  if (noll_prob->pabstr != NULL)
    {
      noll_sat_free (noll_prob->pabstr);
      noll_prob->pabstr = NULL;
    }
  if (noll_prob->pgraph != NULL)
    {
      noll_graph_free (noll_prob->pgraph);
      noll_prob->pgraph = NULL;
    }
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

  /*
   * Compute typing infos
   */
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

  //noll_prob->pabstr = noll_normalize (form, "f-out.txt", true, false);
  //slid_sat_check(form);
  test_check_sat(form);

  /*
   * FIN
   */
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
      if (noll_option_is_diag ())
        noll_sat_diag_unsat (form, noll_prob->pabstr);
      res = 0;
    }
  else
    {
      // else, form->kind is sat
      if (noll_option_get_verb () > 0)
        fprintf (stdout, " sat formula!\n");
      if (noll_option_is_diag ())
        noll_sat_diag_sat (form, noll_prob->pabstr);
    }
  /*
   * Free the allocated memory
   * (only boolean abstraction, formulas will be deallocated at the end)
   */
  noll_sat_free_aux (form);

  return res;
}
