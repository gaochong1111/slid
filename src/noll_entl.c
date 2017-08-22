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
// #include "slid_sat.h"

#include "csltp_sat.h"


// extern int solve_entail(void);

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
 * check the predicate type: NOLL_PRED_LIN or NOLL_PRED_TREE
 *
 */
void noll_check_predicate_type() {
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
}

/**
 * check the predicate definition and type the pred->typing
 * @return 1, if ok
 *        -1, otherwise
 */
int noll_check_tree_pred(noll_pred_t* pred) {
  // check
  int res  = 1;
  noll_pred_type_init (pred);

  uid_t fargs = pred->def->fargs;
  if (fargs<2 || fargs%2 == 1) {
    fprintf(stdout, "Error for predicate %s, arguments number must be great than 1 and even number. \n", pred->pname);
    return -1;
  }

  noll_var_array* lvars = pred->def->vars;
  noll_var_t* E = noll_vector_at(lvars, 1);
  noll_var_t* F = noll_vector_at(lvars, 1+fargs/2);
  if (E->vty->kind!=NOLL_TYP_RECORD || F->vty->kind!=NOLL_TYP_RECORD) {
    fprintf(stdout, "Error for predicate %s, the firt parameter must be record type. \n", pred->pname);
    return -1;
  }

  int type_match_flag = 1;

  if (E->vty->kind!=F->vty->kind) {
    type_match_flag = 0;
    fprintf(stdout, "Error for predicate %s, the source parameters and destination parameters must be matched in types. \n", pred->pname);
  }

  int size_type_flag = 0;
  int data_type_flag = 0;
  noll_uid_array* alpha = noll_uid_array_new();
  noll_uid_array_reserve(alpha, fargs/2);

  noll_uid_array* beta = noll_uid_array_new();
  noll_uid_array_reserve(beta, fargs/2);


  for (uid_t i=2; i<=fargs/2; i++) {
    noll_var_t* arg_alpha = noll_vector_at(lvars, i);
    noll_var_t* arg_beta = noll_vector_at(lvars, i+fargs/2);

    if (arg_alpha->vty->kind == NOLL_TYP_RAT) {
      if (size_type_flag) {
        fprintf(stdout, "Error for predicate %s, data parameters must be before size parameter in the source parameters. \n", pred->pname);
        return -1;
      } else {
        data_type_flag = 1;
      }
    } else if (arg_alpha->vty->kind == NOLL_TYP_INT) {
      size_type_flag = 1;
    } else {
      fprintf(stdout, "Error for predicate %s, there are only data and size parameters in the alpha source parameters. \n", pred->pname);
      return -1;
    }

    if (!type_match_flag || arg_alpha->vty->kind != arg_beta->vty->kind) {
      fprintf(stdout, "Error for predicate %s, source parameters must be mathed in type with the destination parameters. \n", pred->pname);
      return -1;
    }
    noll_uid_array_push(alpha, arg_alpha->vid);
    noll_uid_array_push(beta, arg_beta->vid);
  }

  // fill the tree predicate type
  if (size_type_flag && data_type_flag) {
    pred->typ->p.treekind = NOLL_PRED_TREE_GENRAL;
  } else if (size_type_flag) {
    pred->typ->p.treekind = NOLL_PRED_TREE_ONLY_SIZE;
  } else if (data_type_flag) {
    pred->typ->p.treekind = NOLL_PRED_TREE_ONLY_DATA;
  } else {
    pred->typ->p.treekind = NOLL_PRED_TREE_NONE_DATA;
  }

  // check rules for predicate
  noll_pred_rule_array* base_rules = pred->def->base_rules;
  // check base rule
  if (noll_vector_size(base_rules) != 1) {
    fprintf(stdout, "Error for predicate %s, the base rule must have exactly one. \n", pred->pname);
    return -1;
  }
  noll_pred_rule_t* base_rule = noll_vector_at(base_rules, 0);

  noll_pure_t* pure_base = base_rule->pure;

  for (uid_t i=1; i<pure_base->size; i++) {
    for (uid_t j=i+1; j<pure_base->size; j++) {
      if (noll_pure_matrix_at(pure_base, i, j) !=  NOLL_PURE_EQ
          && noll_pure_matrix_at(pure_base, i, j) !=  NOLL_PURE_NEQ) {
        fprintf(stdout, "Error for predicate %s, the base rule must have only = or != relation. \n", pred->pname);
        return -1;
      }
    }
  }

  if (base_rule->pto!=NULL&&base_rule->rec!=NULL && !noll_vector_empty(pure_base->data)) {
    fprintf(stdout, "Error for predicate %s, the base rule must have only = or != relation. \n", pred->pname);
    return -1;
  }

  //check the recursive rules
  noll_pred_rule_array* rec_rules  = pred->def->rec_rules;
  uid_t size_rules = noll_vector_size(rec_rules);
  if (size_rules<1) {
    fprintf(stdout, "Error for predicate %s, the number of inductive rule must be at least one. \n", pred->pname);
    return -1;
  }


  for (uid_t i=0; i<size_rules; i++) {
    noll_pred_rule_t* rec_rule = noll_vector_at(rec_rules, i);
    noll_var_array* rec_vars = rec_rule->vars;

    noll_uid_array* X_var = noll_uid_array_new();
    noll_uid_array* x_var = noll_uid_array_new();
    noll_uid_array* h_var = noll_uid_array_new();

    for (uid_t j=0; j<noll_vector_size(rec_vars); j++) {
      noll_var_t* exist_v = noll_vector_at(rec_vars, j);
      if (exist_v->vty->kind == NOLL_TYP_INT) {
        noll_uid_array_push(h_var, exist_v->vid);
      } else if (exist_v->vty->kind == NOLL_TYP_RAT) {
        noll_uid_array_push(x_var, exist_v->vid);
      } else if (exist_v->vty->kind == NOLL_TYP_RECORD) {
        noll_uid_array_push(X_var, exist_v->vid);
      }
    }

    noll_pure_t* pure_rec = rec_rule->pure;
    noll_dform_array* dforms_rec = pure_rec->data;

    for (uid_t j=0; j<noll_vector_size(dforms_rec); j++) {
      noll_dform_t* dform_rec = noll_vector_at(dforms_rec, j);
      if (dform_rec->typ == NOLL_TYP_BOOL) {
        // TODO: true?

      }
      if(dform_rec->kind>NOLL_DATA_GE){
        fprintf(stdout, "Error for predicate %s, not supported op in data constraints in the inductive rule. \n", pred->pname);
        return -1;
      } else{
        uid_t term_size = noll_vector_size(dform_rec->p.targs);
        noll_dterm_t* term1 = noll_vector_at(dform_rec->p.targs, 0);
        noll_dterm_t* term2 = noll_vector_at(dform_rec->p.targs, 1);
        if (term1->kind != NOLL_DATA_VAR) {
          fprintf(stdout, "Error for predicate %s, variable must be the first in data constraints in the inductive rule. \n", pred->pname);
          return -1;
        }

        noll_var_t* var1 = noll_vector_at(rec_vars, term1->p.sid);

        noll_var_t* var2 = NULL;
        if (term2->kind == NOLL_DATA_VAR) {
          var2 = noll_vector_at(rec_vars, term2->p.sid);
        }
        int size_type_constraint_flag = 0;
        if (var1->vty->kind == NOLL_TYP_INT) {
          size_type_constraint_flag = 1;
          // size type constraint: h = n or h = h + n
          if (term2->kind == NOLL_DATA_INT) {

          } else if (term2->kind == NOLL_DATA_PLUS) {
            // record alpha_i = delta_i + n : term1 = term21 + term22
            noll_dterm_t* term21 = noll_vector_at(term2->args, 0);
            noll_dterm_t* term22 = noll_vector_at(term2->args, 1);
            if (term21->kind != NOLL_DATA_VAR || term22->kind!=NOLL_DATA_INT) {
              fprintf(stdout, "Error for predicate %s, size type must be h op n or h op h+n in data constraints in the inductive rule. \n", pred->pname);
              return -1;
            }
          } else {
            fprintf(stdout, "Error for predicate %s, size type must be h op n or h op h+n in data constraints in the inductive rule. \n", pred->pname);
            return -1;
          }

        } else if (var1->vty->kind == NOLL_TYP_RAT) {
          if (size_type_constraint_flag) {
            fprintf(stdout, "Error for predicate %s, size type must be after data type constraint in data constraints in the inductive rule. \n", pred->pname);
            return -1;
          }
          // data type constraint x < d or x < x
          if (term2->kind == NOLL_DATA_VAR || term2->kind == NOLL_DATA_INT) {
          } else {
            fprintf(stdout, "Error for predicate %s, data type must be x op d or x op x1 in data constraints in the inductive rule. \n", pred->pname);
            return -1;
          }
        }
      }
    }

    noll_pto_t pto_rec = rec_rule->pto->m.pto;
    if (pto_rec.sid != E->vid) {
      fprintf(stdout, "Error for predicate %s, the source pto must be the first predicate parameter  in the inductive rule. \n", pred->pname);
      return -1;
    }

    noll_uid_array* fields_pto = pto_rec.fields;
    noll_uid_array* dest_pto = pto_rec.dest;
    // TODO:   fileds check


    noll_space_t* pcall_rec = rec_rule->rec;
    noll_space_t* phi_delta = noll_vector_at(pcall_rec->m.sep, 0);
    noll_space_t* phi = noll_vector_at(pcall_rec->m.sep, 1);
    if (noll_vector_at(phi_delta->m.ls.args ,fargs/2) == 0) {
      phi = phi_delta;
      phi_delta =  noll_vector_at(pcall_rec->m.sep, 1);
    }

    // delta, gamma, epsilon
    noll_uid_array* delta = noll_uid_array_new();
    noll_uid_array* gamma = noll_uid_array_new();
    noll_uid_array* epsilon = noll_uid_array_new();

    // pcall(Y,delta;F,beta) : phi_delta

    uid_t Y_id = noll_vector_at(phi_delta->m.ls.args, 0);
    for (uid_t j=1; j<fargs/2; j++) {
      uid_t delta_vid = noll_vector_at(phi_delta->m.ls.args, j);
      noll_uid_array_push(delta, delta_vid);

      uid_t gamma_vid = noll_vector_at(phi->m.ls.args, j);
      noll_uid_array_push(gamma, gamma_vid);
    }

    // pcall(X,gamma;nil,epsilon) : phi
    uid_t X_id = noll_vector_at(phi->m.ls.args, 0);
    for (uid_t j=fargs/2+1; j<fargs; j++) {
      uid_t epsilon_vid = noll_vector_at(phi->m.ls.args, j);
      noll_uid_array_push(epsilon, epsilon_vid);
    }

    // check C1
    // check C2
    // check C3
    // check C4

  }

  return 1;
}

/**
 * check all predicates
 * @return 1, if ok
 *        -1, otherwise
 */
int noll_check_preds() {
  int res = 0;
  for (uint_t pid = 0; pid < noll_vector_size (preds_array); pid++) {
    noll_pred_t* pred = noll_vector_at(preds_array, pid);
    noll_check_tree_pred(pred);
  }
  return res;
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

  noll_check_predicate_type();

  struct timeval tvBegin, tvEnd, tvDiff;

  gettimeofday (&tvBegin, NULL);

  if (noll_prob->pred_t == NOLL_PRED_TREE)
  {
    // tree predicate
#ifndef NDEBUG
    noll_entl_fprint (stdout);
    fflush (stdout);
#endif

    // check the predicate definition


    res = csltp_sat_check(noll_prob->pform);
  }
  else{
    // linear predicate
    noll_entl_type ();

    if (noll_entl_is_sat ()) {
      // res = slid_sat_check(noll_prob->pform);
    } else {
      // solve entail problem
      // res = solve_entail();
    }
    //return noll_sat_solve (noll_prob->pform);
  }
  gettimeofday (&tvEnd, NULL);
  time_difference (&tvDiff, &tvEnd, &tvBegin);
  printf ("\nTotal time (sec): %ld.%06ld\n\n", (long int) tvDiff.tv_sec,
          (long int) tvDiff.tv_usec);
  return res;
}
