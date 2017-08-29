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
#include<iostream>




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
  for (uint_t pid = 0; pid < noll_vector_size (preds_array); pid++)
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


void print_error_info(int code, noll_pred_t* pred) {
  // error infos
  string infos[] = {
    "the number of parameter must be even number. \n", // -1000 check
    "the firt parameter must be record type. \n", //-1001 check
    "the source parameters and destination parameters must be matched in types. \n", //-1002 check
    "the data parameters must be before size parameters in the source parameters. \n", // -1003 check
    "the only data and size parameters in the alpha source parameters. \n", // -1004 check
    "the number of size parameters in the alpha source parameters is at most one. \n", // -1005 check
    "the parameter in the alpha (or beta) source parameters must be different from each other. \n", // -1006 check
    "the number of base rules must be exactly one. \n", //-1007 NONE
    "the OP of base rules must include only = or !=. \n", // -1008 little bug
    "the number of inductive rules must be at least one. \n", // -1009 BUG
    "not supported op in the data constraints in the inductive rule. \n", // -1010 NONE
    "the data constraints in each inductive rule must start with the variable. \n", //-1011 check
    "the size type must include like h op n or h op h+n in data constraints in the inductive rule. \n", //-1012 check
    "the data type constraints must be before the size type constraint in data constraints in the inductive rule. \n", // -1013 NONE
    "the data type must include like x op d or x op x1 in data constraints in the inductive rule. \n", //-1014 check
    "the source of pto must be the first predicate parameter  in the inductive rule. \n", // -1015 check
    "the all fields of pto must be (left, right, rho_d) from the predicate type and the dest location must be from exist in the inductive rule. \n", // -1016 check
    "the only one of recursive call must include one nil parameter in the inductive rule. \n", // -1017 check
    "the parameters of Beta can not occur in other of body of the inductive rule. \n", //-1018 check
    "the parameters of Gamma or Delta must be diffrent from each other in the inductive rule. \n", //-1019 NONE
    "the parameters of Gamma and Delta must be subset of the parameters of Alpha and x and h and constant in the inductive rule. \n", //-1020
    "the parameters of Epsilon must be subset of the parameters of Alpha and constant in the inductive rule. \n", //-1021 check
    "the parameters of x and h must occur in some spatial atom of body of the inductive rule. \n", //-1022 check
    "when size type occur in Alph(i), the Delta(i) and Gamma(i) must be in h and Epsilon(i) is constant and the Alpha(i) = Delta(i) + n or Alpha(i) = Gamma(i) + n must ouccur in data constraint in the inductive rule. \n",//-1023 check


  };

  // print error info
  cout << "For predicate: " << pred->pname << ", Error: " <<infos[-1000-code];
  exit(-1);
}


set<uid_t> vec_to_set(vector<uid_t> vec) {
  set<uid_t> res;
  for(uid_t i=0; i<vec.size(); i++) {
    res.insert(vec[i]);
  }
  return res;
}

set<uid_t> set_union(set<uid_t> set1, set<uid_t> set2) {
  set<uid_t> res;
  for (auto uid : set1) {
    res.insert(uid);
  }
  for (auto uid : set2) {
    res.insert(uid);
  }
  return res;
}

set<uid_t> set_inter(set<uid_t> set1, set<uid_t> set2) {
  set<uid_t> res;
  for (auto uid: set1) {
    if (set2.find(uid) != set2.end()) {
      res.insert(uid);
    }
  }
  return res;
}

int noll_check_tree_pred_rule(noll_pred_t* pred, noll_pred_rule_t* rec_rule, set<uid_t>& alpha, set<uid_t>& beta) {
  noll_var_array* rec_vars = rec_rule->vars;
  uid_t fargs = pred->def->fargs;

  set<uid_t> X_set;
  set<uid_t> x_set;
  set<uid_t> h_set;

  vector<vector<uid_t>> size_constraints;

  for (uid_t j=fargs+1; j<noll_vector_size(rec_vars); j++) {
    noll_var_t* exist_v = noll_vector_at(rec_vars, j);
    if (exist_v->vty->kind == NOLL_TYP_INT) {
      h_set.insert(exist_v->vid);
    } else if (exist_v->vty->kind == NOLL_TYP_RAT) {
      x_set.insert(exist_v->vid);
    } else if (exist_v->vty->kind == NOLL_TYP_RECORD) {
      X_set.insert(exist_v->vid);
    }
  }

  noll_pure_t* pure_rec = rec_rule->pure;
  noll_dform_array* dforms_rec = pure_rec->data;

  for (uid_t j=0; j<noll_vector_size(dforms_rec); j++) {
    noll_dform_t* dform_rec = noll_vector_at(dforms_rec, j);

    if(dform_rec->kind>NOLL_DATA_GE){
      return -1010;
    } else{
      uid_t term_size = noll_vector_size(dform_rec->p.targs);
      noll_dterm_t* term1 = noll_vector_at(dform_rec->p.targs, 0);
      noll_dterm_t* term2 = noll_vector_at(dform_rec->p.targs, 1);
      if (term1->kind != NOLL_DATA_VAR) {
        return -1011;
      }
      // start with v.
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
          noll_dterm_t* term21 = noll_vector_at(term2->args, 0);
          noll_dterm_t* term22 = noll_vector_at(term2->args, 1);
          if (term21->kind != NOLL_DATA_VAR || term22->kind!=NOLL_DATA_INT) {
            return -1012;
          } else {
            // record alpha_i = delta_i + n : term1 = term21 + term22
            vector<uid_t> size_cons_ops;
            size_cons_ops.push_back(term1->p.sid);
            size_cons_ops.push_back(term21->p.sid);
            size_cons_ops.push_back(term22->p.value);
            size_constraints.push_back(size_cons_ops);
          }
        } else {
          return -1012;
        }
      } else if (var1->vty->kind == NOLL_TYP_RAT) {
        if (size_type_constraint_flag) {
          return -1013;
        }
        // data type constraint x < d or x < x
        if (term2->kind == NOLL_DATA_VAR || term2->kind == NOLL_DATA_INT) {
        } else {
          return -1014;
        }
      }
    }
  }


  // check pto
  noll_var_t* E = noll_vector_at(rec_vars, 1);

  noll_pto_t pto_rec = rec_rule->pto->m.pto;

  if (pto_rec.sid != E->vid) {
    return -1015;
  }

  set<uid_t> fields_set;
  set<uid_t> fields_pto_set;
  set<uid_t> vars_rho;
  noll_uid_array* fields_pto = pto_rec.fields;
  noll_uid_array* dest_pto = pto_rec.dest;
  noll_record_t *record_type = noll_vector_at (records_array, pred->typ->ptype0);

  string left_f = noll_vector_at (fields_array, noll_vector_at (fields_pto, 0))->name;
  // cout << "info: "<< left_f <<endl;
  if (left_f != "left" || X_set.find(noll_vector_at(dest_pto, 0)) == X_set.end()) {
    return -1016;
  }

  string right_f = noll_vector_at (fields_array, noll_vector_at (fields_pto, 1))->name;
  // cout << "info: "<< right_f <<endl;
  if (right_f != "right" || X_set.find(noll_vector_at(dest_pto, 1)) == X_set.end()) {
    return -1016;
  }

  uint_t length_fld = noll_vector_size (record_type->flds);
  for (uint_t j = 2; j < length_fld; j++)
  {
    uint_t field_id = noll_vector_at (record_type->flds, j);
    fields_set.insert(field_id);
  }

  for (uid_t i=2; i<noll_vector_size(fields_pto); i++) {
    fields_pto_set.insert(noll_vector_at(fields_pto, i));
    vars_rho.insert(noll_vector_at(dest_pto, i));
  }

  if (fields_set.size() != fields_pto_set.size()) {
    return -1016;
  }
  for (auto fld : fields_pto_set) {
    if (fields_set.find(fld) == fields_set.end()) {
      return -1016;
    }
  }
  //check the recursive call
  noll_space_t* pcall_rec = rec_rule->rec;
  noll_space_t* phi_delta = noll_vector_at(pcall_rec->m.sep, 0);
  noll_space_t* phi = noll_vector_at(pcall_rec->m.sep, 1);

  if ((noll_vector_at(phi->m.ls.args ,fargs/2) == 0 && noll_vector_at(phi_delta->m.ls.args ,fargs/2) == 0) ||
      (noll_vector_at(phi->m.ls.args ,fargs/2) != 0 && noll_vector_at(phi_delta->m.ls.args ,fargs/2) != 0)) {
    return -1017;
  }

  if (noll_vector_at(phi_delta->m.ls.args ,fargs/2) == 0) {
    phi = phi_delta;
    phi_delta =  noll_vector_at(pcall_rec->m.sep, 1);
  }
  // delta, gamma, epsilon
  set<uid_t> delta;
  set<uid_t> gamma;
  vector<uid_t> epsilon;
  // pcall(Y,delta;F,beta) : phi_delta
  uid_t Y_id = noll_vector_at(phi_delta->m.ls.args, 0);
  for (uid_t j=1; j<fargs/2; j++) {
    uid_t delta_vid = noll_vector_at(phi_delta->m.ls.args, j);
    delta.insert(delta_vid);
    uid_t gamma_vid = noll_vector_at(phi->m.ls.args, j);
    gamma.insert(gamma_vid);
  }
  // pcall(X,gamma;nil,epsilon) : phi
  uid_t X_id = noll_vector_at(phi->m.ls.args, 0);
  for (uid_t j=fargs/2+1; j<fargs; j++) {
    uid_t epsilon_vid = noll_vector_at(phi->m.ls.args, j);
    epsilon.push_back(epsilon_vid);
  }

  // we have alhpa , beta, E, F; gamma, epsilon, delta, var_rho, X_set, x_set, h_set
  // check C1
  set<uid_t> beta_other = set_union(gamma, set_union(delta, set_union(gamma, set_union(vars_rho, vec_to_set(epsilon))))); // gamma, epsilon, delta, var_rho_d
  set<uid_t> c1_set = set_inter(beta, beta_other);
  if (c1_set.size() > 0) {
    return -1018;
  }
  // check C2
  set<uid_t> alpha_x_h = set_union(alpha, set_union(x_set, h_set));
  if (gamma.size() != alpha.size() || delta.size() != alpha.size()) {
    return -1019;
  }

  set<uid_t> gamma_delta = set_union(gamma, delta);
  for (auto uid : gamma_delta) {
    if (alpha_x_h.find(uid) == alpha_x_h.end() && uid < noll_vector_size(rec_vars)) {
      return -1020;
    }
  }
  set<uid_t> epsilon_set = vec_to_set(epsilon);
  for (auto uid: epsilon_set) {
    if (alpha.find(uid) == alpha.end() && uid < noll_vector_size(rec_vars)) {
      return -1021;
    }
  }
  // check C3
  set<uid_t> x_h = set_union(x_set, h_set);
  for (auto uid : x_h) {
    if (beta_other.find(uid) == beta_other.end()) {
      return -1022;
    }
  }
  // check C4
  if (noll_vector_at(rec_vars, fargs/2)->vty->kind == NOLL_TYP_INT) {
    int err_flag = 1;

    uid_t alpha_i = noll_vector_at(rec_vars, fargs/2)->vid;
    uid_t delta_i =  noll_vector_at(phi_delta->m.ls.args, fargs/2-1);
    uid_t gamma_i = noll_vector_at(phi->m.ls.args, fargs/2-1);
    uid_t epsilon_i = noll_vector_at(phi->m.ls.args, fargs-1);

    if (h_set.find(delta_i) != h_set.end() && h_set.find(gamma_i) != h_set.end() && epsilon_i>=noll_vector_size(rec_vars)) {
      for (uid_t i=0; i<size_constraints.size(); i++) {
        vector<uid_t> size_cons1 = size_constraints[i];
        if (size_cons1[0] == alpha_i && (size_cons1[1] == delta_i || size_cons1[1]==gamma_i)) {
          err_flag = 0;
        }
      }
    }
    if (err_flag) {
      return -1023;
    }
  }
  return 0;
}

/**
 * check the predicate definition and type the pred->typing
 * @return 0, if ok
 *        ERROR_CODE, otherwise
 */
int noll_check_tree_pred(noll_pred_t* pred) {
  // check
  int res  = 1;
  noll_pred_type_init (pred);

  uid_t fargs = pred->def->fargs;
  if (fargs<2 || fargs%2 == 1) {
    return -1000;
  }

  noll_var_array* lvars = pred->def->vars;

  noll_var_t* E = noll_vector_at(lvars, 1);
  noll_var_t* F = noll_vector_at(lvars, 1+fargs/2);
  if (E->vty->kind!=NOLL_TYP_RECORD || F->vty->kind!=NOLL_TYP_RECORD) {
    return -1001;
  }

  int type_match_flag = 1;
  if (noll_vector_at(E->vty->args, 0) != noll_vector_at(F->vty->args, 0)) {
    type_match_flag = 0;
    return -1002;
  }

  int size_type_flag = 0;
  int data_type_flag = 0;

  set<uid_t> alpha;
  set<uid_t> beta;

  for (uid_t i=2; i<=fargs/2; i++) {
    noll_var_t* arg_alpha = noll_vector_at(lvars, i);
    noll_var_t* arg_beta = noll_vector_at(lvars, i+fargs/2);

    if (arg_alpha->vty->kind == NOLL_TYP_RAT) {
      if (size_type_flag) {
        return -1003;
      } else {
        data_type_flag = 1;
      }
    } else if (arg_alpha->vty->kind == NOLL_TYP_INT) {
      size_type_flag++;
    } else {
      return -1004;
    }

    if (!type_match_flag || arg_alpha->vty->kind != arg_beta->vty->kind) {
      return -1002;
    }
    alpha.insert(arg_alpha->vid);
    beta.insert(arg_beta->vid);
  }

  if(size_type_flag > 1) {
    return -1005;
  }

  if (alpha.size() != fargs/2-1 || beta.size() != fargs/2-1) {
    return -1006;
  }

  // fill the tree predicate type
  pred->typ->ptype0 = noll_vector_at(E->vty->args, 0); // type(record) id
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
    return -1007;
  }
  noll_pred_rule_t* base_rule = noll_vector_at(base_rules, 0);
  noll_pure_t* pure_base = base_rule->pure;
  // parser translate < into !=
  if (base_rule->pto!=NULL&&base_rule->rec!=NULL && !noll_vector_empty(pure_base->data)) {
    return -1008;
  }

  //check the recursive rules
  noll_pred_rule_array* rec_rules  = pred->def->rec_rules;
  uid_t size_rules = noll_vector_size(rec_rules);
  if (size_rules<1) {
    return -1009;
  }

  for (uid_t i=0; i<size_rules; i++) {
    noll_pred_rule_t* rule_rec = noll_vector_at(rec_rules, i);
    return noll_check_tree_pred_rule(pred, rule_rec, alpha, beta);
  }
  return 0;
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
    res = noll_check_tree_pred(pred);
    if (res < 0) {
      print_error_info(res, pred);
    }
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
    noll_check_preds();


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
