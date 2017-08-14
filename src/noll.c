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

/** Additional definitions needed to parse NOLL files
 */

#include "noll.h"
#include "noll_option.h"

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

int noll_error_parsing = 0;

/*
 * ======================================================================
 * Messages
 * ======================================================================
 */

void
noll_error (int level, const char *fun, const char *msg)
{
  fprintf (stderr, "Error of level %d in %s: %s.\n", level, fun, msg);
  if (level == 0)
    //terminate
    exit (0);
  else
    noll_error_parsing = level;
}

void
noll_error_args (int level, const char *fun, uint_t size, const char *expect)
{
  fprintf (stderr,
           "Error of level %d in %s: bad number (%d) of arguments, expected (%s).\n",
           level, fun, size, expect);
  if (level == 0)
    //terminate
    exit (0);
  else
    noll_error_parsing = level;
}

void
noll_error_id (int level, char *fun, const char *name)
{
  fprintf (stderr,
           "Error of level %d in %s: identifier '%s' is not declared.\n",
           level, fun, name);
  if (level == 0)
    //terminate
    exit (0);
  else
    noll_error_parsing = level;
}

/*
 * ======================================================================
 * Globals
 * ======================================================================
 */

void
noll_init ()
{
  noll_record_init ();
  noll_field_init ();
  //TODO:remove noll_vars_init();
  noll_pred_init ();
}

/*
 * ======================================================================
 * Context
 * ======================================================================
 */

noll_context_t *
noll_mk_context (void)
{
  noll_context_t *r =
    (noll_context_t *) malloc (sizeof (struct noll_context_t));

  /* initialize the global tables for the analysis */
  noll_init ();

#ifndef NDEBUG
  printf ("noll_mk_context reset qstack\n");
#endif
  /* initialize the stack of location variables to store
   * one global variable (nil) */
  r->lvar_stack = noll_uint_array_new ();
  noll_uint_array_push (r->lvar_stack, 1);

  /* initialize the set of location variables to store
   * nil */
  r->lvar_env = noll_var_array_new ();
  noll_var_register (r->lvar_env, "nil",
                     noll_record_find ("void"), NOLL_SCOPE_GLOBAL);

  /* initialize the stack of sloc vars to the empty stack */
  r->svar_stack = noll_uint_array_new ();
  noll_uint_array_push (r->svar_stack, 0);

  /* initialize the set of sloc vars to be empty */
  r->svar_env = noll_var_array_new ();

  /* the current procedure name */
  r->pname = NULL;

  return r;
}

/**
 * Destroy context data at the end of parsing.
 */
void
noll_del_context (noll_context_t * ctx)
{
  //ctx->l_env is in general in use
  noll_uint_array_delete (ctx->lvar_stack);
  noll_var_array_delete (ctx->lvar_env);
  noll_uint_array_delete (ctx->svar_stack);
  noll_var_array_delete (ctx->svar_env);
  free (ctx->pname);
  //not in use, usually
  free (ctx);
}

/**
 * Reinitialize the context to globals.
 * A new array shall be created for the @p ctx->*vars.
 */
void
noll_context_restore_global (noll_context_t * ctx)
{
  assert (ctx != NULL);
  assert (ctx->lvar_env != NULL);
  assert (ctx->lvar_stack != NULL);
  assert (ctx->svar_env != NULL);
  assert (ctx->svar_stack != NULL);

#ifndef NDEBUG
  fprintf (stderr,
           "noll_context_restore_global: (begin) %d lvars, %d svars\n",
           noll_vector_at (ctx->lvar_stack, 0),
           noll_vector_at (ctx->svar_stack, 0));
#endif
  // ctx->* vars have been copied in  the formulae
  // refill the context with the global variables
  /// Ref, Int and BagInt vars
  noll_var_array *arr = ctx->lvar_env;
  //this array is in the formulae
  uint_t size = noll_vector_at (ctx->lvar_stack, 0);
  ctx->lvar_env = noll_var_array_new ();
  if (size > 0)
    noll_var_array_reserve (ctx->lvar_env, size);
  for (uint_t i = 0; i < size; i++)
    noll_var_array_push (ctx->lvar_env,
                         noll_var_copy (noll_vector_at (arr, i)));

  /// SetLoc vars
  arr = ctx->svar_env;
  //this array is in the formulae
  size = noll_vector_at (ctx->svar_stack, 0);
  ctx->svar_env = noll_var_array_new ();
  if (size > 0)
    noll_var_array_reserve (ctx->svar_env, size);
  for (uint_t i = 0; i < size; i++)
    noll_var_array_push (ctx->svar_env,
                         noll_var_copy (noll_vector_at (arr, i)));

#ifndef NDEBUG
  fprintf (stderr, "noll_context_restore_global: (end) %d lvars, %d svars\n",
           noll_vector_size (ctx->lvar_env),
           noll_vector_size (ctx->svar_env));
#endif
  return;
}

void
noll_context_fprint (FILE * f, noll_context_t * ctx)
{
  if (ctx == NULL)
    {
      fprintf (f, "ctx = NULL\n");
      return;
    }
  fprintf (f, "ctx = [pname => %s,\n", ctx->pname);

  /// Ref vars
  fprintf (f, "\tlvar_stack => [");
  if (ctx->lvar_stack == NULL)
    fprintf (f, "NULL");
  else
    {
      for (uint_t i = 0; i < noll_vector_size (ctx->lvar_stack); i++)
        fprintf (stdout, "%d,", noll_vector_at (ctx->lvar_stack, i));
    }
  fprintf (stdout, "\n\t]\n");

  fprintf (f, "\tlvar_env => ");
  if (ctx->lvar_env == NULL)
    fprintf (f, "NULL");
  else
    fprintf (f, "%d", noll_vector_size (ctx->lvar_env));

  /// SetLoc vars
  fprintf (stdout, "\n\tsvar_stack=[");
  if (ctx->svar_stack == NULL)
    fprintf (f, "NULL");
  else
    {
      for (uint_t i = 0; i < noll_vector_size (ctx->svar_stack); i++)
        fprintf (stdout, "%d,", noll_vector_at (ctx->svar_stack, i));
    }
  fprintf (stdout, "\n\t]\n");

  fprintf (f, "\tsvar_env => ");
  if (ctx->svar_env == NULL)
    fprintf (f, "NULL");
  else
    fprintf (f, "%d", noll_vector_size (ctx->svar_env));

  fprintf (stdout, "\n]\n");
}

/*
 * ======================================================================
 * Logic
 * ======================================================================
 */

/** Checks that the logic is supported.
 * @return 1 if the logic is correct, 0 otherwise
 */
int
noll_set_logic (noll_context_t * ctx, const char *logic)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (0 == strcmp (logic, "QF_NOLL"))
    return noll_form_logic = NOLL_LOGIC_NOLL;

  if (0 == strcmp (logic, "QF_SLRD"))
    return noll_form_logic = NOLL_LOGIC_SLRD;

  if (0 == strcmp (logic, "QF_S"))
    return noll_form_logic = NOLL_LOGIC_SLL;

  if (0 == strcmp (logic, "QF_SLRDI"))
    return noll_form_logic = NOLL_LOGIC_SLRDI;

  noll_error (0, "set-logic", "unknown logic");
  return noll_form_logic = NOLL_LOGIC_OTHER;
}

/*
 * ======================================================================
 * Commands
 * ======================================================================
 */

/**
 * Declare a variable or a field.
 * @pre: The @p name is not yet used or predefined.
 * @param ctx    context of the declaration, only globals
 * @param name   identifier declared
 * @param rty    (optionnal) record type
 * @return       @p rty if correct declaration, NULL otherwise 
 */
noll_type_t *
noll_mk_fun_decl (noll_context_t * ctx, const char *name, noll_type_t * rty)
{
  switch (rty->kind)
    {
    case NOLL_TYP_INT:
    case NOLL_TYP_BAGINT:
    case NOLL_TYP_RECORD:
      {
        /* global variable declaration
         * register it in the array of variables
         */
        noll_var_register (ctx->lvar_env, name, rty, NOLL_SCOPE_GLOBAL);
        if (rty != NULL)
          noll_vector_at (ctx->lvar_stack, 0) += 1;
        return rty;
      }
    case NOLL_TYP_SETLOC:
      {
        //variable declaration
        // register it in the array of variables
        noll_var_register (ctx->svar_env, name, rty, NOLL_SCOPE_GLOBAL);
        if (rty != NULL)
          noll_vector_at (ctx->svar_stack, 0) += 1;
        return rty;
      }
    case NOLL_TYP_FIELD:
      {
        //field declaration
        // register it in the array of fields
        noll_field_register (name, rty);
        assert (rty != NULL);
        return rty;
      }
    default:
      //error, return NULL below
      break;
    }
  return NULL;
}

/**
 * @brief Built the pure constraints from the expression @p exp and, 
 *        if correct syntax, push in @p pdef
 * No typechecking is done here! @see noll_mk_pred_rule_check_pure
 * 
 * @return 1 if correct, 0 otherwise
 */
int
noll_mk_pred_exp2rule_pure (noll_context_t * ctx, const char *name,
                            noll_exp_t * exp, uid_t pid,
                            noll_pred_rule_t * prule, uint_t nrec_p)
{
  if (ctx != ctx || pid != pid || nrec_p != nrec_p)
    return 0;                   // to remove warning on unsed parameters

  return noll_exp_push_pure (NULL, prule->pure, exp, prule->vars,
                             "Building predicate rule", name);
}


/**
 * @brief Built the space constraints from the expression @p exp and, 
 *        if correct syntax, push in @p pdef
 * Typechecking is done in @see noll_mk_pred_rule_check_*
 * 
 * @return 1 if correct, 0 otherwise
 */
int
noll_mk_pred_exp2rule_space (noll_context_t * ctx, const char *name,
                             noll_exp_t * exp, uid_t pid,
                             noll_pred_rule_t * prule, uint_t nrec_p)
{
  assert (exp != NULL);
  assert (prule != NULL);

  if (nrec_p != nrec_p)
    return 0;                   // to remove warning on unsed parameters

  switch (exp->discr)
    {
    case NOLL_F_EMP:
      {
        if (prule->pto == NULL && prule->nst == NULL && prule->rec == NULL)
          {
            prule->pto = noll_space_new ();     /// ASSERT: base case has pto=emp
          }
        else
          {
            noll_error (1, "Building predicate definition ", name);
            noll_error (1, "Bad rule", "(emp used not in base rule)");
            return 0;
          }
        return 1;
      }
    case NOLL_F_PTO:
      {
        noll_space_t *pto = noll_mk_form_pto (ctx, exp);
        if (pto == NULL)
          {
            noll_error (1, "Building predicate definition ", name);
            noll_error (1, "Bad recursive rule", "(bad pto)");
            return 0;
          }
        /// if starting from first parameter, then push in prule->pto
        /// otherwise in prule->nst
        if (pto->m.pto.sid == VID_FST_PARAM)
          {
            if (prule->pto != NULL)
              {
                noll_error (1, "Building predicate definition ", name);
                noll_error (1, "Bad recursive rule",
                            "(several pto in the rule)");
                return 0;
              }
            prule->pto = pto;
          }
        else
          {
            // this maybe not used?
            if (prule->nst == NULL)
              {
                prule->nst = noll_space_new ();
                prule->nst->kind = NOLL_SPACE_SSEP;
                prule->nst->is_precise = true;
                prule->nst->m.sep = noll_space_array_new ();
              }
            assert (prule->nst->kind == NOLL_SPACE_SSEP);
            noll_space_array_push (prule->nst->m.sep, pto);
          }
        return 1;
      }
    case NOLL_F_PRED:
      {
        noll_space_t *pcall = noll_mk_form_pred (ctx, prule->vars, name, exp);
#ifndef NDEBUG
        fprintf (stderr, "\nmk_exp2rule_space: new call: ");
        noll_space_fprint (stderr, prule->vars, NULL, pcall);
#endif
        if (pcall == NULL)
          {
            noll_error (1, "Building predicate definition ", name);
            noll_error (1, "Bad recursive rule", "(in recursive call)");
            return 0;
          }
        if (pcall->m.ls.pid == pid)
          {
            /// it is a recursive call
            /// TODO: the recursive call can be modified array ?
            noll_space_t *nrec = prule->rec;
            if (nrec == NULL)
              {
                nrec = noll_space_new ();
                nrec->kind = NOLL_SPACE_SSEP;
                nrec->is_precise = true;
                nrec->m.sep = noll_space_array_new ();
              }
            assert (nrec->kind == NOLL_SPACE_SSEP);
            assert (nrec->m.sep != NULL);
            noll_space_array_push (nrec->m.sep, pcall);
            prule->rec = nrec;
#ifndef NDEBUG
            fprintf (stderr,
                     "\nmk_pred_exp2rule_space: added rec call in rule:");
            noll_pred_rule_fprint (stderr, prule);
#endif
          }
        else
          {
            /// it is a nested call
            if (prule->nst == NULL)
              {
                prule->nst = noll_space_new ();
                prule->nst->kind = NOLL_SPACE_SSEP;
                prule->nst->is_precise = true;
                prule->nst->m.sep = noll_space_array_new ();
              }
            assert (prule->nst->kind == NOLL_SPACE_SSEP);
            noll_space_array_push (prule->nst->m.sep, pcall);
#ifndef NDEBUG
            fprintf (stderr,
                     "\nmk_pred_exp2rule_space: added nst call in rule:");
            noll_pred_rule_fprint (stderr, prule);
#endif
          }
        return 1;
      }
    case NOLL_F_LOOP:
      {
        noll_space_t *pcall = noll_mk_form_loop (ctx, prule->vars, name, exp);
        if ((pcall == NULL) || (pcall->m.ls.pid == pid))
          {
            noll_error (1, "Building predicate definition ", name);
            noll_error (1, "Bad recursive rule", "(loop use)");
            return 0;
          }
        /// it is a nested call
        if (prule->nst == NULL)
          {
            prule->nst = noll_space_new ();
            prule->nst->kind = NOLL_SPACE_SSEP;
            prule->nst->is_precise = true;
            prule->nst->m.sep = noll_space_array_new ();
          }
        assert (prule->nst->kind == NOLL_SPACE_SSEP);
        noll_space_array_push (prule->nst->m.sep, pcall);
        return 1;
      }
    default:
      {
        noll_error (1, "Building predicate definition ", name);
        noll_error (1, "Bad space formula in rule", "(operator not allowed)");
        return 0;
      }
    }
  return 1;
}


/**
 * @brief Built the rule from the expression @p exp and, 
 *        if correct, push in @p pdef
 * Called inside both base and recursive case, the set of vars is already
 * in @p prule->vars
 * @return 1 if correct, 0 otherwise
 */
int
noll_mk_pred_exp2rule (noll_context_t * ctx, const char *name,
                       noll_exp_t * exp, uid_t pid,
                       noll_pred_rule_t * prule, uint_t nrec_p, bool isSpace)
{
  assert (exp != NULL);

  int res = 1;
  if (exp->discr == NOLL_F_AND)
    {
      if (isSpace == true)
        {
          noll_error (1, "Building predicate definition ", name);
          noll_error (1, "Bad space formula", "(nested with pure)");
          return 0;
        }
      for (uint_t i = 0; (i < exp->size) && (res == 1); i++)
        res =
          noll_mk_pred_exp2rule (ctx, name, exp->args[i], pid, prule, nrec_p,
                                 false);
    }
  else if ((exp->discr >= NOLL_F_EQ) && (exp->discr <= NOLL_F_SUBSET))
    res = noll_mk_pred_exp2rule_pure (ctx, name, exp, pid, prule, nrec_p);
  else if (exp->discr == NOLL_F_TOBOOL)
    {
      if (isSpace == true)
        {
          noll_error (1, "Building predicate definition ", name);
          noll_error (1, "Bad space formula", "(conversion to bool)");
          return 0;
        }
      res =
        noll_mk_pred_exp2rule (ctx, name, exp->args[0], pid, prule, nrec_p,
                               true);
    }
  else if ((exp->discr == NOLL_F_PRED) ||
           (exp->discr >= NOLL_F_EMP && exp->discr <= NOLL_F_LOOP))
    {
      if (isSpace == false)
        {
          noll_error (1, "Building predicate definition ", name);
          noll_error (1, "Bad pure formula", "(no conversion to space)");
          return 0;
        }
      switch (exp->discr)
        {
        case NOLL_F_SSEP:
          {
            for (uint_t i = 0; i < exp->size && (res == 1); i++)
              res =
                noll_mk_pred_exp2rule (ctx, name, exp->args[i], pid, prule,
                                       nrec_p, true);
            break;
          }
        case NOLL_F_EMP:
        case NOLL_F_PTO:
        case NOLL_F_LOOP:
        case NOLL_F_PRED:
          {
            res =
              noll_mk_pred_exp2rule_space (ctx, name, exp, pid, prule,
                                           nrec_p);
            break;
          }
        default:
          {
            noll_error (1, "Building predicate definition ", name);
            noll_error (1, "Bad space formula",
                        "(no pto or conversion to space)");
            return 0;
          }
        }
    }
  else
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Bad formula in rule", "(operator not allowed)");
      return 0;
    }
#ifndef NDEBUG
  fprintf (stderr, "\nmk_pred_exp2rule: rule built for %s = ", name);
  noll_pred_rule_fprint (stderr, prule);
#endif
  return res;
}

/**
 * @brief Check the form of the pure contraints in @p prule
 * @return 1 if correct, 0 otherwise
 */
int
noll_mk_pred_rule_check_pure (const char *name,
                              noll_pred_rule_t * prule, uint_t nrec_p,
                              bool isRec)
{
  /// base rule
  if (isRec == false)
    {
      /// first argument shall be equal to second one or nil
      /*uint_t E = 1;
      if (nrec_p == 1)
        {
          /// shall be E = nil
          if ((prule->pure->m != NULL) &&
              (noll_pure_matrix_at (prule->pure, 0, E) != NOLL_PURE_EQ))
            {
              noll_error (1, "Building predicate definition ", name);
              noll_error (1, "Base rule not well defined ",
                          "(not fst = nil)");
              return 0;
            }
          // TODO NEW: check mset and length constraints
        }
      else if (nrec_p == 2)
        {
          /// shall be E = F
          uint_t F = 2;
          if ((prule->pure->m != NULL) &&
              (noll_pure_matrix_at (prule->pure, E, F) != NOLL_PURE_EQ))
            {
              noll_error (1, "Building predicate definition ", name);
              noll_error (1, "Base rule not well defined ",
                          "(not fst = snd)");
              return 0;
            }
          // TODO NEW: check mset and length constraints
        }*/
      // TODO NEW: check case of more recursive parameters
      // nrec_p == 4 for dll
    }
  else
    {
      /// isRec == true
      // if nrec_p == 1 then empty or E != nil and mset composition
      // if nrec_p == 2 then E != F and mset composition

      uint_t E = 1;
      if (nrec_p == 1)
        {
          /// may be E != nil
          if ((prule->pure->m != NULL) &&
              (noll_pure_matrix_at (prule->pure, 0, E) == NOLL_PURE_EQ))
            {
              noll_error (1, "Building predicate definition ", name);
              noll_error (1, "Recursive rule not well defined ",
                          "(not fst != nil)");
              return 0;
            }
          // TODO NEW: check mset and length constraints
        }
      else if (nrec_p == 2)
        {
          /// shall be E != F U B
          /*uint_t F = 2;
          if ((prule->pure->m != NULL) &&
              (noll_pure_matrix_at (prule->pure, E, F) != NOLL_PURE_NEQ))
            {
              noll_error (1, "Building predicate definition ", name);
              noll_error (1, "Recursive rule not well defined ",
                          "(not fst != snd)");
              return 0;
            }*/
          // TODO NEW: check for border parameters
          // TODO NEW: check mset and length constraints
        }
      // TODO NEW: check case of more recursive parameters
      // nrec_p == 4 for dll
    }
  return 1;
}

/**
 * @brief Check the form of the pto contraint in @p prule
 * @return 1 if correct, 0 otherwise
 */
int
noll_mk_pred_rule_check_pto (const char *name,
                             noll_pred_rule_t * prule, uint_t nrec_p)
{
  if (name != name || prule != prule || nrec_p != nrec_p)
    return 0;                   // to remove warning on unsed parameters

  //TODO NEW:
  /// the source of pto shall be the first parameter
  return 1;
}

/**
 * @brief Check the form of the nested calls in @p prule
 * Depends on logic.
 * @return 1 if correct, 0 otherwise
 */
int
noll_mk_pred_rule_check_nst (const char *name,
                             noll_pred_rule_t * prule, uint_t nrec_p)
{
  if (name != name || prule != prule || nrec_p != nrec_p)
    return 0;                   // to remove warning on unsed parameters

  //TODO NEW:
  /// the nested calls shall start from existential vars
  return 1;
}


/**
 * @brief Check the form of the recrusive calls in @p prule
 * Depends on logic.
 * @return 1 if correct, 0 otherwise
 */
int
noll_mk_pred_rule_check_rec (const char *name,
                             noll_pred_rule_t * prule, uint_t nrec_p)
{
  if (name != name || prule != prule || nrec_p != nrec_p)
    return 0;                   // to remove warning on unsed parameters
  //TODO NEW:
  /// the recursive calls shall only change the first argument?
  return 1;
}

/**
 * @brief Fill the base rule given by @p fequals in @p pdef, if correct
 * @return 1 if correct, 0 otherwise
 */
int
noll_mk_pred_rule_base (noll_context_t * ctx, const char *name,
                        noll_exp_t * fequals, uid_t pid,
                        noll_pred_binding_t * pdef, uint_t nrec_p)
{
  assert (fequals != NULL);

  int res = 1;
  /// the syntax is (and (equalities) (data?) (tobool emp)) 
  /// over variables in ctx->lvar_env

#ifndef NDEBUG
  fprintf (stdout, "pred_rule_base ctx: ");
  noll_context_fprint (stdout, ctx);
#endif

  /// create a new rule
  noll_pred_rule_t *prule = noll_pred_rule_new ();
  prule->vars = noll_var_array_new ();
  noll_var_array_copy (prule->vars, ctx->lvar_env);     // be carefull on pop
  prule->fargs = noll_vector_at (ctx->lvar_stack, 1);
  prule->pure = noll_pure_new (noll_vector_size (prule->vars));

  /// transform any expression with pure operators into 
  /// a pure or data formula in prule->pure
  res = noll_mk_pred_exp2rule (ctx, name, fequals, pid, prule, nrec_p, false);
  if (res == 0)
    return 0;

  res = noll_mk_pred_rule_check_pure (name, prule, nrec_p, false);      // is base

  /// check the spatial part to be emp
  if (prule->pto != NULL && prule->pto->kind != NOLL_SPACE_EMP)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Base case not well defined ", "(not precise)");
      return 0;
    }

  noll_pred_binding_push_rule (pdef, prule, false);

  return 1;
}

/**
 * Check the parameters of the predicate definition for logics <= NOLL_LOGIC_SLL
 * @return number of recursive parameters if no error, 0 otherwise
 */
int
noll_mk_pred_typecheck_par_SL (noll_context_t * ctx, const char *name,
                               uint_t npar, noll_pred_binding_t * pdef)
{
  /*
   * assert: number of parameters is at least 2 and
   * exactly the ctx->lvar_stack[1]
   */
  if (noll_vector_size (pdef->vars) <= 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Empty set of location parameters in ", name);
      return 0;
    }
  if (noll_vector_at (ctx->lvar_stack, 1) < 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect number of parameters (< 2) in ", name);
      return 0;
    }
  /* cond 0: all the parameters are of record type */
  for (uint_t i = 1; i <= npar; i++)
    {
      if (noll_var_record (pdef->vars, i) == UNDEFINED_ID)
        {
          noll_error (1, "Building predicate definition ", name);
          noll_error (1, "Parameter not of record type ", name);
          return 0;
        }
    }
  /*
   * cond 1: The first two parameters are of the same sort, the
   * sort of the predicate.
   *
   * TODO: for dll, the first four parameters shall have the same sort.
   * TODO: the sort of the remaining parameters shall be checked also!
   */
  /* first parameters is at position 1 in vars */
  uint_t pred_ty = noll_var_record (pdef->vars, 1);
  uint_t nrec_p = 0;
  while ((nrec_p < npar)
         && (noll_var_record (pdef->vars, nrec_p + 1) == pred_ty))
    nrec_p++;
#ifndef NDEBUG
  fprintf (stderr, "noll_mk_fun_def: Number of recursive parameters %d.\n",
           nrec_p);
#endif
  if (nrec_p < 2)
    {
      char str[10];
      snprintf (str, 10, "%d", nrec_p);
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect number of recursive parameters (< 2), i.e., ",
                  str);
      return 0;
    }
  /* nrec_p is the first parameter of type different from pred_ty */
  /* TODO: check the other parameters */
  /*
     for (uint_t i = nrec_p; i < npar; i++) {
     if (noll_var_record(ctx->lvar_env, i) == pred_ty) {
     char str[10];
     snprintf(str, 10, "%d", i);
     noll_error(1, "Building predicate definition ", name);
     noll_error(1, "Incorrect type of parameter ", str);
     return UNDEFINED_ID;
     }
     }
   */
  return nrec_p;
}

/**
 * @brief Check the parameters of the predicate definition 
 *        for logic NOLL_LOGIC_SLRDI
 * @return number of recursive parameters if no error, 0 otherwise
 */
int
noll_mk_pred_typecheck_par_SLRDI (noll_context_t * ctx, const char *name,
                                  uint_t npar, noll_pred_binding_t * pdef)
{
  if (ctx != ctx || name != name || npar == 0)
    return 0;                   // to remove warning on unused parameter

  /*
   * assert: number of parameters is at least 1 and
   * exactly the ctx->lvar_stack[1]
   */
  if (noll_vector_size (pdef->vars) <= 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Empty set of location parameters in ", name);
      return 0;
    }
  if (noll_vector_at (ctx->lvar_stack, 1) < 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect number of parameters (< 2) in ", name);
      return 0;
    }
  /*
   * assert: first parameters are of type record
   */
  uint_t npar_loc = 1;
  for (uint_t i = 1; i <= npar; i++)
    {
      if (noll_var_record (pdef->vars, i) == UNDEFINED_ID)
        {
          // TODO NEW: check that they are BagInt and Int
          continue;
        }
      else if (i > (npar_loc + 1))
        {
    	  /*TODO: first parameter should be location?
          /// record parameter not in first parameters
          noll_error (1, "Building predicate definition ", name);
          noll_error (1, "Parameter of record type shall be first in list",
                      name);
          return 0;*/
        }
      else
        npar_loc++;
    }
  /*
   * The first parameter is of type record
   */
  if (npar_loc < 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "First parameter shall be of reference type", name);
      return 0;
    }
  /// get the number of recursive parameters = same type as the first one
  uint_t pred_ty = noll_var_record (pdef->vars, 1);
  uint_t nrec_p = 0;
  while ((nrec_p < npar)
         && (noll_var_record (pdef->vars, nrec_p + 1) == pred_ty))
    nrec_p++;
#ifndef NDEBUG
  fprintf (stderr, "noll_mk_fun_def: Number of recursive parameters %d.\n",
           nrec_p);
#endif

  return nrec_p;
}


/**
 * Check the parameters of the predicate definition for logic NOLL_LOGIC_SLRDI
 * @return 1 if no error, 0 otherwise
 */
int
noll_mk_pred_typecheck (noll_context_t * ctx, const char *name,
                        uint_t npar, noll_type_t * rety,
                        noll_pred_binding_t * pdef)
{
  assert ((npar + 1) == noll_vector_size (pdef->vars));

  uint_t env_size = noll_vector_at (ctx->lvar_stack, 1);
  if ((noll_vector_at (ctx->lvar_stack, 1) > noll_vector_size (ctx->lvar_env))
      || (env_size != npar))
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect number of parameters in ", name);
      return 0;
    }
  /* assert:rety sort shall be Space */
  if ((rety == NULL) || (rety->kind != NOLL_TYP_SPACE))
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect result type (!= Space) ", name);
      return 0;
    }
  if (noll_form_logic != NOLL_LOGIC_SLRDI)
    return noll_mk_pred_typecheck_par_SL (ctx, name, npar, pdef);
  else
    return noll_mk_pred_typecheck_par_SLRDI (ctx, name, npar, pdef);
}

int
noll_mk_pred_rules (noll_context_t * ctx, const char *name,
                    noll_exp_t * def, uid_t pid, noll_pred_binding_t * pdef,
                    uint_t nrec_p);

/**
 * Build a user predicate definition using the input
 */
uid_t
noll_mk_pred_userdef (noll_context_t * ctx, const char *name, uint_t npar,
                      noll_type_t * rety, noll_exp_t * def, uid_t pid,
                      noll_pred_binding_t * pdef)
{
  /*
   * assert: no global variables except the "nil" constant
   * may be defined before the predicate definition,
   * since no global context is kept for the definition of
   * the predicate
   */
  if (noll_vector_at (ctx->lvar_stack, 0) >= 2)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Global variables declared before ", name);
      return UNDEFINED_ID;
    }
  /*
   * typechecks the predicate profile depending on the logic used,
   * and computes the number of recursive parameters >= 1
   */
  uint_t nrec_p = 0; // the number of location
  if ((nrec_p = noll_mk_pred_typecheck (ctx, name, npar, rety, pdef)) == 0)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Bad parameters!", " ");
      return UNDEFINED_ID;
    }

  pdef->pargs = (nrec_p == 2) ? 0 : 1;  // TODO NEW: no more interesting, keep only for dll

  /*
   * Check the syntax of predicates while
   * the predicate definition is built in pdef.
   */
  if (noll_mk_pred_rules (ctx, name, def, pid, pdef, nrec_p) == 0)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Bad rules!", "");
      return UNDEFINED_ID;
    }
  return pid;
}

/**
 * Check that the rule given in @p rule is a correct base or recursive rule.
 * If correct, store it in @p pdef.
 * @return 0 if not a correct rule, 1 otherwise
 */
int
noll_mk_pred_rule_SL (noll_context_t * ctx, const char *name,
                      noll_exp_t * rule, noll_pred_binding_t * pdef,
                      uint_t nrec_p)
{

  assert (pdef != NULL);
  assert (rule != NULL);

  if (ctx != ctx || name != name || rule != rule || pdef != pdef || nrec_p)
    return 0;                   // to remove warning on unused parameters

  // TODO NEW: from old noll_mk_pred_userdef
  return 1;
}

int
noll_mk_pred_rule_rec (noll_context_t * ctx, const char *name,
                       noll_exp_t * def, uid_t pid,
                       noll_pred_binding_t * pdef, uint_t nrec_p)
{
  assert (def != NULL);
  assert (def->discr == NOLL_F_EXISTS);

  int res = 1;
  // the form is (and (equalities) (data?) (tobool space)) 
  // over variables in def->p.quant.lvars
#ifndef NDEBUG
  fprintf (stdout, "pred_rule_rec ctx: ");
  noll_context_fprint (stdout, ctx);
  fprintf (stdout, "pred_rule_rec quant.lvars: ");
  noll_var_array_fprint (stdout, def->p.quant.lvars, "local vars");
  fprintf (stdout, "\n");
#endif
  noll_pred_rule_t *prule = noll_pred_rule_new ();
  prule->vars = def->p.quant.lvars;
  prule->fargs = noll_vector_at (ctx->lvar_stack, 1);
  prule->pure = noll_pure_new (noll_vector_size (prule->vars));

  /// transform the expression into a rule
  res =
    noll_mk_pred_exp2rule (ctx, name, def->args[0], pid, prule, nrec_p,
                           false);
  if (res == 0)
    return 0;

  /// check the pure part is compositional (recursive case)
  res = noll_mk_pred_rule_check_pure (name, prule, nrec_p, true);
  if (res == 0)
    return 0;

  /// check the pto of the spatial part 
  res = noll_mk_pred_rule_check_pto (name, prule, nrec_p);
  if (res == 0)
    return 0;

  /// check the nested part of the rule (depends on logic)
  res = noll_mk_pred_rule_check_nst (name, prule, nrec_p);
  if (res == 0)
    return 0;

  /// check the recursive part of the rule (depends on logic)
  res = noll_mk_pred_rule_check_rec (name, prule, nrec_p);
  if (res == 0)
    return 0;

  /// push the rule; it also fills the simple rule case 
  noll_pred_binding_push_rule (pdef, prule, true);

  return 1;
}

/**
 * @brief Fills the @p pdef with rules from @p def.
 * Each rule is checked to be well formed.
 * @return 0 if error, 1 otherwise
 */
int
noll_mk_pred_rule (noll_context_t * ctx, const char *name,
                   noll_exp_t * def, uid_t pid, noll_pred_binding_t * pdef,
                   uint_t nrec_p)
{
  assert (def != NULL);
  assert (pdef != NULL);

  int res = 1;
  if (def->discr == NOLL_F_OR)
    {
      for (uint_t i = 0; i < def->size && (res == 1); i++)
        res = noll_mk_pred_rule (ctx, name, def->args[i], pid, pdef, nrec_p);
    }
  else if (def->discr == NOLL_F_EXISTS)
    {
      /// recursive rule
      res = noll_mk_pred_rule_rec (ctx, name, def, pid, pdef, nrec_p);
    }
  else
    {
      /// shall be a basic rule
      res = noll_mk_pred_rule_base (ctx, name, def, pid, pdef, nrec_p);
    }
  return res;
}

int
noll_mk_pred_rules (noll_context_t * ctx, const char *name,
                    noll_exp_t * def, uid_t pid, noll_pred_binding_t * pdef,
                    uint_t nrec_p)
{

  assert (def != NULL);

  /// the def has the syntax (tospace (or ...))
  if (def->discr != NOLL_F_TOSPACE || def->size != 1)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "First operator is not 'tospace' ", "");
      return 0;
    }
  if (def->args == NULL || def->args[0]->discr != NOLL_F_OR)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Second operator is not 'or' ", "");
      return 0;
    }

  /// Fill the rules in pdef from def->args[0]
  /// checks are done for the well-formedness of each kind (base,rec) of rule
  int res = noll_mk_pred_rule (ctx, name, def->args[0], pid, pdef, nrec_p);
  if (res == 0)
    return 0;

  /// Verify that at least one base case is specified
  if (pdef->base_rules == NULL)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "No base rule provided!", "");
      return 0;
    }

  /// Verify that at least one recursive case is specified
  /* if (pdef->sigma_0 == NULL)
    {
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "No recursive rule provided!", "");
      return 0;
      }*/
  return 1;
}

/**
 * Build a predefined predicate definition using the input name in
 * ls, dll0a, nll0a, skl3
 */
uid_t
noll_mk_pred_predef (noll_context_t * ctx, const char *name, uint_t npar,
                     noll_type_t * rety, noll_exp_t * def, uid_t pid,
                     noll_pred_binding_t * pdef)
{
  assert (NULL != ctx);
  assert (NULL != name);
  assert (npar == npar);
  assert (NULL != rety);
  assert (NULL != def);
  // TODO: fill with predefined data depending on name
  return noll_mk_pred_userdef (ctx, name, npar, rety, def, pid, pdef);
}

/**
 * @brief Define a predicate.
 *
 * @param ctx   contains the parameters and local variables
 * @param name  name of the predicate
 * @param npar  number of parameters in the local context, first npar
 * @param rety  return type (shall be Space)
 * @param def   the term defining the predicate
 * @return      the identifier of the predicate defined or UNDEFINED_ID
 */
uint_t
noll_mk_fun_def (noll_context_t * ctx, const char *name, uint_t npar,
                 noll_type_t * rety, noll_exp_t * def)
{

  /// assert: name is unique
  if (ctx->pname != NULL && strcmp (ctx->pname, name))
    {
      /* name does not correspond to this predicate definition */
      noll_error (1, "Building predicate definition ", name);
      noll_error (1, "Incorrect predicate name in ", name);
      return UNDEFINED_ID;
    }

  /*
   * build the record for this predicate definition and register it
   */
  noll_pred_binding_t *pdef = noll_pred_binding_new ();
  /// NEW: context contains only parameters
  assert ((npar + 1) == noll_vector_size (ctx->lvar_env));
  pdef->fargs = npar;
  pdef->vars = ctx->lvar_env;   /// NEW: no need to copy the context

  /// NEW: push the binding in the predicate definition to allow typechecking
  uid_t pid = noll_pred_register (name, pdef);

  if (noll_option_is_preds_builtin () == false)
    /// not fixed definitions, build the predicate
    pid = noll_mk_pred_userdef (ctx, name, npar, rety, def, pid, pdef);
  else
    /// predefined predicate
    pid = noll_mk_pred_predef (ctx, name, npar, rety, def, pid, pdef);

  if (UNDEFINED_ID == pid)
    noll_pred_binding_delete (pdef);

  /* reset the predicate name in the context */
  if (ctx->pname != NULL)
    free (ctx->pname);
  ctx->pname = NULL;

#ifndef NDEBUG
  fprintf (stderr, "Predicate built: ");
  noll_pred_fprint (stderr, pid);
#endif
  return pid;
}

int
noll_assert (noll_context_t * ctx, noll_exp_t * term)
{
  //check that the formula is not null
  if (!term)
    {
      noll_error (1, "noll_assert", "null formula");
      return 0;
    }
  /* if the local environment is not empty, signal it */
  if ((noll_vector_size (ctx->lvar_stack) > 1)
      || (noll_vector_size (ctx->svar_stack) > 1))
    {
      noll_error (1, "noll_assert", "non empty local environment");
      return 0;
    }
  /* typecheck the formula and do simplifications, if needed */
  noll_exp_t *form = noll_exp_typecheck (ctx, term);
  if (form == NULL)
    {
      noll_error (1, "noll_assert", "typechecking error");
      return 0;
    }
  /* translate into a formula and
   * fill the positive or negative formulae depending on the first operator
   */
  if (form->discr == NOLL_F_NOT)
    noll_exp_push (ctx, form->args[0], 0);
  /* push in negative */
  else
    noll_exp_push (ctx, form, 1);
  /* push in positive */
  /* restore the global environment */
  noll_context_restore_global (ctx);
  return 1;
}

/**
 * Sets the command.
 * @return if only one formula then 0, 1, -1 for sat, unsat, unknown
 *         if entailment (two formulas) then 0, 1, -1 for valid, invalid, unknown
 */
int
noll_check (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);               // to avoid "unused parameter" warning
    }
  if (noll_error_parsing > 0)
    {
      assert (noll_prob->smt_fname != NULL);
      noll_error (0, "noll_check", "stop because of parsing error");
      return 0;
    }

  noll_entl_set_cmd (NOLL_FORM_SAT);
  return noll_entl_solve ();
}

/*
 * ======================================================================
 * Terms
 * ======================================================================
 */

/** Adds the variable to the topmost local array in the context,
 * depending of this type.
 */
void
noll_push_var (noll_context_t * ctx, const char *name, noll_type_t * vty)
{
  if (!ctx)
    return;
  uid_t vid = UNDEFINED_ID;
  if ((vty->kind == NOLL_TYP_RECORD) ||
      (vty->kind == NOLL_TYP_INT) || (vty->kind == NOLL_TYP_BAGINT))
    {
      assert (ctx->lvar_env != NULL);
      noll_var_t *v = noll_var_new (name, vty, NOLL_SCOPE_LOCAL);
      noll_var_array_push (ctx->lvar_env, v);
      v->vid = noll_vector_size (ctx->lvar_env) - 1;
      //update the number of elements in the top of the stack
      uint_t top_stack = noll_vector_size (ctx->lvar_stack) - 1;
      noll_vector_at (ctx->lvar_stack, top_stack) += 1;
    }
  else if (vty->kind == NOLL_TYP_SETLOC)
    {
      assert (ctx->svar_env != NULL);
      noll_var_t *v = noll_var_new (name, vty, NOLL_SCOPE_LOCAL);
      noll_var_array_push (ctx->svar_env, v);
      v->vid = noll_vector_size (ctx->svar_env) - 1;
      //update the number of elements in the top of the stack
      uint_t top_stack = noll_vector_size (ctx->svar_stack) - 1;
      noll_vector_at (ctx->svar_stack, top_stack) += 1;
    }
  else
    assert (0);
}

int
noll_push_quant (noll_context_t * ctx)
{
#ifndef NDEBUG
  fprintf (stdout, "push_quant start: \n");
  noll_context_fprint (stdout, ctx);
#endif
  //the NOLL supports only 2 levels of nesting and only inside define-fun
  if (noll_vector_size (ctx->lvar_stack) >= 3)
    {
      noll_error (0, "noll_push_quant", "too much nesting");
      return 0;
    }
  noll_uint_array_push (ctx->lvar_stack, 0);
  noll_uint_array_push (ctx->svar_stack, 0);
  return 1;
}

int
noll_pop_quant (noll_context_t * ctx)
{
#ifndef NDEBUG
  fprintf (stdout, "pop_quant start: \n");
  noll_context_fprint (stdout, ctx);
#endif
  if (noll_vector_size (ctx->lvar_stack) <= 1)
    {
      noll_error (0, "noll_pop_quant", "too much pops");
      return 0;
    }
  //NEW: remove vars from context
  uint_t lvar_pop = noll_vector_last (ctx->lvar_stack);
  for (uint_t i = 0; i < lvar_pop; i++)
    noll_var_array_pop (ctx->lvar_env);
  uint_t svar_pop = noll_vector_last (ctx->svar_stack);
  for (uint_t i = 0; i < svar_pop; i++)
    noll_var_array_pop (ctx->svar_env);
  //OLD only:
  noll_uint_array_pop (ctx->lvar_stack);
  noll_uint_array_pop (ctx->svar_stack);
#ifndef NDEBUG
  fprintf (stdout, "pop_quant end: ");
  noll_context_fprint (stdout, ctx);
#endif
  return 1;
}

noll_exp_t *
noll_mk_op (noll_expkind_t f, noll_exp_t ** args, uint_t size)
{
  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = f;
  res->size = size;
  res->args = NULL;
  if (size != 0)
    {
      res->args = (noll_exp_t **) malloc (size * sizeof (noll_exp_t *));
      for (uint_t i = 0; i < size; i++)
        res->args[i] = args[i];
    }
  return res;
}

/**
 * @brief Build a term for field application
 */
noll_exp_t *
noll_mk_dfield (noll_context_t * ctx, const char *name, noll_exp_t ** args,
                uint_t size)
{
  if (ctx != ctx)
    return 0;                   // to remove warning on unused parameter
  /// search the field
  uid_t fid = noll_field_array_find (name);
  if ((fid == UNDEFINED_ID) || (size != 1))
    return NULL;
  noll_exp_t *res = noll_mk_op (NOLL_F_DFIELD, args, size);
  return res;
}

/**
 * This function is called
 * - either for predicate definition
 * - either at the top-most of a NOLL formula
 */
noll_exp_t *
noll_mk_exists (noll_context_t * ctx, noll_exp_t * term)
{
  //the exist variables are at the end of the stack,
  //i.e., top of ctx->* var_stack element,
  //in ctx->* _env

  uint_t nb_exists_lvar = noll_vector_last (ctx->lvar_stack);
  uint_t nb_exists_svar = noll_vector_last (ctx->svar_stack);
#ifndef NDEBUG
  fprintf (stdout, "mk_exists start lvar_stack=[");
  for (uint_t i = 0; i < noll_vector_size (ctx->lvar_stack); i++)
    fprintf (stdout, "%d,", noll_vector_at (ctx->lvar_stack, i));
  fprintf (stdout, "]\n");
  fprintf (stdout, "mk_exists exists lvar=[");
  for (uint_t i = nb_exists_lvar; i > 0; i--)
    {
      noll_var_t *vi = noll_vector_at (ctx->lvar_env,
                                       noll_vector_size (ctx->lvar_env) - i);
      fprintf (stdout, "%s,", vi->vname);
    }
  fprintf (stdout, "]\n");
  fprintf (stdout, "mk_exists start svar_stack=[");
  for (uint_t i = 0; i < noll_vector_size (ctx->svar_stack); i++)
    fprintf (stdout, "%d,", noll_vector_at (ctx->svar_stack, i));
  fprintf (stdout, "]\n");
  fprintf (stdout, "mk_exists exists svar=[");
  for (uint_t i = nb_exists_svar; i > 0; i--)
    {
      noll_var_t *vi = noll_vector_at (ctx->svar_env,
                                       noll_vector_size (ctx->svar_env) - i);
      fprintf (stdout, "%s,", vi->vname);
    }
  fprintf (stdout, "]\n");
#endif
  noll_exp_t *res = noll_mk_op (NOLL_F_EXISTS, &term, 1);
  res->p.quant.lvars = noll_var_array_new ();   // NEW: keep the context of variables
  noll_var_array_copy (res->p.quant.lvars, ctx->lvar_env);
  res->p.quant.lstart = noll_vector_size (ctx->lvar_env) - nb_exists_lvar;
  res->p.quant.lend = noll_vector_size (ctx->lvar_env);
  res->p.quant.svars = noll_var_array_new ();   // NEW: keep the context of variables
  noll_var_array_copy (res->p.quant.svars, ctx->svar_env);
  res->p.quant.sstart = noll_vector_size (ctx->svar_env) - nb_exists_svar;
  res->p.quant.send = noll_vector_size (ctx->svar_env);
  return res;
}

/** Used to build terms from user-defined predicates
 *  or symbols (variables or fields) or true/false.
 * @param ctx contains the local context
 * @param name function name
 * @param args array of size of arguments
 * @param size length of the array above
 * @return the term built
 */
noll_exp_t *
noll_mk_app (noll_context_t * ctx, const char *name,
             noll_exp_t ** args, uint_t size)
{
  if (size == 0)
    {
      /// is 0-arity keywords or variable
      if (strcmp (name, "true") == 0)
        return noll_mk_true (ctx);
      if (strcmp (name, "false") == 0)
        return noll_mk_false (ctx);
      if (strcmp (name, "emp") == 0)
        return noll_mk_emp (ctx);
      if (strcmp (name, "junk") == 0)
        return noll_mk_junk (ctx);
      if (strcmp (name, "emptybag") == 0)
        return noll_mk_emptybag (ctx);
      return noll_mk_symbol (ctx, name);
    }
  /// is a data field application
  if (size == 1)
    {
      noll_exp_t *res = noll_mk_dfield (ctx, name, args, size);
      if (res != NULL)
        return res;
    }
  /// is a predicate call(name args) or a data field function
  return noll_mk_pred (ctx, name, args, size);
}

/** @brief Build a term including the integer given by @p str.
 */
noll_exp_t *
noll_mk_number (noll_context_t * ctx, const char *str)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = noll_mk_op (NOLL_F_INT, NULL, 0);
  char *endstr;
  res->p.value = strtol (str, &endstr, 10);
  if (endstr == NULL)
    {
      /// bad translation to integer
      noll_error_id (1, "noll_mk_number", str);
      return NULL;
    }
  return res;
}

/** @brief Build a term from this variable or field.
 */
noll_exp_t *
noll_mk_symbol (noll_context_t * ctx, const char *name)
{
  assert (ctx && name);
  noll_exp_t *ret = NULL;
  uint_t sid = UNDEFINED_ID;
  noll_type_t *typ = NULL;
#ifndef NDEBUG
  fprintf (stdout, "mk_symbol: start %s\n", name);
  fflush (stdout);
#endif
  /* special case of 'emptybag' */
  if (strcmp (name, "emptybag") == 0)
    {
      ret = noll_mk_op (NOLL_F_EMPTYBAG, NULL, 0);
      return ret;
    }
  //search the variable environment
  // -search in the location env
  assert (ctx->lvar_env != NULL);
  sid = noll_var_array_find_local (ctx->lvar_env, name);
  if (sid != UNDEFINED_ID)
    typ = (noll_vector_at (ctx->lvar_env, sid))->vty;
  else
    {
      //search in the sloc env
      assert (ctx->svar_env != NULL);
      sid = noll_var_array_find_local (ctx->svar_env, name);
      if (sid != UNDEFINED_ID)
        typ = (noll_vector_at (ctx->svar_env, sid))->vty;
    }
  if (typ != NULL)
    {
      if ((typ->kind == NOLL_TYP_RECORD) ||
          (typ->kind == NOLL_TYP_INT) || (typ->kind == NOLL_TYP_BAGINT))
        {
          ret = noll_mk_op (NOLL_F_LVAR, NULL, 0);
          ret->p.sid = sid;
        }
      else
        {
          ret = noll_mk_op (NOLL_F_SVAR, NULL, 0);
          ret->p.sid = sid;
        }
#ifndef NDEBUG
      fprintf (stdout, "mk_symbol: local %s (id %d)\n", name, ret->p.sid);
#endif
      return ret;
    }
  /* else, it shall be a field */
  if (name[0] == '?')
    {
      //fields cannot start with ?
      noll_error_id (1, "noll_mk_symbol", name);
      return NULL;
    }
  sid = noll_field_array_find (name);
  if (sid != UNDEFINED_ID)
    {
      ret = noll_mk_op (NOLL_F_FIELD, NULL, 0);
      ret->p.sid = sid;
      return ret;
    }
  /* else error */
  noll_error_id (1, "noll_mk_symbol", name);
  return NULL;
}

noll_exp_t *
noll_mk_pred (noll_context_t * ctx, const char *name,
              noll_exp_t ** args, uint_t size)
{
  assert (name != NULL);
  assert (args != NULL);
  if (size < 2)
    {
      char *msg = strdup (name);
      noll_error_args (1, msg, size, ">= 2");
      free (msg);
      return NULL;
    }
  //search the predicate name
  uint_t pid = noll_pred_array_find (name);
  if (pid == UNDEFINED_ID)
    {
      //it is maybe a recursive definition
      if ((noll_vector_size (ctx->lvar_stack) < 3) ||
          ((ctx->pname != NULL) && (strcmp (ctx->pname, name) > 0)))
        {                       // not inside a recursive rule 
          // or not a recursive call
          noll_error_id (1, "noll_mk_pred", name);
          return NULL;
        }
      else if (ctx->pname == NULL)
        //a predicate definition, fill pname
        ctx->pname = strdup (name);
    }
  //typechecking is done afterwards, build the expression
  noll_exp_t *res = noll_mk_op (NOLL_F_PRED, args, size);
  res->p.sid = pid;
  return res;
}

noll_exp_t *
noll_mk_true (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_TRUE;
  return res;
}

noll_exp_t *
noll_mk_false (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_FALSE;
  return res;
}

noll_exp_t *
noll_mk_and (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (size <= 0)
    /*
     * 0 arguments is
     * false
     */
    return noll_mk_false (ctx);
  else if (size == 1)
    return args[0];
  return noll_mk_op (NOLL_F_AND, args, size);
}

noll_exp_t *
noll_mk_or (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (size <= 0)
    /*
     * 0 arguments is
     * true
     */
    return noll_mk_true (ctx);
  else if (size == 1)
    return args[0];
  return noll_mk_op (NOLL_F_OR, args, size);
}

noll_exp_t *
noll_mk_not (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_not", size, "= 1");
  /// remove negation on atoms, when possible
  noll_exp_t *e = args[0];
  if (e->discr == NOLL_F_EQ)
    {
      e->discr = NOLL_F_DISTINCT;
    }
  else if (e->discr == NOLL_F_DISTINCT)
    {
      e->discr = NOLL_F_EQ;
    }
  else if (e->discr == NOLL_F_LT)
    {
      e->discr = NOLL_F_GE;
    }
  else if (e->discr == NOLL_F_GT)
    {
      e->discr = NOLL_F_LE;
    }
  else if (e->discr == NOLL_F_LE)
    {
      e->discr = NOLL_F_GT;
    }
  else if (e->discr == NOLL_F_GE)
    {
      e->discr = NOLL_F_LT;
    }
  else if (e->discr == NOLL_F_INLOC)
    {
      e->discr = NOLL_F_NILOC;
    }
  else if (e->discr == NOLL_F_NILOC)
    {
      e->discr = NOLL_F_INLOC;
    }
  else
    e = noll_mk_op (NOLL_F_NOT, args, size);
  return e;
}

noll_exp_t *
noll_mk_implies (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_impl", size, "= 2");
  return noll_mk_op (NOLL_F_IMPLIES, args, size);
}

noll_exp_t *
noll_mk_eq (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_eq", size, "= 2");
  return noll_mk_op (NOLL_F_EQ, args, size);
}

noll_exp_t *
noll_mk_distinct (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_distinct", size, "= 2");
  return noll_mk_op (NOLL_F_DISTINCT, args, size);
}

noll_exp_t *
noll_mk_ite (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 3)
    noll_error_args (1, "noll_mk_ite", size, "= 3");
  return noll_mk_op (NOLL_F_ITE, args, size);
}

noll_exp_t *
noll_mk_lt (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_lt", size, "= 2");
  return noll_mk_op (NOLL_F_LT, args, size);
}

noll_exp_t *
noll_mk_gt (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_gt", size, "= 2");
  return noll_mk_op (NOLL_F_GT, args, size);
}

noll_exp_t *
noll_mk_le (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_le", size, "= 2");
  return noll_mk_op (NOLL_F_LE, args, size);
}

noll_exp_t *
noll_mk_ge (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_ge", size, "= 2");
  return noll_mk_op (NOLL_F_GE, args, size);
}

noll_exp_t *
noll_mk_plus (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_plus", size, "< 2");
  return noll_mk_op (NOLL_F_PLUS, args, size);
}

noll_exp_t *
noll_mk_minus (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_minus", size, "= 2");
  return noll_mk_op (NOLL_F_MINUS, args, size);
}

noll_exp_t *
noll_mk_bag (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_bag", size, "= 1");
  return noll_mk_op (NOLL_F_BAG, args, size);
}

noll_exp_t *
noll_mk_emptybag (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_EMPTYBAG;
  res->args = NULL;
  res->size = 0;
  return res;
}

noll_exp_t *
noll_mk_bagunion (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_bagunion", size, ">= 2");
  return noll_mk_op (NOLL_F_BAGUNION, args, size);
}

noll_exp_t *
noll_mk_bagminus (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_bagminus", size, "= 2");
  return noll_mk_op (NOLL_F_BAGMINUS, args, size);
}

noll_exp_t *
noll_mk_subset (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_subset", size, "= 2");
  return noll_mk_op (NOLL_F_SUBSET, args, size);
}

noll_exp_t *
noll_mk_emp (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_EMP;
  return res;
}

noll_exp_t *
noll_mk_junk (noll_context_t * ctx)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  noll_exp_t *res = (noll_exp_t *) malloc (sizeof (struct noll_exp_t));
  res->discr = NOLL_F_JUNK;
  return res;
}

noll_exp_t *
noll_mk_wsep (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_wsep", size, ">= 2");
  return noll_mk_op (NOLL_F_WSEP, args, size);
}

noll_exp_t *
noll_mk_ssep (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_ssep", size, ">= 2");
  return noll_mk_op (NOLL_F_SSEP, args, size);
}

noll_exp_t *
noll_mk_pto (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_pto", size, "= 2");
  return noll_mk_op (NOLL_F_PTO, args, size);
}

noll_exp_t *
noll_mk_ref (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mksref", size, ">= 2");
  return noll_mk_op (NOLL_F_REF, args, size);
}

noll_exp_t *
noll_mk_sref (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_sref", size, ">= 2");
  return noll_mk_op (NOLL_F_SREF, args, size);
}

noll_exp_t *
noll_mk_index (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_index", size, "= 2");
  return noll_mk_op (NOLL_F_INDEX, args, size);
}

noll_exp_t *
noll_mk_sloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_sloc", size, "= 1");
  return noll_mk_op (NOLL_F_SLOC, args, size);
}

noll_exp_t *
noll_mk_unloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size < 2)
    noll_error_args (1, "noll_mk_unloc", size, ">= 2");
  return noll_mk_op (NOLL_F_UNLOC, args, size);
}

noll_exp_t *
noll_mk_inloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_inloc", size, "= 2");
  return noll_mk_op (NOLL_F_INLOC, args, size);
}

noll_exp_t *
noll_mk_eqloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_eqloc", size, "= 2");
  return noll_mk_op (NOLL_F_EQLOC, args, size);
}

noll_exp_t *
noll_mk_leloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_leloc", size, "= 2");
  return noll_mk_op (NOLL_F_LELOC, args, size);
}

noll_exp_t *
noll_mk_seloc (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 2)
    noll_error_args (1, "noll_mk_seloc", size, "= 2");
  return noll_mk_op (NOLL_F_SELOC, args, size);
}

noll_exp_t *
noll_mk_tobool (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_tobool", size, "= 1");
  return noll_mk_op (NOLL_F_TOBOOL, args, size);
}

noll_exp_t *
noll_mk_tospace (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_tospace", size, "= 1");
  return noll_mk_op (NOLL_F_TOSPACE, args, size);
}

noll_exp_t *
noll_mk_loop (noll_context_t * ctx, noll_exp_t ** args, uint_t size)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (size != 1)
    noll_error_args (1, "noll_mk_loop", size, "= 1");
  return noll_mk_op (NOLL_F_LOOP, args, size);
}


/*
 * ======================================================================
 * Printing
 * ======================================================================
 */

void
noll_exp_printf (FILE * f, noll_context_t * ctx, noll_exp_t * e)
{
  assert (f);
  if (!e)
    {
      fprintf (f, "null\n");
      return;
    }
  switch (e->discr)
    {
    case NOLL_F_FALSE:
      {
        fprintf (f, " false ");
        return;
      }
    case NOLL_F_TRUE:
      {
        fprintf (f, " true ");
        return;
      }
    case NOLL_F_LVAR:
      {
        fprintf (f, " %s ",
                 noll_var_name (ctx->lvar_env, e->p.sid, NOLL_TYP_RECORD));
        return;
      }
    case NOLL_F_SVAR:
      {
        fprintf (f, " %s ",
                 noll_var_name (ctx->svar_env, e->p.sid, NOLL_TYP_SETLOC));
        return;
      }
    case NOLL_F_FIELD:
      {
        fprintf (f, " %s ", noll_field_name (e->p.sid));
        return;
      }
    case NOLL_F_INT:
      {
        fprintf (f, " %ld ", e->p.value);
        return;
      }
    case NOLL_F_DFIELD:
      {
        fprintf (f, " (");
        break;
      }
    case NOLL_F_EMP:
      {
        fprintf (f, " emp ");
        return;
      }
    case NOLL_F_JUNK:
      {
        fprintf (f, " junk ");
        return;
      }
    case NOLL_F_NOT:
      {
        fprintf (f, " (not \n");
        break;
      }
    case NOLL_F_AND:
      {
        fprintf (f, " (and \n\t");
        break;
      }
    case NOLL_F_OR:
      {
        fprintf (f, " (or \n\t");
        break;
      }
    case NOLL_F_IMPLIES:
      {
        fprintf (f, " (=> \n\t");
        break;
      }
    case NOLL_F_EXISTS:
      {
        fprintf (f, " (exists (");
        for (uint_t i = e->p.quant.lstart; i < e->p.quant.lend; i++)
          {
            noll_var_t *vi = noll_vector_at (e->p.quant.lvars, i);
            fprintf (f, " (%s %s) ", vi->vname, noll_record_name (noll_var_record       // NEW: could be replaces by type
                                                                  (e->p.
                                                                   quant.lvars,
                                                                   i)));
          }
        for (uint_t i = e->p.quant.sstart; i < e->p.quant.send; i++)
          {
            noll_var_t *vi = noll_vector_at (e->p.quant.svars, i);
            fprintf (f, " (%s SetLoc) ", vi->vname);
          }
        fprintf (f, " )\n\t");
        break;
      }
    case NOLL_F_PRED:
      {
        const char *pred_name = noll_pred_name (e->p.sid);
        assert (NULL != pred_name);
        fprintf (f, " (%s ", pred_name);
        break;
      }
    case NOLL_F_EQ:
      {
        fprintf (f, " (= ");
        break;
      }
    case NOLL_F_DISTINCT:
      {
        fprintf (f, " (distinct ");
        break;
      }
    case NOLL_F_WSEP:
      {
        fprintf (f, " (wsep \n\t");
        break;
      }
    case NOLL_F_SSEP:
      {
        fprintf (f, " (ssep \n\t");
        break;
      }
    case NOLL_F_PTO:
      {
        fprintf (f, " (pto ");
        break;
      }
    case NOLL_F_REF:
      {
        fprintf (f, " (ref ");
        break;
      }
    case NOLL_F_SREF:
      {
        fprintf (f, " (sref \n\t");
        break;
      }
    case NOLL_F_INDEX:
      {
        fprintf (f, " (index ");
        break;
      }
    case NOLL_F_SLOC:
      {
        fprintf (f, " (sloc ");
        break;
      }
    case NOLL_F_UNLOC:
      {
        fprintf (f, " (unloc ");
        break;
      }
    case NOLL_F_INLOC:
      {
        fprintf (f, " (inloc ");
        break;
      }
    case NOLL_F_NILOC:
      {
        fprintf (f, " (notinloc ");
        break;
      }
    case NOLL_F_EQLOC:
      {
        fprintf (f, " (eqloc ");
        break;
      }
    case NOLL_F_LELOC:
      {
        fprintf (f, " (leloc ");
        break;
      }
    case NOLL_F_SELOC:
      {
        fprintf (f, " (seloc ");
        break;
      }
    case NOLL_F_TOBOOL:
      {
        fprintf (f, " (tobool \n\t");
        break;
      }
    case NOLL_F_TOSPACE:
      {
        fprintf (f, " (tospace \n\t");
        break;
      }
    case NOLL_F_LOOP:
      {
        fprintf (f, " (loop \n\t");
        break;
      }
    case NOLL_F_ITE:
      {
        fprintf (f, " (ite ");
        break;
      }
    case NOLL_F_LT:
      {
        fprintf (f, " (< ");
        break;
      }
    case NOLL_F_GT:
      {
        fprintf (f, " (> ");
        break;
      }
    case NOLL_F_LE:
      {
        fprintf (f, " (<= ");
        break;
      }
    case NOLL_F_GE:
      {
        fprintf (f, " (>= ");
        break;
      }
    case NOLL_F_BAG:
      {
        fprintf (f, " (bag ");
        break;
      }
    case NOLL_F_EMPTYBAG:
      {
        fprintf (f, " emptybag ");
        break;
      }
    case NOLL_F_BAGUNION:
      {
        fprintf (f, " (bagunion ");
        break;
      }
    case NOLL_F_BAGMINUS:
      {
        fprintf (f, " (bagminus ");
        break;
      }
    case NOLL_F_SUBSET:
      {
        fprintf (f, " (subset ");
        break;
      }
    default:
      {
        fprintf (f, " (unknown \n\t");
        break;
      }
    }
  if (e->args)
    {
      uint_t i;
      for (i = 0; i < e->size; i++)
        {
          noll_exp_printf (f, ctx, e->args[i]);
          fprintf (f, "\n\t");
        }
    }
  fprintf (f, " )\n");
}

/*
 * ======================================================================
 * Typechecking
 * ======================================================================
 */

/**
 * Typechecks an AND formula in the local environment env.
 */
noll_exp_t *
noll_exp_typecheck_and (noll_context_t * ctx, noll_exp_t * e)
{
  if (&ctx != &ctx)
    {
      assert (0);
    }

  if (!e)
    return e;
  /// top formulas shall be linked by and or any other atomic boolean
  /// or tobool, expected type bool
  assert ((e->discr == NOLL_F_AND) ||
          (e->discr == NOLL_F_TRUE) ||
          (e->discr == NOLL_F_FALSE) ||
          (e->discr == NOLL_F_EQ) ||
          (e->discr == NOLL_F_DISTINCT) ||
          (e->discr == NOLL_F_LT) ||
          (e->discr == NOLL_F_GT) ||
          (e->discr == NOLL_F_LE) ||
          (e->discr == NOLL_F_GE) ||
          (e->discr == NOLL_F_SUBSET) || (e->discr == NOLL_F_TOBOOL));
  return e;
}

/**
 * Typechecks an EXISTS formula.
 */
noll_exp_t *
noll_exp_typecheck_exists (noll_context_t * ctx, noll_exp_t * e)
{
  if (!e)
    return e;
  if (e->discr == NOLL_F_EXISTS)
    {
      //top formula shall non be empty, expected type bool
      assert (e->size == 1);
      e->args[0] = noll_exp_typecheck_and (ctx, e->args[0]);
      if (!e->args[0])
        return NULL;
      return e;
    }
  return noll_exp_typecheck_and (ctx, e);
}

/** Typechecks the expression and simplifies it.
 *  Expected type is boolean at the top level.
 * @param ctx  context with global variables
 * @param e    formula to be typechecked
 * @return the new (simplified) formula
 */
noll_exp_t *
noll_exp_typecheck (noll_context_t * ctx, noll_exp_t * e)
{
  if (!e)
    return e;
  switch (e->discr)
    {
    case NOLL_F_TRUE:
    case NOLL_F_FALSE:
      return e;
    case NOLL_F_NOT:
      {
        assert (e->size == 1);
        noll_exp_t *se = noll_exp_typecheck_exists (ctx, e->args[0]);
        if (se == NULL)
          return NULL;
        e->args[0] = se;
        return e;
      }
    case NOLL_F_TOBOOL:
    case NOLL_F_AND:
      return noll_exp_typecheck_and (ctx, e);
    case NOLL_F_IMPLIES:
      {
        assert (e->size == 2);
        //done in mk_implies
        e->args[0] = noll_exp_typecheck_exists (ctx, e->args[0]);
        e->args[1] = noll_exp_typecheck_exists (ctx, e->args[1]);
        if (!e->args[0] || !e->args[1])
          return NULL;
        return e;
      }
    case NOLL_F_EXISTS:
      {
        return noll_exp_typecheck_exists (ctx, e);
      }
    default:
      {
        noll_error (0, "noll_exp_typecheck", "syntax error in formula");
        return NULL;
      }
    }
}

/*
 * ======================================================================
 * Translation to formula
 * ======================================================================
 */

/**
 * @brief Translate the SMTLIB AST into the internal data AST.
 * Because the translation is direct, no need to push in a formula.
 */
noll_dterm_t *
noll_exp_push_dterm (noll_exp_t * e, noll_var_array * lenv)
{
  assert (NULL != e);

#ifndef NDEBUG
  fprintf (stdout, "push_dterm: discr=%d, size=%d\n", e->discr, e->size);
#endif

  noll_dterm_t *dt = noll_dterm_new ();
  switch (e->discr)
    {
    case NOLL_F_INT:
      {
        dt->kind = NOLL_DATA_INT;
        dt->typ = NOLL_TYP_INT;
        dt->p.value = e->p.value;
        break;
      }
    case NOLL_F_LVAR:
      {
        dt->kind = NOLL_DATA_VAR;
        noll_var_t *v = noll_vector_at (lenv, e->p.sid);
        dt->typ = v->vty->kind;
        dt->p.sid = e->p.sid;
        break;
      }
    case NOLL_F_EMPTYBAG:
      {
        dt->kind = NOLL_DATA_EMPTYBAG;
        dt->typ = NOLL_TYP_BAGINT;
        break;
      }
    case NOLL_F_DFIELD:
      {
        dt->kind = NOLL_DATA_FIELD;
        dt->typ = NOLL_TYP_INT;
        break;
      }
    case NOLL_F_ITE:
      {
        dt->kind = NOLL_DATA_ITE;
        dt->typ = NOLL_TYP_INT; /// NEW: or BagInt?
        break;
      }
    case NOLL_F_PLUS:
      {
        dt->kind = NOLL_DATA_PLUS;
        dt->typ = NOLL_TYP_INT;
        break;
      }
    case NOLL_F_MINUS:
      {
        dt->kind = NOLL_DATA_MINUS;
        dt->typ = NOLL_TYP_INT;
        break;
      }
    case NOLL_F_BAG:
      {
        dt->kind = NOLL_DATA_BAG;
        dt->typ = NOLL_TYP_BAGINT;
        break;
      }
    case NOLL_F_BAGUNION:
      {
        dt->kind = NOLL_DATA_BAGUNION;
        dt->typ = NOLL_TYP_BAGINT;
        break;
      }
    case NOLL_F_BAGMINUS:
      {
        dt->kind = NOLL_DATA_BAGMINUS;
        dt->typ = NOLL_TYP_BAGINT;
        break;
      }
    default:
      {
        noll_error (1, "Building data term ", "(bad operator)");
        noll_dterm_free (dt);
        return NULL;
      }
    }
  if (e->size > 0)
    {
      dt->args = noll_dterm_array_new ();
      noll_dterm_array_reserve (dt->args, e->size);
    }
  uint_t i = 0;
  if (dt->kind == NOLL_DATA_ITE)
    {
      noll_dform_t *cond = noll_exp_push_dform (e->args[i], lenv, 1);
      if (cond == NULL)
        {
          noll_error (1, "Building data term ",
                      "(bad bollean condition in ite)");
          noll_dterm_free (dt);
          return NULL;
        }
      dt->p.cond = cond;
      i++;
    }
  for (; i < e->size; i++)
    {
      noll_dterm_t *ti = noll_exp_push_dterm (e->args[i], lenv);
      if (ti == NULL)
        {
          noll_error (1, "Building data term ", "(bad sub-term)");
          noll_dterm_free (dt);
          return NULL;
        }
      if ((dt->kind == NOLL_DATA_ITE) && (i == 1))
        dt->typ = ti->typ;
      if (((dt->kind != NOLL_DATA_BAG) && (dt->kind != NOLL_DATA_FIELD) &&
           ((dt->kind != NOLL_DATA_ITE) || (i > 1)) &&
           (ti->typ != dt->typ)) ||
          ((dt->kind == NOLL_DATA_BAG) && (ti->typ != NOLL_TYP_INT)) ||
          ((dt->kind == NOLL_DATA_FIELD) && (ti->typ != NOLL_TYP_RECORD)))
        {
          noll_error (1, "Building data term ", "(bad type)");
          noll_dterm_free (dt);
          return NULL;
        }
      noll_dterm_array_push (dt->args, ti);
    }
  return dt;
}

/**
 * @brief Translate the SMTLIB AST into the internal data AST.
 * Because the translation is direct, no need to push in a formula.
 */
noll_dform_t *
noll_exp_push_dform (noll_exp_t * e, noll_var_array * lenv, int level)
{
  assert (NULL != e);

  noll_dform_t *df = noll_dform_new ();
  switch (e->discr)
    {
    case NOLL_F_EQ:
      {
        df->kind = NOLL_DATA_EQ;
        break;
      }
    case NOLL_F_DISTINCT:
      {
        df->kind = NOLL_DATA_NEQ;
        break;
      }
    case NOLL_F_LT:
      {
        df->kind = NOLL_DATA_LT;
        break;
      }
    case NOLL_F_GT:
      {
        df->kind = NOLL_DATA_GT;
        break;
      }
    case NOLL_F_LE:
      {
        df->kind = NOLL_DATA_LE;
        break;
      }
    case NOLL_F_GE:
      {
        df->kind = NOLL_DATA_GE;
        break;
      }
    case NOLL_F_SUBSET:
      {
        df->kind = NOLL_DATA_SUBSET;
        break;
      }
    case NOLL_F_IMPLIES:
      {
        if (level != 0)
          {
            noll_error (1, "Building data formula ",
                        "(nesting of implies forbiden)");
            return NULL;
          }
        df->kind = NOLL_DATA_IMPLIES;
        /// it is a binary operator
        noll_dform_t *t1 = noll_exp_push_dform (e->args[0], lenv, 1);
        noll_dform_t *t2 = noll_exp_push_dform (e->args[1], lenv, 1);
        if ((t1 == NULL) || (t2 == NULL))
          {
            noll_error (1, "Building data formula ",
                        "(bad terms for implies)");
            noll_dform_free (df);
            return NULL;
          }
        df->p.bargs = noll_dform_array_new ();
        df->typ = NOLL_TYP_BOOL;
        noll_dform_array_push (df->p.bargs, t1);
        noll_dform_array_push (df->p.bargs, t2);
        return df;

        break;
      }
    default:
      {
        noll_error (1, "Building data formula ", "(bad operator)");
        noll_dform_free (df);
        return NULL;
      }
    }
  /// all data formulas are built from binary operators
  noll_dterm_t *t1 = noll_exp_push_dterm (e->args[0], lenv);
  noll_dterm_t *t2 = noll_exp_push_dterm (e->args[1], lenv);
  if (t1 == NULL || t2 == NULL)
    {
      noll_error (1, "Building data formula ", "(bad terms)");
      noll_dform_free (df);
      return NULL;
    }
  if ((t1->typ != t2->typ) ||
      ((e->discr == NOLL_F_SUBSET) && (t1->typ != NOLL_TYP_BAGINT)))
    {
      noll_error (1, "Building data formula ", "(bad type for terms)");
      noll_dform_free (df);
      return NULL;
    }
  df->p.targs = noll_dterm_array_new ();
  df->typ = NOLL_TYP_BOOL;
  noll_dterm_array_push (df->p.targs, t1);
  noll_dterm_array_push (df->p.targs, t2);
  return df;
}

int
noll_exp_push_pure (noll_form_t * form, noll_pure_t * pure,
                    noll_exp_t * exp, noll_var_array * lenv,
                    const char *msg, const char *ctx)
{
  assert (exp != NULL);

  if ((exp->discr == NOLL_F_EQ) || (exp->discr == NOLL_F_DISTINCT))
    {
      /// the two parameters may be a location variable or a data expression
      /// consider here the location case
      uint_t v1 = UNDEFINED_ID;
      uint_t v2 = UNDEFINED_ID;
      if (exp->args[0]->discr == NOLL_F_LVAR)
        v1 = exp->args[0]->p.sid;
      if (exp->args[1]->discr == NOLL_F_LVAR)
        v2 = exp->args[1]->p.sid;
      if ((v1 != UNDEFINED_ID) && (v2 != UNDEFINED_ID))
        {
          noll_form_kind_t status = NOLL_FORM_SAT;
          if (exp->discr == NOLL_F_EQ)
            status = noll_pure_add_eq (pure, v1, v2);
          else
            status = noll_pure_add_neq (pure, v1, v2);
          if (form != NULL)
            form->kind = status;
          if (status == NOLL_FORM_UNSAT)
            {
              noll_error (1, msg, ctx);
              noll_error (1, "Pure constraint", "(leads to unsat)");
              return 0;
            }
          return 1;
        }
    }
  /// it is a data constraint
  noll_dform_t *df = noll_exp_push_dform (exp, lenv, 0);
  if (df == NULL)
    {
      noll_error (1, msg, ctx);
      noll_error (1, "Pure data constraint", "(bad syntax)");
      return 0;
    }
  return noll_pure_add_dform (pure, df);
}

/**
 * Translates the AST in e to a space formula.
 * @param f the AST of the emp formula
 * @return the space formula or NULL of error
 */
noll_space_t *
noll_mk_form_emp (noll_exp_t * f)
{
  assert (NULL != f);
  noll_space_t *sigma = NULL;
  if (f->discr == NOLL_F_EMP)
    {
      sigma = (noll_space_t *) malloc (sizeof (noll_space_t));
      sigma->kind = NOLL_SPACE_EMP;
      sigma->is_precise = true;
    }
  return sigma;
}

/**
 * Translates the AST in e to a space formula.
 * @param f the AST of the points-to formula
 * @return the space formula or NULL of error
 */
noll_space_t *
noll_mk_form_junk (noll_exp_t * f)
{
  assert (f && f->discr == NOLL_F_JUNK);
  noll_space_t *sigma = (noll_space_t *) malloc (sizeof (noll_space_t));
  sigma->kind = NOLL_SPACE_JUNK;
  sigma->is_precise = (f != NULL) ? false : true;
  return sigma;
}

/**
 * Translates the AST in e to a points-to space formula.
 * @param env  formula containing the environment of variables used
 * @param f the AST of the points-to formula
 * @return the space formula or NULL of error
 */
noll_space_t *
noll_mk_form_pto (noll_context_t * ctx, noll_exp_t * f)
{
  assert (f && f->discr == NOLL_F_PTO && f->size == 2);
  noll_exp_t *v = f->args[0];
  noll_exp_t **fv = NULL;
  uint_t fv_size = 1;
  noll_space_t *sigma = noll_space_new ();
  sigma->kind = NOLL_SPACE_PTO;
  sigma->is_precise = true;
  if (v->discr == NOLL_F_LVAR)
    sigma->m.pto.sid = v->p.sid;
  //is in context
  // fill the set of locations from fv which may be ref or sref
  if (f->args[1]->discr == NOLL_F_REF)
    {
      fv_size = 1;
      fv = &f->args[1];
    }
  else if (f->args[1]->discr == NOLL_F_SREF)
    {
      fv_size = f->args[1]->size;
      fv = f->args[1]->args;
    }
  else
    {
      noll_error (1, "Building points-to formula: bad type for location ",
                  noll_var_name (ctx->lvar_env, v->p.sid, NOLL_TYP_RECORD));
      noll_space_free (sigma);
      return NULL;
    }
  sigma->m.pto.dest = noll_uid_array_new ();
  noll_uid_array_reserve (sigma->m.pto.dest, fv_size);
  sigma->m.pto.fields = noll_uid_array_new ();
  noll_uid_array_reserve (sigma->m.pto.fields, fv_size);
  uint_t i;
  for (i = 0; i < fv_size; i++)
    {
      assert (fv[i]->discr == NOLL_F_REF && fv[i]->size == 2);
      uint_t dest = UNDEFINED_ID;
      if (fv[i]->args[1]->discr == NOLL_F_LVAR)
        dest = fv[i]->args[1]->p.sid;
      else
        {
          noll_error (1,
                      "Building points-to formula: bad destination, not a variable",
                      "");
          noll_space_free (sigma);
          return NULL;
        }
      assert (fv[i]->args[0]->discr == NOLL_F_FIELD);
      uint_t fld = fv[i]->args[0]->p.sid;
      // because the term has been built
      assert (fld != UNDEFINED_ID);
      // notice that we may have dest == UNDEFINED_ID == VNIL_ID
      noll_uid_array_push (sigma->m.pto.dest, dest);
      noll_uid_array_push (sigma->m.pto.fields, fld);
    }
  return sigma;
}

noll_space_t *
noll_mk_form_loop (noll_context_t * ctx, noll_var_array * lenv,
                   const char *name, noll_exp_t * e)
{
  noll_space_t *ret = NULL;
  assert (e && e->discr == NOLL_F_LOOP);
  //there is only one argument
  if (e->size != 1)
    {
      noll_error (1, "Loop expression", "bad number of arguments");
      return ret;
    }
  //generate the argument which shall be a predicate call
  if (e->args[0]->discr != NOLL_F_PRED)
    {
      noll_error (1, "Loop expression", "bad predicate argument");
      return ret;
    }
  ret = noll_mk_form_pred (ctx, lenv, name, e->args[0]);
  if (ret != NULL)
    {
      /* if no error, set loop in the predicate call */
      ret->m.ls.is_loop = true;
    }
  return ret;
}

noll_space_t *
noll_mk_form_pred (noll_context_t * ctx, noll_var_array * lenv,
                   const char *name, noll_exp_t * e)
{
  assert (e && e->discr == NOLL_F_PRED && e->size >= 1);        /// NEW: changed from 2 to 1

  if (ctx != ctx)
    return NULL;                // to remove warning on unused parameter

  /// check the type of actual arguments
  noll_uid_array *actuals = noll_uid_array_new ();
  noll_uid_array_reserve (actuals, e->size);
  noll_type_array *actuals_ty = noll_type_array_new ();
  noll_type_array_reserve (actuals_ty, e->size);
  const char *pname = name;
  uid_t pid = e->p.sid;
  if (pid != UNDEFINED_ID)
    /// it is a call to an already defined predicate, get its name
    pname = noll_pred_name (e->p.sid);
  else
    {
      /// it is a recursive call, so pname not changed but pid is now set
      assert (strcmp (ctx->pname, name) == 0);
      pid = noll_pred_array_find (pname);
    }

  assert (NULL != pname);
  uint_t i;
  for (i = 0; i < e->size; i++)
    {
      if (e->args[i]->discr != NOLL_F_LVAR || e->args[i]->size != 0)
        {
          noll_error (1, "Predicate call to ", pname);
          noll_error (1, "Bad (last) parameters.", "");
          free (actuals);
          free (actuals_ty);
          return NULL;
        }
      uint_t pi = e->args[i]->p.sid;
      noll_uid_array_push (actuals, pi);
      noll_type_array_push (actuals_ty, noll_var_type (lenv, pi));
    }
  pid = noll_pred_typecheck_call (pid, actuals_ty);
  noll_type_array_delete (actuals_ty);
  /// generate the corresponding space formula
  noll_space_t *pcall = noll_space_new ();
  pcall->kind = NOLL_SPACE_LS;
  pcall->is_precise = true;
  pcall->m.ls.pid = pid;
  pcall->m.ls.args = actuals;
  pcall->m.ls.sid = UNDEFINED_ID;
  pcall->m.ls.is_loop = false;
  /// pcall->m.ls.sid is set in INDEX
  return pcall;
}

noll_space_t *
noll_mk_form_index (noll_context_t * ctx, noll_exp_t * e)
{
  noll_space_t *ret = NULL;
  assert (e && e->discr == NOLL_F_INDEX);
  //there are two arguments only
  if (e->size != 2)
    {
      noll_error (1, "Index expression", "bad number of arguments");
      return ret;
    }
  //first argument is a variable, get its id
  uint_t sid = UNDEFINED_ID;
  if (e->args[0]->discr == NOLL_F_SVAR)
    sid = e->args[0]->p.sid;
  if (sid == UNDEFINED_ID)
    {
      noll_error (1, "Index expression", "bad variable argument");
      return ret;
    }
  //generate the second argument which shall be a predicate call
  //with maybe a loop
  if ((e->args[1]->discr != NOLL_F_PRED) &&
      (e->args[1]->discr != NOLL_F_LOOP))
    {
      noll_error (1, "Index expression", "bad predicate argument");
      return ret;
    }
  if (e->args[1]->discr == NOLL_F_PRED)
    ret = noll_mk_form_pred (ctx, ctx->lvar_env, ctx->pname, e->args[1]);
  else
    ret = noll_mk_form_loop (ctx, ctx->lvar_env, NULL, e->args[1]);
  if (ret != NULL)
    {
      /* if no error, bound sid to the predicate call */
      ret->m.ls.sid = sid;
    }
  return ret;
}

noll_space_t *
noll_mk_form_sep (noll_context_t * ctx, noll_exp_t * e)
{
  noll_space_t *ret = NULL;
  assert (e && (e->discr == NOLL_F_SSEP || e->discr == NOLL_F_WSEP));
  //allocate the space formula
  ret = (noll_space_t *) malloc (sizeof (noll_space_t));
  ret->kind = (e->discr == NOLL_F_SSEP) ? NOLL_SPACE_SSEP : NOLL_SPACE_WSEP;
  ret->is_precise = true;
  ret->m.sep = noll_space_array_new ();
  //reserve at least the number of arguments here
  noll_space_array_reserve (ret->m.sep, e->size);
  for (uint_t i = 0; i < e->size; i++)
    {
      noll_space_t *ei = noll_exp_push_space (ctx, e->args[i]);
      if (ei == NULL)
        continue;
      //is_precise attribute is propagated to parents
      if (ei->is_precise == false)
        ret->is_precise = false;
      if (ei->kind == ret->kind)
        {
          //same separation operator, remove the intermediary node
          for (uint_t j = 0; j < noll_vector_size (ei->m.sep); j++)
            {
              noll_space_t *eij = noll_vector_at (ei->m.sep, j);
              noll_space_array_push (ret->m.sep, eij);
              noll_vector_at (ei->m.sep, j) = NULL;
            }
          noll_space_array_delete (ei->m.sep);
          free (ei);
        }
      else
        {
          //different operator, push the formula as arguments
          noll_space_array_push (ret->m.sep, ei);
        }
    }
  return ret;
}

noll_space_t *
noll_exp_push_space (noll_context_t * ctx, noll_exp_t * e)
{
  assert (e);
  noll_space_t *ret = NULL;
  switch (e->discr)
    {
    case NOLL_F_EMP:
      {
        ret = noll_mk_form_emp (e);
        break;
      }
    case NOLL_F_JUNK:
      {
        ret = noll_mk_form_junk (e);
        break;
      }
    case NOLL_F_PTO:
      {
        ret = noll_mk_form_pto (ctx, e);
        break;
      }
    case NOLL_F_PRED:
      {
        ret = noll_mk_form_pred (ctx, ctx->lvar_env, ctx->pname, e);
        break;
      }
    case NOLL_F_INDEX:
      {
        ret = noll_mk_form_index (ctx, e);
        break;
      }
    case NOLL_F_WSEP:
    case NOLL_F_SSEP:
      {
        ret = noll_mk_form_sep (ctx, e);
        break;
      }
    default:
      noll_error (1, "noll_exp_push_space", "not a space formula");
      break;
    }
  return ret;
}

void
noll_exp_push_sterm (noll_exp_t * e, noll_sterm_array * a)
{
  assert (e);
  if (!(e->discr == NOLL_F_SLOC || e->discr == NOLL_F_UNLOC
        || e->discr == NOLL_F_SELOC || e->discr == NOLL_F_SVAR))
    {
      noll_error (1, "noll_exp_push_sterm",
                  "not a term for sets of locations");
      return;
    }
  switch (e->discr)
    {
    case NOLL_F_SLOC:
      {
        assert (e->args[0] && e->args[0]->discr == NOLL_F_LVAR);
        noll_sterm_t *tv = noll_sterm_new_var (e->args[0]->p.sid,
                                               NOLL_STERM_LVAR);
        noll_sterm_array_push (a, tv);
        break;
      }
    case NOLL_F_SVAR:
      {
        noll_sterm_t *tv = noll_sterm_new_var (e->p.sid, NOLL_STERM_SVAR);
        noll_sterm_array_push (a, tv);
        break;
      }
    case NOLL_F_SELOC:
      {
        assert (e->args[0] && e->args[0]->discr == NOLL_F_SVAR);
        assert (e->args[1] && e->args[1]->discr == NOLL_F_LVAR);
        noll_sterm_t *tv = noll_sterm_new_prj (e->args[0]->p.sid,
                                               e->args[1]->p.sid);
        noll_sterm_array_push (a, tv);
        break;
      }
    default:
      //NOLL_F_UNLOC:
      {
        for (uint_t i = 0; i < e->size; i++)
          noll_exp_push_sterm (e->args[i], a);
        break;
      }
    }
}

void
noll_exp_push_share (noll_context_t * ctx, noll_exp_t * e, noll_form_t * form)
{
  assert (e && e->size == 2);
  switch (e->discr)
    {
    case NOLL_F_NILOC:
    case NOLL_F_INLOC:
      {
        noll_atom_share_t *a =
          (noll_atom_share_t *) malloc (sizeof (noll_atom_share_t));
        a->kind = (e->discr == NOLL_F_INLOC) ? NOLL_SHARE_IN : NOLL_SHARE_NI;
        assert (e->args[0]);
        assert (e->args[0]->discr == NOLL_F_LVAR);
        noll_sterm_t *tv = noll_sterm_new_var (e->args[0]->p.sid,
                                               NOLL_STERM_LVAR);
        a->t_left = tv;
        a->t_right = noll_sterm_array_new ();
        noll_exp_push_sterm (e->args[1], a->t_right);
        noll_share_array_push (form->share, a);
        break;
      }
    case NOLL_F_EQLOC:
      {
        //push conjunct for <=
        e->discr = NOLL_F_LELOC;
        noll_exp_push_share (ctx, e, form);
        //push conjunct for >=
        noll_exp_t *tmp = e->args[0];
        e->args[0] = e->args[1];
        e->args[1] = tmp;
        noll_exp_push_share (ctx, e, form);
        //redo the expression
        e->discr = NOLL_F_EQLOC;
        tmp = e->args[0];
        e->args[0] = e->args[1];
        e->args[1] = tmp;
        break;
      }
    case NOLL_F_LELOC:
      {
        noll_sterm_array *left = noll_sterm_array_new ();
        noll_exp_push_sterm (e->args[0], left);
        noll_sterm_array *right = noll_sterm_array_new ();
        noll_exp_push_sterm (e->args[1], right);
        for (uint_t i = 0; i < noll_vector_size (left); i++)
          {
            noll_atom_share_t *a =
              (noll_atom_share_t *) malloc (sizeof (noll_atom_share_t));
            a->kind = NOLL_SHARE_SUBSET;
            a->t_left = noll_vector_at (left, i);
            a->t_right = right;
            noll_share_array_push (form->share, a);
          }
        break;
      }
    default:
      {
        noll_error (1, "noll_exp_push_share", "not a sharing constraint");
        break;
      }
    }
}

void
noll_exp_push_top (noll_context_t * ctx, noll_exp_t * e, noll_form_t * form)
{
  assert (ctx != NULL);
  assert (e != NULL);
  assert (form != NULL);
  if (form->kind == NOLL_FORM_UNSAT)
    return;
  /// copy variables from context to formula
  if (form->lvars != NULL && form->lvars != ctx->lvar_env)
    noll_var_array_delete (form->lvars);
  form->lvars = ctx->lvar_env;
  if (form->svars != NULL && form->svars != ctx->svar_env)
    noll_var_array_delete (form->svars);
  form->svars = ctx->svar_env;
#ifndef NDEBUG
  fprintf (stdout, "\nnoll_exp_push_top:\n\t");
  noll_var_array_fprint (stdout, form->lvars, "lvars");
  fprintf (stdout, "\n\t");
  noll_var_array_fprint (stdout, form->svars, "svars");
  fprintf (stdout, "\n");
#endif
  //fill other parts of the formula
  switch (e->discr)
    {
      /* boolean operations */
    case NOLL_F_TRUE:
      return;                   /* nothing to be done */
    case NOLL_F_FALSE:
      {
        /*
         * set the formula to unsat
         */
        noll_form_set_unsat (form);
        break;
      }
    case NOLL_F_AND:
      {
        for (uint_t i = 0; i < e->size; i++)
          noll_exp_push_top (ctx, e->args[i], form);
        break;
      }
    case NOLL_F_EXISTS:
      {
        //existential variables are already in form->? vars
        for (uint_t i = 0; i < e->size; i++)
          noll_exp_push_top (ctx, e->args[i], form);
        break;
      }
    case NOLL_F_NOT:
    case NOLL_F_OR:
    case NOLL_F_FORALL:
      {
        //this is an error, no translation is possible
        noll_error (0, "noll_exp_push_top", "boolean operation not allowed");
        return;
      }

      /* pure constraints */
    case NOLL_F_EQ:
    case NOLL_F_DISTINCT:
    case NOLL_F_LT:
    case NOLL_F_GT:
    case NOLL_F_LE:
    case NOLL_F_GE:
    case NOLL_F_SUBSET:
    case NOLL_F_IMPLIES:
      {
#ifndef NDEBUG
        fprintf (stdout, "Push pure:");
        noll_exp_printf (stdout, ctx, e);
        fflush (stdout);
#endif
        if (form->pure == NULL)
          form->pure = noll_pure_new (noll_vector_size (form->lvars));
        noll_exp_push_pure (form, form->pure, e, form->lvars,
                            "Translate top formula", "pure part");
        break;
      }
    case NOLL_F_PLUS:
    case NOLL_F_MINUS:
    case NOLL_F_BAG:
    case NOLL_F_EMPTYBAG:
    case NOLL_F_BAGUNION:
    case NOLL_F_BAGMINUS:
      {
        //this is an error, no translation is possible
        noll_error (0, "noll_exp_push_top", "data operation not allowed");
        return;
      }
      /*
       * towards space
       * operations
       */
    case NOLL_F_TOBOOL:
      {
        form->space = noll_exp_push_space (ctx, e->args[0]);
        if (form->kind == NOLL_FORM_VALID && form->space != NULL)
          form->kind = NOLL_FORM_SAT;
        //over - approximate
        break;
      }
      /* share operators */
    case NOLL_F_INLOC:
    case NOLL_F_NILOC:
    case NOLL_F_EQLOC:
    case NOLL_F_LELOC:
      {
        if (!form->share)
          form->share = noll_share_array_new ();
        noll_exp_push_share (ctx, e, form);
        if (form->kind == NOLL_FORM_VALID && form->share != NULL)
          form->kind = NOLL_FORM_SAT;
        //over - approximate
        break;
      }
    case NOLL_F_SELOC:
    case NOLL_F_SLOC:
    case NOLL_F_UNLOC:
      {
        //this is an error, no translation is possible
        noll_error (0, "noll_exp_push_top", "set operation not allowed");
        return;
      }
    default:
      {
        //this is an error, no translation is possible
        noll_error (0, "noll_exp_push_top", "space operation not allowed");
        return;
      }
    }
}

/** Translation form AST to NOLL formula and push into the global formulas.
 */
void
noll_exp_push (noll_context_t * ctx, noll_exp_t * e, int ispos)
{
#ifndef NDEBUG
  //printing now:
  fprintf (stdout, "Push %stive formula:\n", (ispos) ? "posi" : "nega");
  noll_exp_printf (stdout, ctx, e);
  fprintf (stdout, "\nwith context: ");
  noll_var_array_fprint (stdout, ctx->lvar_env, "lvars");
  fflush (stdout);
#endif
  if (!e)
    return;
  noll_form_t *form =
    (ispos == 0) ? noll_entl_get_nform_last () : noll_entl_get_pform ();
  /* if unsat formula, no need to push more formulas */
  if (form->kind == NOLL_FORM_UNSAT)
    return;
  noll_exp_push_top (ctx, e, form);
  return;
}
