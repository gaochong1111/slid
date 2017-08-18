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
 * Abstract Syntax Tree of NOLL formulas.
 */

#ifndef _NOLL_FORM_H_
#define	_NOLL_FORM_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>
#include <stdio.h>
#include "noll_vars.h"
#include "noll_types.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Theory of formulas.
 */
  typedef enum noll_logic_t
  {
    NOLL_LOGIC_NOLL,            /* ESOP'13 */
    NOLL_LOGIC_SLL,             /* APLAS'14 */
    NOLL_LOGIC_SLRD,            /* SLCOMP'14 */
    NOLL_LOGIC_SLRDI,
    NOLL_LOGIC_OTHER            /* NOT SUPPORTED */
  } noll_logic_t;

/** Data formulas.
 *  Encoded by smtlib expressions in noll.h
 */
  typedef enum noll_data_op_t
  {
    NOLL_DATA_EQ = 0,
    NOLL_DATA_LT,
    NOLL_DATA_GT,
    NOLL_DATA_LE,
    NOLL_DATA_GE,
    NOLL_DATA_NEQ,
    NOLL_DATA_PLUS,
    NOLL_DATA_MINUS,
    NOLL_DATA_ITE,
    NOLL_DATA_INT,
    NOLL_DATA_RAT,
    NOLL_DATA_VAR,
    NOLL_DATA_EMPTYBAG,
    NOLL_DATA_FIELD,
    NOLL_DATA_BAG,
    NOLL_DATA_BAGUNION,
    NOLL_DATA_BAGMINUS,
    NOLL_DATA_SUBSET,
    NOLL_DATA_IMPLIES,
    NOLL_DATA_OTHER             /* NOT TO BE USED */
  } noll_data_op_t;

  typedef struct noll_dterm_s noll_dterm_t;     /* forward definition */
    NOLL_VECTOR_DECLARE (noll_dterm_array, noll_dterm_t *);

  typedef struct noll_dform_s noll_dform_t;     /* forward definition */
    NOLL_VECTOR_DECLARE (noll_dform_array, noll_dform_t *);

  struct noll_dterm_s
  {
    noll_data_op_t kind;        // only data terms
    noll_typ_t typ;             // either NOLL_TYP_INT or NOLL_TYP_BAGINT

    union
    {
      long value;               // integer constant
      uid_t sid;                // symbol (variable or field) identifier
      noll_dform_t *cond;       // simple condition for ite
    } p;

    noll_dterm_array *args;     // NULL for 0-arity terms
  };


  struct noll_dform_s
  {
    noll_data_op_t kind;        // only data formulas
    noll_typ_t typ;             // either NOLL_TYP_INT or NOLL_TYP_BAGINT

    union
    {
      noll_dterm_array *targs;  // term arguments
      noll_dform_array *bargs;  // boolean arguments iff kind == NOLL_DATA_IMPLIES
    } p;
  };


/** Pure formulas.
 *  Encoded as an upper diagonal matrix of size = nb location variables:
 *  for (v1(id) < v2(id))
 *    m[v1][v2] = NOLL_PURE_EQ if v1=v2,
 *                NOLL_PURE_NEQ if v1!=v2,
 *                NOLL_PURE_OTHER (-1) if unknown
 */
  typedef enum noll_pure_op_t
  {
    NOLL_PURE_EQ = 0, NOLL_PURE_NEQ, NOLL_PURE_OTHER
  } noll_pure_op_t;

  typedef struct noll_pure_t
  {
    noll_pure_op_t **m;         // matrix of equality and inequality constraints
    uint_t size;                // allocated size for the matrix, 0 if empty or == locs_array size
    noll_dform_array *data;     // set (conjunction of) pure constraints on data
  } noll_pure_t;

/**
 * For variable i <= j, the matrix p->m stores an array of size-i cells!
 */
#define noll_pure_matrix_at(p,i,j) p->m[i][j-i]

/**
 * Spatial formulas.
 */

  typedef struct noll_space_s noll_space_t;     /* forward definition */
    NOLL_VECTOR_DECLARE (noll_space_array, noll_space_t *);

  typedef enum noll_space_op_t
  {
    NOLL_SPACE_EMP = 0,
    NOLL_SPACE_JUNK,
    NOLL_SPACE_PTO,
    NOLL_SPACE_LS,
    NOLL_SPACE_WSEP,
    NOLL_SPACE_SSEP,
    NOLL_SPACE_OTHER
/* NOT TO BE USED */
  } noll_space_op_t;

// points-to constraint

  typedef struct noll_pto_t
  {
    uid_t sid;                  // source location
    noll_uid_array *fields;     // array of fields
    noll_uid_array *dest;       // array of destination locations
  } noll_pto_t;

// list segment constraint

  typedef struct noll_ls_t
  {
    uid_t pid;                  // predicate
    noll_uid_array *args;       // arguments used
    uid_t sid;                  // set of locations variable bound
    bool is_loop;               // set if it is a loop instance
  } noll_ls_t;

  struct noll_space_s
  {
    noll_space_op_t kind;
    bool is_precise;

    union
    {
      noll_pto_t pto;           // points-to constraint
      noll_ls_t ls;             // list segment constraint
      noll_space_array *sep;    // array of constraints
      // for weak or strong separation
    } m;
  };

/** Sharing formulas.
 */
  typedef enum noll_share_op_t
  {
    NOLL_SHARE_IN = 0,          /* \in */
    NOLL_SHARE_NI,              /* \not\in */
    NOLL_SHARE_SUBSET,          /* \subseteq */
    NOLL_SHARE_OTHER
/* NOT TO BE USED */
  } noll_share_op_t;

  typedef enum noll_sterm_kind_t
  {
    NOLL_STERM_LVAR = 0, NOLL_STERM_SVAR, NOLL_STERM_PRJ, NOLL_STERM_OTHER
/* NOT TO BE USED */
  } noll_sterm_kind_t;

/**
 * Type for set of location terms.
 * Warning: because smtlib does not allow to use type names,
 * we use a location variable to obtain the type on which the projection
 * of the set of location variables shall be done.
 */
  typedef struct noll_sterm_t
  {
    noll_sterm_kind_t kind;
    uid_t lvar;                 // location variable, UNDEFINED_ID if kind == NOLL_STERM_SVAR
    uid_t svar;                 // set of locations variable, UNDEFINED_ID if kind == NOLL_STERM_LVAR
  } noll_sterm_t;

    NOLL_VECTOR_DECLARE (noll_sterm_array, noll_sterm_t *);

/**
 * Type for sharing constraints.
 * Normal form used: term op (union of terms)
 */
  typedef struct noll_atom_share_t
  {
    noll_share_op_t kind;       // kind of constraint
    noll_sterm_t *t_left;       // term left
    noll_sterm_array *t_right;  // term right = union of terms
  } noll_atom_share_t;

    NOLL_VECTOR_DECLARE (noll_share_array, noll_atom_share_t *);

  typedef enum noll_form_kind_t
  {
    NOLL_FORM_UNSAT = 0, NOLL_FORM_SAT, NOLL_FORM_VALID, NOLL_FORM_OTHER
/* NOT TO BE USED */
  } noll_form_kind_t;

/** Formula in NOLL */
  typedef struct noll_form_t
  {
    noll_form_kind_t kind;      // kind of formula
    noll_var_array *lvars;      // local variables
    noll_var_array *svars;
    noll_pure_t *pure;          // pure part
    noll_space_t *space;        // space part
    noll_share_array *share;    // sharing part
  } noll_form_t;

    NOLL_VECTOR_DECLARE (noll_form_array, noll_form_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

  extern noll_logic_t noll_form_logic;

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

  noll_form_t *noll_form_new (void);
  noll_pure_t *noll_pure_new (uint_t size);
  noll_space_t *noll_space_new (void);
  noll_share_array *noll_share_new (void);
  noll_sterm_t *noll_sterm_new_var (uid_t v, noll_sterm_kind_t kind);
  noll_sterm_t *noll_sterm_new_prj (uid_t s, uid_t v);

  noll_dterm_t *noll_dterm_new (void);
  noll_dterm_t *noll_dterm_new_var (uint_t vid, noll_typ_t ty);
  noll_dform_t *noll_dform_new (void);
  noll_dform_t *noll_dform_new_eq (noll_dterm_t * t1, noll_dterm_t * t2);

/* Allocation */

  void noll_form_free (noll_form_t * f);
  void noll_form_set_unsat (noll_form_t * f);
  void noll_dterm_free (noll_dterm_t * t);
  void noll_dform_free (noll_dform_t * d);
  void noll_pure_free (noll_pure_t * p);
  void noll_space_free (noll_space_t * s);
  void noll_share_free (noll_share_array * s);
/* Deallocation */

  noll_sterm_t *noll_sterm_copy (noll_sterm_t * a);
/* Copy */
  noll_space_t *noll_space_sub (noll_space_t * a, noll_uid_array * sub);
/* Apply variable substitution and provide a copy */

  int noll_pure_add_dform (noll_pure_t * form, noll_dform_t * df);
  noll_form_kind_t noll_pure_add_eq (noll_pure_t * form, uid_t v1, uid_t v2);
  noll_form_kind_t noll_pure_add_neq (noll_pure_t * form, uid_t v1, uid_t v2);
  void noll_form_add_eq (noll_form_t * form, uid_t v1, uid_t v2);
  void noll_form_add_neq (noll_form_t * form, uid_t v1, uid_t v2);
/* Add equality/inequality pure formula */

/* ====================================================================== */
/* Typing */
/* ====================================================================== */

  int noll_form_type (noll_form_t * form);
  /* Type the formula */

/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

  int noll_form_is_unsat (noll_form_t * phi);
  int noll_form_is_sat (noll_form_t * phi);
  int noll_form_is_valid (noll_form_t * phi);

  int noll_form_array_is_unsat (noll_form_array * phi1_phiN);
/* All formulae shall be unsat */
  int noll_form_array_is_valid (noll_form_array * phi1_phiN);
/* One formula shall be valid */

/* ====================================================================== */
/* Composition/Reduction */
/* ====================================================================== */

  void noll_dform_array_cup_all (noll_dform_array * dst,
                                 noll_dform_array * src);
  /* Do the union between @p dst and @p src in @p dst */

  noll_dterm_t *noll_dterm_apply (noll_dterm_t * dt, noll_uid_array * m);
  noll_dform_t *noll_dform_apply (noll_dform_t * df, noll_uid_array * m);
  noll_dform_array *noll_dform_array_apply (noll_dform_array * df,
                                            noll_uid_array * m);
  /* Apply the substitution @p m on @p df and generate new formulas */
  noll_dform_array *noll_dform_array_compose (noll_uid_array * mg2,
                                              noll_dform_array * f1,
                                              noll_dform_array * df2);

/* ====================================================================== */
/* Solvers */
/* ====================================================================== */

  int noll_pure_check_entl (bool ** diff, uint_t dsize, noll_pure_t * f,
                            noll_uid_array * args,
                            noll_var_array * lv, noll_uid_array * map,
                            noll_dform_array * df);
/* Check that @p diff entails @p ops[@p map] */

  int noll_dform_array_check_entl (noll_var_array * lv1,
                                   noll_dform_array * df1,
                                   noll_var_array * lv2, noll_uid_array * m,
                                   noll_dform_array * df2);
/* Check that constraints on data variables from @p df1 entail @p df2 */

/* ====================================================================== */
/* Printing */
/* ====================================================================== */


  void noll_pure_fprint (FILE * f, noll_var_array * lvars, noll_pure_t * phi);

  void noll_dform_fprint (FILE * f, noll_var_array * lvars,
                          noll_dform_t * phi);
  void noll_dform_array_fprint (FILE * f, noll_var_array * lvars,
                                noll_dform_array * phi);

  void noll_share_atom_fprint (FILE * f, noll_var_array * lvars,
                               noll_var_array * svars,
                               noll_atom_share_t * phi);
  void noll_share_fprint (FILE * f, noll_var_array * lvars,
                          noll_var_array * svars, noll_share_array * phi);
  void noll_space_fprint (FILE * f, noll_var_array * lvars,
                          noll_var_array * svars, noll_space_t * phi);
  void noll_form_fprint (FILE * f, noll_form_t * phi);

#ifdef	__cplusplus
}
#endif

#endif                          /* _NOLL_FORMULA_H_ */
