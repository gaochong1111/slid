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
 * Predicates for NOLL.
 */

#ifndef _NOLL_PREDS_H_
#define	_NOLL_PREDS_H_

#ifdef	__cplusplus
extern "C"
{
#endif

#include "noll_option.h"
#include "noll_types.h"
#include "noll_vars.h"
#include "noll_form.h"

  /* ====================================================================== */
  /* Datatypes */
  /* ====================================================================== */

  /** Predicate rule
   */
  typedef struct noll_pred_rule_t
  {
    noll_var_array *vars;       // nil + formal arguments + existentially quantified variables
    uint_t fargs;               // limit of formal arguments
    noll_pure_t *pure;          // pure part of the rule (including data)
    noll_space_t *pto;          // points-to part, if any, NULL for base rules
    noll_space_t *nst;          // calls to predicates, non-recursive, NULL for base rule
    noll_space_t *rec;          // recursive calls
  } noll_pred_rule_t;

    NOLL_VECTOR_DECLARE (noll_pred_rule_array, noll_pred_rule_t *);

  /** Predicate definition
   */
  typedef struct noll_pred_binding_t
  {
    size_t pargs;               // type of list = number of arguments of this record type 2 or 4
    noll_var_array *vars;       // nil + formal arguments
    uint_t fargs;               // number of formal arguments in the array above
    noll_pred_rule_array *base_rules;   // set of base rules
    noll_pred_rule_array *rec_rules;    // set of base rules
  } noll_pred_binding_t;

  /** Kind of inductive definition
   *  -- from most specific to more general
   */
  typedef enum 
  {
    NOLL_PRED_LST_PAR,          // list-like definition, with parent
    NOLL_PRED_LST,              // list-like definition, one way
    NOLL_PRED_COMP_PAR,         // compositional definition, with parent
    NOLL_PRED_COMP,             // compositional definition, one way
    NOLL_PRED_WS,               // well structured definition
    NOLL_PRED_LIN,              // linear predicate (single-list, double-list)
    NOLL_PRED_TREE,             // tree predicate
    NOLL_PRED_OTHER             // default
  } noll_pred_kind_e;


  typedef enum
  {
    NOLL_PRED_TREE_NONE_DATA,
    NOLL_PRED_TREE_ONLY_DATA,
    NOLL_PRED_TREE_ONLY_SIZE,
    NOLL_PRED_TREE_GENRAL
  } noll_pred_tree_kind;

  /** Arguments typing infos
   */
  typedef enum
  {
    NOLL_ATYP_LROOT = 0,
    NOLL_ATYP_LPAR,
    NOLL_ATYP_BROOT,
    NOLL_ATYP_IROOT,
    NOLL_ATYP_LPENDING,
    NOLL_ATYP_LLST,
    NOLL_ATYP_BPENDING,
    NOLL_ATYP_IPENDING,
    NOLL_ATYP_BORDER,
    NOLL_ATYP_OTHER
  } noll_atyp_e;

  /** Predicate typing infos
   */
  typedef struct noll_pred_typing_t
  {
    /* typing record for this predicate, index in record_array
     */
    uid_t ptype0;
    /* array of size @global records_array 
     * with 1 for records covered by pred
     */
    noll_uint_array *ptypes;
    /* array of size @global fields_array 
     * with values of @type noll_field_e for each field used in pred
     */
    noll_uint_array *pfields;
    bool isUnaryLoc;            /* the predicate has only source */
    bool useNil;                /* the predicate use fields to nil */
    bool isTwoDir;              /* the predicate is a two direction */
    noll_uid_array *argkind;    /* for each argument, kind of it */

    /* array of size @global preds_array
     * with values 1 for predicates called inside the definition of pred
     */
    noll_uint_array *ppreds;


    noll_pred_kind_e pkind;     /* class of the inductive definition */
    union {
      noll_pred_tree_kind treekind; // the tree predicate type
    }p;
    int nDir; /* number of the location var*/

  } noll_pred_typing_t;

  /** Predicate information:
   * - the name of the predicate
   * - the type(s) of the variable
   */

  typedef struct noll_pred_t
  {
    char *pname;                // declaration name
    uid_t pid;                  // predicate identifier
    noll_pred_binding_t *def;   // predicate definition
    noll_pred_typing_t *typ;    // predicate typing infos
  } noll_pred_t;

  /** Type of the global array of predicates. */
    NOLL_VECTOR_DECLARE (noll_pred_array, noll_pred_t *);

  /* ====================================================================== */
  /* Globals */
  /* ====================================================================== */

  extern noll_pred_array *preds_array;  // predicates

  void noll_pred_init (void);
  /* Initialize global arrays of predicates */

  /* ====================================================================== */
  /* Constructors/Destructors */
  /* ====================================================================== */

  noll_pred_rule_t *noll_pred_rule_new (void);
  /* Allocate a new rule for the predicate and initialize the fields to 0 */

  void noll_pred_rule_delete (noll_pred_rule_t * r);
  /* Free the rule @p r */

  noll_pred_binding_t *noll_pred_binding_new (void);
  /* Allocate a new biding for the predicate and initialize the fields to 0 */

  void noll_pred_binding_delete (noll_pred_binding_t * def);
  /* Free the binding @p def */

  void noll_pred_binding_push_rule (noll_pred_binding_t * def,
                                    noll_pred_rule_t * r, bool isRec);

  /* ====================================================================== */
  /* Other methods */
  /* ====================================================================== */

  uid_t noll_pred_array_find (const char *name);
  /* Returns the id of the predicate in preds_array */

  uid_t noll_pred_register (const char *pname, noll_pred_binding_t * def);
  /* Insert the predicate definition in the global array */

  uid_t noll_pred_typecheck_call (uid_t pid, noll_type_array * actuals_ty);
  /* Typecheck the call of name with the types of @p actuals_ty */

  /**
   * @brief  Returns the predicate with given Predicate ID
   *
   * @param[in]  pid   ID of the desired predicate
   *
   * @returns  The desired predicate
   */
  const noll_pred_t *noll_pred_getpred (uid_t pid);

  const char *noll_pred_name (uid_t pid);

  /**
   * @brief  Returns the 'main' type of the predicate.
   *
   * @param[in]  pid   ID of the desired predicate
   *
   * @returns  The type of the first argument of the predicate
   */
  const noll_type_t *noll_pred_gettype (uid_t pid);

  bool noll_pred_order_lt (uid_t lhs, uid_t rhs);
  /* Total ordering of predicates using their call */

  bool noll_pred_use_nil (uid_t pid);
  /* Return true if pid uses nil internally */

  bool noll_pred_isUnaryLoc (uid_t pid);
  /* Return true if pid has only source in arguments */

  bool noll_pred_is_one_dir (uid_t pid);
  /* Retrun true if pid is a one direction predicate */
  /* WARNING: for the moment, only dll are two direction predicates */

  bool noll_pred_is_field (uid_t pid, uid_t fid, noll_field_e kind);
  /* Search the field in the predicate with a role of at most kind.
   */

  bool noll_pred_is_backbone_field (uid_t fid);
  /* Test if fid is a backbone for some predicate */

  /**
   * @brief  Checks whether the field as the main backbone field of a predicate
   *
   * Checks whether @p fid denoters the main backbone firld of some predicate.
   * That is, the least backbone field (w.r.t. the field ordering) that goes to
   * @p X_tl.
   *
   * @param[in]  fid  The field identifier
   *
   * @returns  @p true iff @p fid denotes the main backbone field of some
   *           predicate, @p false otherwise
   */
  bool noll_pred_is_main_backbone_field (uid_t fid);

  /* Type the predicate definitions.*/
  int noll_pred_type (void);

  /**
   * Alloc the type structure and fill the fields with the default values
   * @param p     predicate
   * @return      1 if ok, 0 otherwise
   */
  int
  noll_pred_type_init (noll_pred_t * p);

  /**
   * @brief  Retrieves the minimum field of a predicate
   *
   * @param[in]  pid  ID of the predicate
   *
   * @returns  The minimum field of the predicate with the ID @p pid
   */
  uid_t noll_pred_get_minfield (uid_t pid);

  /* Order the fields using the predicate order.*/
  int noll_field_order (void);


  /* ====================================================================== */
  /* Related Order Graph functions */
  /* ====================================================================== */


  /* ====================================================================== */
  /* Printing */
  /* ====================================================================== */

  void noll_pred_rule_fprint (FILE * f, noll_pred_rule_t * rule);
  /* Print the rule @p rule. */

  void noll_pred_fprint (FILE * f, uid_t pid);
  /* Print the predicate @p pid. */

  void noll_pred_array_fprint (FILE * f, noll_pred_array * a,
                               const char *msg);
  /* Print the array a. */


#ifdef	__cplusplus
}
#endif

#endif                          /* _NOLL_PREDS_H_ */
