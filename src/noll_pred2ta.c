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

/**
 * Defines translation between heap graph to tree automata.
 * Special cases are dealt here, @see noll_pred2ta_gen.c for 
 * the general case.
 */

#include "noll.h"
#include "libvata_noll_iface.h"
#include "noll_pred2ta.h"



NOLL_VECTOR_DEFINE (noll_tree_array, noll_tree_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_tree_array *pred2tree_array = NULL;

void
noll_pred2tree_init ()
{
  pred2tree_array = noll_tree_array_new ();
  noll_tree_array_resize (pred2tree_array, noll_vector_size (preds_array));
}

noll_graph_array *pred2graph_array = NULL;

void
noll_pred2graph_init ()
{
  pred2graph_array = noll_graph_array_new ();
  noll_graph_array_resize (pred2graph_array, noll_vector_size (preds_array));
}

/* ====================================================================== */
/* Markings */
/* ====================================================================== */

void
noll_marking_push (noll_uid_array * mark, uid_t fid)
{
  assert (NULL != mark);

  if ((noll_vector_size (mark) == 0) || (noll_vector_last (mark) != fid))
    noll_uid_array_push (mark, fid);
  /* else nothing */
  return;
}

/* ====================================================================== */
/* Edge translators */
/* ====================================================================== */

/**
 * Add to the @p ta the transitions encoding the ls predicate,
 * starting from state @p qinit, labeling the first state by @p vars_in,
 * ending in @p vars_out, and marking the first state by @p mark_in.
 *
 * @param ta       the TA to which transitions are added
 * @param pred     the predicate generated
 * @param fid      the field to be used as selector
 * @param qinit    the initial state to which transitions are added
 * @param vars_in  labeling of initial state
 * @param mark_in  marking of the initial state
 * @param out_symbol   symbol for the output transition
 * @return         the number of the last state generated for @p ta
 */
uint_t
noll_pred2ta_ls (noll_ta_t * ta,
                 const noll_pred_t * pred,
                 uid_t fid,
                 uint_t qinit,
                 const noll_uid_array * vars_in,
                 const noll_uid_array * mark_in,
                 const noll_ta_symbol_t * out_symbol)
{

  NOLL_DEBUG ("WARNING: Generating a nested TA for the predicate ls\n");

  assert (NULL != ta);
  assert (NULL != mark_in);     // at least eps
  assert (NULL != out_symbol);

  uint_t q = qinit;

  /* the selectors */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, fid);

  /* the marking used mark_in_fld = mark_in . fld */
  noll_uid_array *mark_in_fld = noll_uid_array_new ();
  assert (NULL != mark_in_fld);
  noll_uid_array_copy (mark_in_fld, mark_in);
  noll_marking_push (mark_in_fld, fid);

  q = q + 1;                    /* next state is qinit + 1 */
  noll_uid_array *children = noll_uid_array_new ();
  noll_uid_array_push (children, q);

  /*
   * Transition: q1 -> [<fid>, {in}, mark_in](q2)
   *       -- one cell
   */
  const noll_ta_symbol_t *symbol_next1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_next1);
  vata_add_transition (ta, qinit, symbol_next1, children);

  /*
   * Transition: q1 -> [<ls>, {in}, mark_in](q2)
   *       -- one list segment
   */
  const noll_ta_symbol_t *symbol_lso1 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_in);
  assert (NULL != symbol_lso1);
  vata_add_transition (ta, qinit, symbol_lso1, children);

  /*
   * Transition: q2 -> [<fid>, {}, mark_in_fld](q2)
   *       -- one list segment
   */
  const noll_ta_symbol_t *symbol_next2 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_fld);
  assert (NULL != symbol_next2);
  vata_add_transition (ta, q, symbol_next2, children);

  /*
   * Transition: q2 -> [<ls>, {}, mark_in_fld](q2)
   *       -- one list segment
   */
  const noll_ta_symbol_t *symbol_lso2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_fld);
  assert (NULL != symbol_lso2);
  vata_add_transition (ta, q, symbol_lso2, children);

  /*
   * Transition: q2 -> [, {out}, ]()
   *       -- one list segment
   */
  vata_add_transition (ta, q, out_symbol, NULL);

  noll_uid_array_delete (mark_in_fld);
  noll_uid_array_delete (children);
  noll_uid_array_delete (selectors);

  return q;
}


/**
 * Get the TA for the edge built with predicate 'ls'
 * by instantiating the definition of the
 * 'lso(in, out)' predicate (see ../samples/ls/ls-vc01.smt)
 *
 * lso(in, out) = (in = out) or
 *                (in != out and
 *                 exists u . in -> {(f, u)} * lso(u, out))
 *
 * to the TA (q1 is a root state):
 *  q1 -> [f, in, m(f)](q2)
 *  q1 -> [lso, in, m(f)](q2)
 *  q2 -> [f, m(f)](q2)
 *  q2 -> [lso, m(f)](q2)
 *  q2 -> [out]
 *
 * @param edge   An edge using the 'lso' predicate
 * @return       The TA recognizing unfolding of this edge
 */
noll_ta_t *
noll_edge2ta_ls (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  NOLL_DEBUG ("WARNING: Generating a fixed TA for the predicate lso\n");

  // get infos about the predicate
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the unique field for the lso predicate */
  uid_t next_uid = UNDEFINED_ID;
  assert (NULL != pred->typ);
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    if (noll_vector_at (pred->typ->pfields, fid) == 1)
      {
        assert (next_uid == UNDEFINED_ID);
        next_uid = fid;
      }
  assert (UNDEFINED_ID != next_uid);

  /* build the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  vata_set_state_root (ta, 1);

  /* identifiers for arguments */
  uid_t initial_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);

  /* label of in variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, initial_node);

  /* empty marking for first state, mark_eps = [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  const noll_ta_symbol_t *end_symbol =
    noll_ta_symbol_get_unique_aliased_var (end_node);
  assert (NULL != end_symbol);
  noll_pred2ta_ls (ta, pred, next_uid, 1, vars_in, mark_eps, end_symbol);

  noll_uid_array_delete (mark_eps);
  noll_uid_array_delete (vars_in);

  return ta;
}


/**
 * Get the TA for the edge built with predicate 'lss'
 * by instantiating the definition of the
 * 'lsso(in, out)' predicate (see ../samples/lss/lss-vc01.smt)
 *
 * lsso(in, out) = (in = out) or
 *                 (in != out and
 *                 exists u . in -> {(f1, u), (f2, u)} * lsso(u, out))
 *
 * to the TA (q1 is a root state):
 *  q1 -> [<f1,f2>, in, m(f)](q2,q3)
 *  q1 -> [<f1,f2>, in, m(f)](qout,qout)
 *  q1 -> [lsso, in, m(f)](q2)
 *  q1 -> [lsso, in, m(f)](qout)
 *  q2 -> [<f1,f2>, m(f)](q2,q3)
 *  q2 -> [<f1,f2>, m(f)](qout,qout)
 *  q2 -> [lsso, m(f)](q2)
 *  q2 -> [lsso, m(f)](qout)
 *  qout -> [out]
 *  q3 -> [alias^v(f1)]
 *
 * @param edge   An edge using the 'lsso' predicate
 * @return       The TA recognizing unfolding of this edge
 */
noll_ta_t *
noll_edge2ta_lss (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  NOLL_DEBUG ("WARNING: Generating a fixed TA for the predicate lsso\n");

  // get infos about the predicate
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the fields for the lsso predicate */
  uid_t next1_uid = UNDEFINED_ID;
  uid_t next2_uid = UNDEFINED_ID;
  assert (NULL != pred->typ);
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    if (noll_pred_is_field (pid, fid, NOLL_PFLD_BCKBONE))
      {
        if (next1_uid == UNDEFINED_ID)
          next1_uid = fid;
        else if (next2_uid == UNDEFINED_ID)
          next2_uid = fid;
        else
          assert (false);
      }
  assert (UNDEFINED_ID != next1_uid);
  assert (UNDEFINED_ID != next2_uid);
  // this translation works only for the lsso predicate where
  // next1 < next2
  if (noll_field_lt (next2_uid, next1_uid))
    {
      // swap fields
      uid_t tmp_uid = next2_uid;
      next2_uid = next1_uid;
      next1_uid = tmp_uid;
    }
  noll_field_t *next1_fld = noll_vector_at (fields_array, next1_uid);
  noll_field_t *next2_fld = noll_vector_at (fields_array, next2_uid);

  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }

  /* the set of selectors */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, next1_uid);
  noll_uid_array_push (selectors, next2_uid);

  /* generic set of variables */
  noll_uid_array *vars1 = noll_uid_array_new ();

  /* identifiers for arguments */
  uid_t initial_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);

  /* fill the set of vars markings */
  assert (NULL != vars1);
  noll_uid_array_push (vars1, initial_node);

  /* the marking [eps] */
  noll_uid_array *marking1 = noll_uid_array_new ();
  assert (NULL != marking1);
  noll_uid_array_push (marking1, NOLL_MARKINGS_EPSILON);

  /*  symbol [f1.eps]] */
  noll_uid_array *marking2 = noll_uid_array_new ();
  assert (NULL != marking2);
  noll_uid_array_copy (marking2, marking1);
  noll_uid_array_push (marking2, next1_uid);

  /* build the TA */
  vata_set_state_root (ta, 1);

  /* q1 -> [<f1, f2> [in, eps]] (q2,q3) */
  const noll_ta_symbol_t *symbol_alloc1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars1, marking1);
  assert (NULL != symbol_alloc1);
  noll_uid_array *children1next = noll_uid_array_new ();
  noll_uid_array_push (children1next, 2);
  noll_uid_array_push (children1next, 3);
  vata_add_transition (ta, 1, symbol_alloc1, children1next);
  noll_uid_array_delete (children1next);

  /* q1 -> [<f1,f2>, [in, eps]](qout,qout) */
  children1next = noll_uid_array_new ();
  noll_uid_array_push (children1next, 4);
  noll_uid_array_push (children1next, 4);
  vata_add_transition (ta, 1, symbol_alloc1, children1next);
  noll_uid_array_delete (children1next);

  /* q1 -> [<lsso>, [in, eps]] (q2) */
  const noll_ta_symbol_t *symbol_lsso1 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars1, marking1);
  assert (NULL != symbol_lsso1);
  noll_uid_array *children1lsso = noll_uid_array_new ();
  noll_uid_array_push (children1lsso, 2);
  vata_add_transition (ta, 1, symbol_lsso1, children1lsso);
  noll_uid_array_delete (children1lsso);

  /* q1 -> [<lsso, [in, eps]](qout) */
  children1lsso = noll_uid_array_new ();
  noll_uid_array_push (children1lsso, 4);
  vata_add_transition (ta, 1, symbol_lsso1, children1lsso);
  noll_uid_array_delete (children1lsso);

  /* q2 -> [<f1, f2> ,[[], f1.eps]] (q2,q3) */
  const noll_ta_symbol_t *symbol_alloc2 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, marking2);
  assert (NULL != symbol_alloc2);
  noll_uid_array *children2next = noll_uid_array_new ();
  noll_uid_array_push (children2next, 2);
  noll_uid_array_push (children2next, 3);
  vata_add_transition (ta, 2, symbol_alloc2, children2next);
  noll_uid_array_delete (children2next);

  /* q2 -> [<f1,f2>, [[], f1.eps]]](qout,qout) */
  children2next = noll_uid_array_new ();
  noll_uid_array_push (children2next, 4);
  noll_uid_array_push (children2next, 4);
  vata_add_transition (ta, 2, symbol_alloc2, children2next);
  noll_uid_array_delete (children2next);

  /* q2 -> [<lsso>, [[], f1.eps]]] (q2) */
  const noll_ta_symbol_t *symbol_lsso2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, marking2);
  assert (NULL != symbol_lsso2);
  noll_uid_array *children2lsso = noll_uid_array_new ();
  noll_uid_array_push (children2lsso, 2);
  vata_add_transition (ta, 2, symbol_lsso2, children2lsso);
  noll_uid_array_delete (children2lsso);

  /* q2 -> [<lsso>, [[], f1.eps]]] (qout) */
  children2lsso = noll_uid_array_new ();
  noll_uid_array_push (children2lsso, 4);
  vata_add_transition (ta, 2, symbol_lsso2, children2lsso);
  noll_uid_array_delete (children2lsso);

  /* q3 -> [alias^v(next1)] */
  const noll_ta_symbol_t *symbol_ref =
    noll_ta_symbol_get_unique_aliased_marking_up_down_fst (marking2);
  assert (NULL != symbol_ref);
  vata_add_transition (ta, 3, symbol_ref, NULL);

  /* q4 -> [out] */
  const noll_ta_symbol_t *symbol_end =
    noll_ta_symbol_get_unique_aliased_var (end_node);
  assert (NULL != symbol_end);
  vata_add_transition (ta, 4, symbol_end, NULL);

  noll_uid_array_delete (marking1);
  noll_uid_array_delete (marking2);
  noll_uid_array_delete (vars1);
  noll_uid_array_delete (selectors);

  return ta;
}

/**
 * Get the TA for the edge built with predicate 'dll'
 * by instantiating the definition of the
 * 'dll(in, out, prv, flw)' predicate (see ../samples/dll/dll-vc01.smt)
 *
 * dll(in,out,pv,fw) = ((in = fw) and (out=pv)) or
 *                 (in != fw and out != pv and
 *                 exists u. in -> {(next, u),(prev, pv)} * dll(u,out,in,fw))
 *
 * (Notice: both int and out are 'allocated' on the list segment!)
 *
 * to the TA (q1 is a root state):
 *
 *  -- only simple fields --
 *  q1 -> [<next,prev>, {in,out}, eps](q4,q5)
 *        -- one cell list
 *  q1 -> [<next,prev>, {in}, eps](q2,q5)
 *        -- at least two cell list
 *  q2 -> [<next,prev>, {out}, m(next)](q4,q6)
 *        -- exactly two cells
 *  q2 -> [<next,prev>, , m(next)](q3,q6)
 *        -- more than two cells
 *  q2 -> [<dll>, , m(next)](q8,q6)
 *        -- more than two cells
 *  q3 -> [<next,prev>, , m(next)](q3,q7)
 *        -- inner cells after two
 *  q3 -> [<next,prev>, {out}, m(next)](q4,q7)
 *        -- end cell after two
 *  q4 -> [,{fw},]()
 *        -- ref to foward var
 *  q5 -> [,{pv},]()
 *        -- ref to prev var
 *  q6 -> [,{in},]()
 *        -- ref to the input of the list
 *  q7 -> [,s2(m(next)),]()
 *        -- ref to the previous inside the list
 *
 *  -- only predicate segments --
 *  q1 -> [<dll>, {in}, eps](q8,q5)
 *        -- one list segment from in location
 *  q8 -> [<next>, {out}, m(next)](q4)
 *        -- end of list segment dll
 *  q8 -> [<next>, , m(next)](q3)
 *        -- link by next to another dll cell
 *  q3 -> [<dll>, , m(next)](q8,q7)
 *
 *
 * @param edge   An edge using the 'dll' predicate
 * @return       The TA recognizing unfolding of this edge
 */
noll_ta_t *
noll_edge2ta_dll (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  NOLL_DEBUG ("WARNING: Generating a fixed TA for the predicate dll\n");

  // get infos about the predicate
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the fields for the dll predicate */
  uid_t next_uid = UNDEFINED_ID;
  uid_t prev_uid = UNDEFINED_ID;
  assert (NULL != pred->typ);
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    if (noll_pred_is_field (pid, fid, NOLL_PFLD_BCKBONE) &&
        (next_uid == UNDEFINED_ID))
      next_uid = fid;
    else if (noll_pred_is_field (pid, fid, NOLL_PFLD_BORDER) &&
             (prev_uid == UNDEFINED_ID))
      prev_uid = fid;
    else
      assert (false);
  assert (UNDEFINED_ID != next_uid);
  assert (UNDEFINED_ID != prev_uid);
  assert (noll_field_lt (next_uid, prev_uid));

  /* identifiers for arguments */
  uid_t in_node = noll_vector_at (edge->args, 0);
  uid_t out_node = noll_vector_at (edge->args, 1);
  uid_t pv_node = noll_vector_at (edge->args, 2);
  uid_t fw_node = noll_vector_at (edge->args, 3);

  /* Start building the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }

  /*
   * Components of TA symbols
   */
  /* the list of fields */
  noll_uid_array *sel_next = noll_uid_array_new ();
  assert (NULL != sel_next);
  noll_uid_array_push (sel_next, next_uid);

  noll_uid_array *sel_prev = noll_uid_array_new ();
  assert (NULL != sel_prev);
  noll_uid_array_push (sel_prev, prev_uid);

  noll_uid_array *sel_next_prev = noll_uid_array_new ();
  assert (NULL != sel_next_prev);
  noll_uid_array_push (sel_next_prev, next_uid);
  noll_uid_array_push (sel_next_prev, prev_uid);

  /* sets of variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, in_node);

  noll_uid_array *vars_out = noll_uid_array_new ();
  assert (NULL != vars_out);
  noll_uid_array_push (vars_out, out_node);

  noll_uid_array *vars_in_out = noll_uid_array_new ();
  assert (NULL != vars_in_out);
  noll_uid_array_push (vars_in_out, in_node);
  noll_uid_array_push (vars_in_out, out_node);

  /* the marking [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  /* the marking m(next)=[eps, next] */
  noll_uid_array *mark_next = noll_uid_array_new ();
  assert (NULL != mark_next);
  noll_uid_array_copy (mark_next, mark_eps);
  noll_marking_push (mark_next, next_uid);

  /* build the TA */
  vata_set_state_root (ta, 1);

  /*
   * Transition: q1 -> [<next,prev>, {in,out}, eps](q4,q5)
   *        -- one cell list
   */
  const noll_ta_symbol_t *symbol_q1_1 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_in_out,
                                         mark_eps);
  assert (NULL != symbol_q1_1);
  noll_uid_array *succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 4);
  noll_uid_array_push (succ_q1, 5);
  vata_add_transition (ta, 1, symbol_q1_1, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [<next,prev>, {in}, eps](q2,q5)
   *        -- at least two cell list
   */
  const noll_ta_symbol_t *symbol_q1_2 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_in, mark_eps);
  assert (NULL != symbol_q1_2);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 2);
  noll_uid_array_push (succ_q1, 5);
  vata_add_transition (ta, 1, symbol_q1_2, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [<dll>, {in}, eps](q8,q5)
   *        -- one list segment from in location
   */
  const noll_ta_symbol_t *symbol_q1_3 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_eps);
  assert (NULL != symbol_q1_3);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, 8);
  noll_uid_array_push (succ_q1, 5);
  vata_add_transition (ta, 1, symbol_q1_3, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q2 -> [<next,prev>, {out}, m(next)](q4,q6)
   *        -- exactly two cells
   */
  const noll_ta_symbol_t *symbol_q2_1 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_out, mark_next);
  assert (NULL != symbol_q2_1);
  noll_uid_array *succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, 4);
  noll_uid_array_push (succ_q2, 6);
  vata_add_transition (ta, 2, symbol_q2_1, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [<next,prev>, , m(next)](q3,q6)
   *         -- more than two cells
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, NULL, mark_next);
  assert (NULL != symbol_q2_2);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, 3);
  noll_uid_array_push (succ_q2, 6);
  vata_add_transition (ta, 2, symbol_q2_2, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [<dll>, , m(next)](q8,q6)
   *        -- more than two cells
   */
  const noll_ta_symbol_t *symbol_q2_p =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_next);
  assert (NULL != symbol_q2_p);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, 8);
  noll_uid_array_push (succ_q2, 6);
  vata_add_transition (ta, 2, symbol_q2_p, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q3 -> [<next,prev>, , m(next)](q3,q7)
   *        -- inner cells after two
   */
  const noll_ta_symbol_t *symbol_q3_1 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, NULL, mark_next);
  assert (NULL != symbol_q3_1);
  noll_uid_array *succ_q3 = noll_uid_array_new ();
  noll_uid_array_push (succ_q3, 3);
  noll_uid_array_push (succ_q3, 7);
  vata_add_transition (ta, 3, symbol_q3_1, succ_q3);
  noll_uid_array_delete (succ_q3);

  /*
   * Transition: q3 -> [<next,prev>, {out}, m(next)](q4,q7)
   *        -- end cell after two
   */
  const noll_ta_symbol_t *symbol_q3_2 =
    noll_ta_symbol_get_unique_allocated (sel_next_prev, vars_out, mark_next);
  assert (NULL != symbol_q3_2);
  succ_q3 = noll_uid_array_new ();
  noll_uid_array_push (succ_q3, 4);
  noll_uid_array_push (succ_q3, 7);
  vata_add_transition (ta, 3, symbol_q3_2, succ_q3);
  noll_uid_array_delete (succ_q3);

  /*
   * Transition: q3 -> [<dll>, , m(next)](q8,q7)
   *        -- start a list segment
   */
  const noll_ta_symbol_t *symbol_q3_3 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_next);
  assert (NULL != symbol_q3_3);
  succ_q3 = noll_uid_array_new ();
  noll_uid_array_push (succ_q3, 8);
  noll_uid_array_push (succ_q3, 7);
  vata_add_transition (ta, 3, symbol_q3_3, succ_q3);
  noll_uid_array_delete (succ_q3);

  /*
   * Transition: q4 -> [,{fw},]()
   *        -- ref to forward var
   */
  const noll_ta_symbol_t *symbol_q4 =
    noll_ta_symbol_get_unique_aliased_var (fw_node);
  assert (NULL != symbol_q4);
  noll_uid_array *succ_empty = noll_uid_array_new ();
  vata_add_transition (ta, 4, symbol_q4, succ_empty);

  /*
   * Transition: q5 -> [,{pv},]()
   *        -- ref to prev var
   */
  const noll_ta_symbol_t *symbol_q5 =
    noll_ta_symbol_get_unique_aliased_var (pv_node);
  assert (NULL != symbol_q5);
  vata_add_transition (ta, 5, symbol_q5, succ_empty);

  /*
   * Transition: q6 -> [,s2(in),]()
   *        -- ref to the input of the list
   */
  const noll_ta_symbol_t *symbol_q6 =
    noll_ta_symbol_get_unique_aliased_var (in_node);
  assert (NULL != symbol_q6);
  vata_add_transition (ta, 6, symbol_q6, succ_empty);

  /*
   * Transition: q7 -> [,s2(m(next)),]()
   *        -- ref to the previous inside the list
   */
  const noll_ta_symbol_t *symbol_q7 =
    noll_ta_symbol_get_unique_aliased_marking_up_up (mark_next);
  assert (NULL != symbol_q7);
  vata_add_transition (ta, 7, symbol_q7, succ_empty);
  noll_uid_array_delete (succ_empty);

  /*
   * Transition: q8 -> [<next>, , [eps,next]](q3)
   *        -- implicit link by next from pred to another dll cell
   */
  const noll_ta_symbol_t *symbol_q8_1 =
    noll_ta_symbol_get_unique_allocated (sel_next, NULL, mark_next);
  assert (NULL != symbol_q8_1);
  noll_uid_array *succ_q8 = noll_uid_array_new ();
  noll_uid_array_push (succ_q8, 3);
  vata_add_transition (ta, 8, symbol_q8_1, succ_q8);
  noll_uid_array_delete (succ_q8);

  /*
   * Transition: q8 -> [<next>, {out}, [eps,next]](q4)
   *        -- end of list segment dll
   */
  const noll_ta_symbol_t *symbol_q8_2 =
    noll_ta_symbol_get_unique_allocated (sel_next, vars_out, mark_next);
  assert (NULL != symbol_q8_2);
  succ_q8 = noll_uid_array_new ();
  noll_uid_array_push (succ_q8, 4);
  vata_add_transition (ta, 8, symbol_q8_2, succ_q8);
  noll_uid_array_delete (succ_q8);

  noll_uid_array_delete (mark_eps);
  noll_uid_array_delete (mark_next);
  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (vars_out);
  noll_uid_array_delete (vars_in_out);
  noll_uid_array_delete (sel_next);
  noll_uid_array_delete (sel_next_prev);
  noll_uid_array_delete (sel_prev);

  return ta;
}


 /**
 * Add to the @p ta the transitions encoding the nll predicate,
 * starting from state @p qinit, labeling the first state by @p vars_in,
 * ending in @p vars_out, and marking the first state by @p mark_in.
 *
 * @param ta        the TA to which transitions are added
 * @param pred      the predicate generated
 * @param *_fid     the fields to be used as selector
 * @param qinit     the initial state to which transitions are added
 * @param vars_in   labeling of initial state
 * @param mark_in   marking of the initial state
 * @param out_symbol  symbol for the output transition
 * @param brd_symbol  symbol for the border transition
 * @return          the number of the last state generated for @p ta
 */
uint_t
noll_pred2ta_nll (noll_ta_t * ta,
                  const noll_pred_t * pred,
                  uid_t b_fid,
                  uid_t z_fid,
                  uid_t n_fid,
                  uint_t qinit,
                  const noll_uid_array * vars_in,
                  const noll_uid_array * mark_in,
                  const noll_ta_symbol_t * out_symbol,
                  const noll_ta_symbol_t * brd_symbol)
{

  NOLL_DEBUG ("WARNING: Generating a nested TA for the predicate nll\n");

  assert (NULL != ta);
  assert (NULL != mark_in);     // at least eps
  assert (NULL != out_symbol);
  assert (NULL != brd_symbol);

  /* nested predicate ls */
  noll_pred_t *pred_ls = NULL;
  for (uint_t pid = 0; pid < noll_vector_size (preds_array); pid++)
    if (noll_vector_at (pred->typ->ppreds, pid) == 1)
      pred_ls = noll_vector_at (preds_array, pid);
  assert (NULL != pred_ls);

  /* states of the automaton */
  uint_t q1 = qinit;            // initial cell
  uint_t q2 = qinit + 1;        // inner cells
  uint_t qbrd = qinit + 2;      // border cell
  uint_t q3 = qinit + 3;        // nested ls from init cell
  uint_t q4 = UNDEFINED_ID;     // nested ls from inner cells, computed
  uint_t qlast = UNDEFINED_ID;  // last state used in the inner automaton ls

  /* the selectors <b_fid, z_fid> */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, b_fid);
  noll_uid_array_push (selectors, z_fid);

  /* the marking used mark_in_bkb = mark_in . b_fid */
  noll_uid_array *mark_in_bkb = noll_uid_array_new ();
  assert (NULL != mark_in_bkb);
  noll_uid_array_copy (mark_in_bkb, mark_in);
  noll_marking_push (mark_in_bkb, b_fid);

  /* the marking used mark_in_z = mark_in . z_fid */
  noll_uid_array *mark_in_z = noll_uid_array_new ();
  assert (NULL != mark_in_z);
  noll_uid_array_copy (mark_in_z, mark_in);
  noll_marking_push (mark_in_z, z_fid);

  /* the marking used mark_in_bkb_z = mark_in_bkb . z_fid */
  noll_uid_array *mark_in_bkb_z = noll_uid_array_new ();
  assert (NULL != mark_in_bkb_z);
  noll_uid_array_copy (mark_in_bkb_z, mark_in_bkb);
  noll_marking_push (mark_in_bkb_z, z_fid);

  /*
   * Transition: q1 -> [<s,h>, {in}, [e]] (q2,q3)
   *       -- first cell
   */
  const noll_ta_symbol_t *symbol_q1_1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_1);
  noll_uid_array *succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  noll_uid_array_push (succ_q1, q3);
  vata_add_transition (ta, q1, symbol_q1_1, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [<nll(brd)>, {in}, [e]] (q2)
   *       -- list segment from q1
   */
  const noll_ta_symbol_t *symbol_q1_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_in);
  assert (NULL != symbol_q1_2);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  noll_uid_array_push (succ_q1, qbrd);
  vata_add_transition (ta, q1, symbol_q1_2, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q3 -> [ {brd} ]()
   */
  vata_add_transition (ta, q3, brd_symbol, NULL);

  /*
   * Transition: qbrd -> [ {brd} ]()
   */
  vata_add_transition (ta, qbrd, brd_symbol, NULL);

  /*
   * Transitions: k = ls(f, q3, {}, [e::h], {brd})
   */
  q4 = noll_pred2ta_ls (ta, pred_ls, n_fid, q3, NULL, mark_in_z, brd_symbol);
  assert (UNDEFINED_ID != q4);
  assert (q4 > q3);

  q4 += 1;                      // next state free

  /*
   * Transition: q2 -> [, {out}, ]()
   *       -- end
   */
  vata_add_transition (ta, q2, out_symbol, NULL);

  /*
   * Transition: q2 -> [<nll(brd)>, , [e::s]] (q2)
   *       -- inner list segment
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_2);
  noll_uid_array *succ_q2 = noll_uid_array_new ();
  assert (succ_q2 != NULL);
  noll_uid_array_push (succ_q2, q2);
  noll_uid_array_push (succ_q2, qbrd);
  vata_add_transition (ta, q2, symbol_q2_2, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [<s,h>, {}, [e::s]] (q2,q4)
   *       -- from cell two
   */
  const noll_ta_symbol_t *symbol_q2_3 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_3);
  // succ_q2 = [q2]
  succ_q2 = noll_uid_array_new ();
  assert (succ_q2 != NULL);
  noll_uid_array_push (succ_q2, q2);
  noll_uid_array_push (succ_q2, q4);
  vata_add_transition (ta, q2, symbol_q2_3, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: qn -> [ {brd} ] ()
   */
  vata_add_transition (ta, q4, brd_symbol, NULL);

  /*
   * Transitions: ls(f, qn, {}, [e::s::h], {brd})
   *       -- nested list segment
   */
  qlast =
    noll_pred2ta_ls (ta, pred_ls, n_fid, q4, NULL, mark_in_bkb_z, brd_symbol);
  assert (UNDEFINED_ID != qlast);
  assert (qlast > q4);

  noll_uid_array_delete (mark_in_bkb);
  noll_uid_array_delete (mark_in_z);
  noll_uid_array_delete (mark_in_bkb_z);
  noll_uid_array_delete (selectors);

  return qlast;
}


/**
 * Get the TA for the edge built with predicate 'nll'
 * by instantiating the definition of the
 * 'nll(in, out, brd)' predicate (see ../samples/nll/nll-vc01.smt)
 *
 * nll(in,out,brd) = (in = out) or
 *                 (in != out and exists u,z.
 *                       in -> {(s, u),(h, z)} *
 *                       ls (z,brd) * nll(u,out,brd))
 *
 * to the TA (q1 is a root state):
 *
 * -- only simple fields --
 * q1 -> [<s,h>, {in}, [e]] (q2,q3)
 *       -- first cell
 * q2 -> [<s,h>, {}, [e::s]] (q2,qn)
 *       -- from cell two
 * q2 -> [, {out}, ]()
 *       -- end
 *
 * -- list segments --
 * q1 -> [<nll(brd)>, {in}, [e]] (q2)
 * q2 -> [<nll(brd)>, , [e::s]] (q2)
 *
 * -- imported transitions --
 * q3 -> [ {brd} ]()
 * q3 --> qn-1 = ls(f, q3, {}, [e::h], {brd})
 *
 * qn -> [ {brd} ] ()
 * qn --> qlast =
 *     ls(f, qn, {}, [e::s::h], {brd})
 */
noll_ta_t *
noll_edge2ta_nll (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  NOLL_DEBUG ("WARNING: Generating a fixed TA for the predicate nll\n");

  // get infos about the predicate
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the fields main backbone, inner and nested for the nll predicate */
  uid_t b_fid = UNDEFINED_ID;
  uid_t z_fid = UNDEFINED_ID;
  uid_t n_fid = UNDEFINED_ID;
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    {
      noll_field_e k = noll_vector_at (pred->typ->pfields, fid);
      switch (k)
        {
        case NOLL_PFLD_BCKBONE:
          {
            assert (b_fid == UNDEFINED_ID);
            b_fid = fid;
            break;
          }
        case NOLL_PFLD_INNER:
          {
            assert (z_fid == UNDEFINED_ID);
            z_fid = fid;
            break;
          }
        case NOLL_PFLD_NESTED:
          {
            assert (n_fid == UNDEFINED_ID);
            n_fid = fid;
            break;
          }
        default:
          NOLL_DEBUG ("Error: incorrect field for 'nll' predicate!\n");
          assert (false);
        }
    }
  assert (UNDEFINED_ID != b_fid);
  assert (UNDEFINED_ID != z_fid);
  assert (UNDEFINED_ID != n_fid);

  /* build the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  vata_set_state_root (ta, 1);

  /* identifiers for arguments */
  uid_t in_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);
  uid_t brd_node = noll_vector_at (edge->args, 2);

  /* label of in variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, in_node);

  /* empty marking for first state, mark_eps = [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  const noll_ta_symbol_t *symbol_brd =
    noll_ta_symbol_get_unique_aliased_var (brd_node);
  assert (NULL != symbol_brd);
  const noll_ta_symbol_t *symbol_out =
    noll_ta_symbol_get_unique_aliased_var (end_node);
  assert (NULL != symbol_out);

  noll_pred2ta_nll (ta, pred, b_fid, z_fid, n_fid, 1, vars_in, mark_eps,
                    symbol_out, symbol_brd);

  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (mark_eps);

  return ta;
}


/**
 * Add to the @p ta the transitions encoding the nlcl predicate,
 * starting from state @p qinit, labeling the first state by @p vars_in,
 * ending in @p vars_out, and marking the first state by @p mark_in.
 *
 * @param ta        the TA to which transitions are added
 * @param pred      the predicate generated
 * @param *_fid     the fields to be used as selector
 * @param qinit     the initial state to which transitions are added
 * @param vars_in   labeling of initial state
 * @param mark_in   marking of the initial state
 * @param out_symbol  symbol on the output transition
 * @return          the number of the last state generated for @p ta
 */
uint_t
noll_pred2ta_nlcl (noll_ta_t * ta,
                   const noll_pred_t * pred,
                   uid_t b_fid,
                   uid_t z_fid,
                   uid_t n_fid,
                   uint_t qinit,
                   const noll_uid_array * vars_in,
                   const noll_uid_array * mark_in,
                   const noll_ta_symbol_t * out_symbol)
{

  NOLL_DEBUG ("WARNING: Generating a nested TA for the predicate nlcl\n");

  assert (NULL != ta);
  assert (NULL != mark_in);     // at least eps
  assert (NULL != out_symbol);

  /* nested predicate ls */
  noll_pred_t *pred_ls = NULL;
  for (uint_t pid = 0; pid < noll_vector_size (preds_array); pid++)
    if (noll_vector_at (pred->typ->ppreds, pid) == 1)
      pred_ls = noll_vector_at (preds_array, pid);
  assert (NULL != pred_ls);

  /* states of the automaton */
  uint_t q1 = qinit;            // initial cell
  uint_t q2 = qinit + 1;        // inner cells
  uint_t q3 = qinit + 2;        // nested ls from init cell
  uint_t q4 = UNDEFINED_ID;     // nested ls from inner cells, computed
  uint_t qlast = UNDEFINED_ID;  // last state used in the inner automaton ls

  /* the selectors <b_fid, z_fid> */
  noll_uid_array *selectors = noll_uid_array_new ();
  assert (NULL != selectors);
  noll_uid_array_push (selectors, b_fid);
  noll_uid_array_push (selectors, z_fid);

  /* the marking used mark_in_bkb = mark_in . b_fid */
  noll_uid_array *mark_in_bkb = noll_uid_array_new ();
  assert (NULL != mark_in_bkb);
  noll_uid_array_copy (mark_in_bkb, mark_in);
  noll_marking_push (mark_in_bkb, b_fid);

  /* the marking used mark_in_z = mark_in . z_fid */
  noll_uid_array *mark_in_z = noll_uid_array_new ();
  assert (NULL != mark_in_z);
  noll_uid_array_copy (mark_in_z, mark_in);
  noll_marking_push (mark_in_z, z_fid);

  /* the marking used mark_in_bkb_z = mark_in_bkb . z_fid */
  noll_uid_array *mark_in_bkb_z = noll_uid_array_new ();
  assert (NULL != mark_in_bkb_z);
  noll_uid_array_copy (mark_in_bkb_z, mark_in_bkb);
  noll_marking_push (mark_in_bkb_z, z_fid);

  /*
   * Transition: q1 -> [<s,h>, {in}, [e]] (q2,q3)
   *       -- first cell
   */
  const noll_ta_symbol_t *symbol_q1_1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_1);
  noll_uid_array *succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  noll_uid_array_push (succ_q1, q3);
  vata_add_transition (ta, q1, symbol_q1_1, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [<nlcl>, {in}, [e]] (q2)
   *       -- list segment from q1
   */
  const noll_ta_symbol_t *symbol_q1_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_in);
  // TODO: see if {in} can be added
  assert (NULL != symbol_q1_2);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  vata_add_transition (ta, q1, symbol_q1_2, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transitions: k = ls(f, q3, {}, [e::h], s1[e::h])
   */
  const noll_ta_symbol_t *symb_mark_in_z =
    noll_ta_symbol_get_unique_aliased_marking_up (mark_in_z);
  assert (NULL != symb_mark_in_z);
  q4 =
    noll_pred2ta_ls (ta, pred_ls, n_fid, q3, NULL, mark_in_z, symb_mark_in_z);
  assert (UNDEFINED_ID != q4);
  assert (q4 > q3);

  q4 += 1;                      // next state free

  /*
   * Transition: q2 -> [, {out}, ]()
   *       -- end
   */
  vata_add_transition (ta, q2, out_symbol, NULL);

  /*
   * Transition: q2 -> [<nlcl>, , [e::s]] (q2)
   *       -- inner list segment
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_bkb);
  // TODO: see if {in} can be added
  noll_uid_array *succ_q2 = noll_uid_array_new ();
  assert (NULL != symbol_q2_2);
  assert (succ_q2 != NULL);
  noll_uid_array_push (succ_q2, q2);
  vata_add_transition (ta, q2, symbol_q2_2, succ_q2);
  // succ_q2 used below

  /*
   * Transition: q2 -> [<s,h>, {}, [e::s]] (q2,q4)
   *       -- from cell two
   */
  const noll_ta_symbol_t *symbol_q2_3 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_3);
  // succ_q2 = [q2]
  noll_uid_array_push (succ_q2, q4);
  vata_add_transition (ta, q2, symbol_q2_3, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transitions: ls(f, q4, {}, [e::s::h], s1([e::s::h])
   *       -- nested list segment
   */
  const noll_ta_symbol_t *mark_in_bkb_z_symb =
    noll_ta_symbol_get_unique_aliased_marking_up (mark_in_bkb_z);
  assert (NULL != mark_in_bkb_z_symb);
  qlast =
    noll_pred2ta_ls (ta, pred_ls, n_fid, q4, NULL, mark_in_bkb_z,
                     mark_in_bkb_z_symb);
  assert (UNDEFINED_ID != qlast);
  assert (qlast > q4);

  noll_uid_array_delete (mark_in_bkb);
  noll_uid_array_delete (mark_in_z);
  noll_uid_array_delete (mark_in_bkb_z);
  noll_uid_array_delete (selectors);

  return qlast;
}


/**
 * Get the TA for the edge built with predicate 'nlcl'
 * by instantiating the definition of the
 * 'nlcl(in, out)' predicate (see ../samples/nll/nlcl-vc01.smt)
 *
 * nlcl(in,out) = (in = out) or
 *                (in != out and exists u,z.
 *                       in -> {(s, u),(h, z)} *
 *                       loop (ls (z,z)) * nlcl(u,out))
 *
 * to the TA (q1 is a root state):
 *
 * -- only simple fields --
 * q1 -> [<s,h>, {in}, [e]] (q2,q3)
 *       -- first cell
 * q2 -> [<s,h>, {}, [e::s]] (q2,qn)
 *       -- from cell two
 * q2 -> [, {out}, ]()
 *       -- end
 *
 * -- list segments --
 * q1 -> [<nlcl>, {in}, [e]] (q2)
 * q2 -> [<nlcl>, , [e::s]] (q2)
 *
 * -- imported transitions --
 * k = ls(f, q3, {}, [e::h], s1[e::h])
 * n = k+1
 *     ls(f, qn, {}, [e::s::h], s1[e::s::h])
 */
noll_ta_t *
noll_edge2ta_nlcl (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  NOLL_DEBUG ("WARNING: Generating a fixed TA for the predicate nlcl\n");

  // get infos about the predicate
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);

  /* find the fields main backbone, inner and nested for the nlcl predicate */
  uid_t b_fid = UNDEFINED_ID;
  uid_t z_fid = UNDEFINED_ID;
  uid_t n_fid = UNDEFINED_ID;
  assert (NULL != pred->typ->pfields);
  for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    {
      noll_field_e k = noll_vector_at (pred->typ->pfields, fid);
      switch (k)
        {
        case NOLL_PFLD_BCKBONE:
          {
            assert (b_fid == UNDEFINED_ID);
            b_fid = fid;
            break;
          }
        case NOLL_PFLD_INNER:
          {
            assert (z_fid == UNDEFINED_ID);
            z_fid = fid;
            break;
          }
        case NOLL_PFLD_NESTED:
          {
            assert (n_fid == UNDEFINED_ID);
            n_fid = fid;
            break;
          }
        default:
          NOLL_DEBUG ("Error: incorrect field for 'nll' predicate!\n");
          assert (false);
        }
    }
  assert (UNDEFINED_ID != b_fid);
  assert (UNDEFINED_ID != z_fid);
  assert (UNDEFINED_ID != n_fid);

  /* build the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  vata_set_state_root (ta, 1);

  /* identifiers for arguments */
  uid_t in_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);

  /* label of in variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, in_node);

  /* empty marking for first state, mark_eps = [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  const noll_ta_symbol_t *out_symbol =
    noll_ta_symbol_get_unique_aliased_var (end_node);
  assert (NULL != out_symbol);

  noll_pred2ta_nlcl (ta, pred,
                     b_fid, z_fid, n_fid, 1, vars_in, mark_eps, out_symbol);

  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (mark_eps);

  return ta;
}

uint_t
noll_pred2ta_skl (noll_ta_t * ta,
                  const noll_pred_t * pred,
                  uint_t level,
                  const noll_uid_array * flds,
                  uint_t maxlevel,
                  uint_t qinit,
                  const noll_uid_array * vars_in,
                  const noll_uid_array * mark_in,
                  const noll_ta_symbol_t * out_symbol);

/**
 * Get the TA for the edge built with one of predicates 'skl'
 * by instantiating the definition of the
 * 'skl(in, out)' predicate (see ../samples/nll/skl2-vc01.smt)
 *
 * skl2(in,out) = (in = out) or
 *                (in != out and exists u,z.
 *                       in -> {(f2, u),(f1, z)} *
 *                       skl1 (z,u)) * skl2(u,out))
 *
 * skl1(in,out) = (in = out) or
 *                (in != out and exists u.
 *                       in -> {(f2, NULL),(f1, u)} *
 *                       skl1(u,out))
 *
 * WARNING: the max level supported is 3.
 */
noll_ta_t *
noll_edge2ta_skl (const noll_edge_t * edge)
{
  /* the checks on edge are done in the wrapper function */

  /* get infos about the predicate */
  uint_t pid = edge->label;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  const char *pname = noll_pred_name (edge->label);
  assert (strlen (pname) == 4);

  NOLL_DEBUG ("WARNING: Generating a fixed TA for the predicate %s\n", pname);

  /* get the level of the skl = char after name = number of fields != NULL */
  uint_t level = pname[3] - '0';
  assert (level >= 1);
  assert (level <= 3);

  /* get the max level for this predicate by counting the number of defined fields */
  uint_t maxlevel = 0;
  for (uid_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    if (noll_pred_is_field (pid, fid, NOLL_PFLD_BORDER))
      maxlevel++;

  assert (level <= maxlevel);

  /* find the fields fk with k <= the maxlevel of this predicate */
  noll_uid_array *flds = noll_uid_array_new ();
  noll_uid_array_resize (flds, maxlevel);
  for (uint_t l = 0; l < level; l++)
    noll_vector_at (flds, l) = UNDEFINED_ID;
  for (uid_t fid = 0; fid < noll_vector_size (fields_array); fid++)
    {
      noll_field_t *fld = noll_vector_at (fields_array, fid);
      if (fld->order < maxlevel)
        noll_vector_at (flds, fld->order) = fid;
      else
        assert (false);
    }
  for (uint_t l = 0; l < maxlevel; l++)
    assert (noll_vector_at (flds, l) != UNDEFINED_ID);

  /* build the TA */
  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  vata_set_state_root (ta, 1);

  /* identifiers for arguments */
  uid_t in_node = noll_vector_at (edge->args, 0);
  uid_t end_node = noll_vector_at (edge->args, 1);

  /* label of in variables */
  noll_uid_array *vars_in = noll_uid_array_new ();
  assert (NULL != vars_in);
  noll_uid_array_push (vars_in, in_node);

  /* empty marking for first state, mark_eps = [eps] */
  noll_uid_array *mark_eps = noll_uid_array_new ();
  assert (NULL != mark_eps);
  noll_uid_array_push (mark_eps, NOLL_MARKINGS_EPSILON);

  const noll_ta_symbol_t *out_symbol =
    noll_ta_symbol_get_unique_aliased_var (end_node);
  assert (NULL != out_symbol);
  uint_t qend = noll_pred2ta_skl (ta, pred, level, flds, maxlevel, 1,
                                  vars_in, mark_eps, out_symbol);

  noll_uid_array_delete (vars_in);
  noll_uid_array_delete (mark_eps);

  return ta;
}

/**
 * Add transitions to @p ta for skl1 of fields @p flds.
 *
 * TA generated:
 *
 * q1 = qinit -> [ flds, {in}, [e] ] (qnil^(maxlevel-1), q2)
 * q1 -> [ <skl1>, {in}, [e] ] (q2)
 *
 * qnil -> [ , {nil-0}, ]()
 *
 * q2 -> [, {out}, ] ()
 * q2 -> [ flds, , [e.flds[maxlevel-1]] ] (qnil^(maxlevel-1), q2)
 * q2 -> [ <skl1>, , [e.flds[maxlevel-1] ] (q2)
 *
 */
uint_t
noll_pred2ta_skl1 (noll_ta_t * ta,
                   const noll_pred_t * pred,
                   const noll_uid_array * flds,
                   uint_t maxlevel,
                   uint_t qinit,
                   const noll_uid_array * vars_in,
                   const noll_uid_array * mark_in,
                   const noll_ta_symbol_t * out_symbol)
{
  NOLL_DEBUG
    ("WARNING: Generating a nested TA for the predicate skl1 - max level %d\n",
     maxlevel);

  assert (NULL != ta);
  assert (1 <= maxlevel);
  assert (NULL != flds);
  assert (NULL != mark_in);     // at least eps
  assert (NULL != out_symbol);

  /* states of the automaton */
  uint_t q1 = qinit;
  uint_t q2 = qinit + 1;
  uint_t qnil = qinit + 2;

  /* the selectors <b_fid, z_fid> */
  const noll_uid_array *selectors = flds;

  /* the backbone field for this predicate */
  uint_t b_fid = noll_vector_at (flds, maxlevel - 1);

  /* the marking used mark_in_bkb = mark_in . b_fid */
  noll_uid_array *mark_in_bkb = noll_uid_array_new ();
  assert (NULL != mark_in_bkb);
  noll_uid_array_copy (mark_in_bkb, mark_in);
  noll_marking_push (mark_in_bkb, b_fid);

  /* states for levels > 1 */
  noll_uid_array *succ_nil = noll_uid_array_new ();
  for (uint_t i = 1; i < maxlevel; i++)
    noll_uid_array_push (succ_nil, qnil);

  /*
   * Transition: q1 -> [ flds, {in}, [e] ] (qnil, qnil, q2)
   *       -- first cell
   */
  const noll_ta_symbol_t *symbol_q1_1 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_1);
  noll_uid_array *succ_q1 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q1, succ_nil);
  noll_uid_array_push (succ_q1, q2);
  vata_add_transition (ta, q1, symbol_q1_1, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [ <skl1>, {in}, [e] ] (q2)
   *       -- first list segment
   */
  const noll_ta_symbol_t *symbol_q1_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in);
  // TODO: how to add { in } ?
  assert (NULL != symbol_q1_2);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  vata_add_transition (ta, q1, symbol_q1_2, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: qnil -> [ , {nil-0}, ] ()
   *       -- nil node is 0
   */
  const noll_ta_symbol_t *symbol_qnil =
    noll_ta_symbol_get_unique_aliased_var (0);
  assert (NULL != symbol_qnil);
  noll_uid_array *succ_empty = noll_uid_array_new ();
  vata_add_transition (ta, qnil, symbol_qnil, succ_empty);
  // succ_empty used below

  /*
   * Transition: q2 -> [, {out}, ] ()
   *       -- end of the list
   */
  vata_add_transition (ta, q2, out_symbol, NULL);

  /*
   * Transition: q2 -> [ flds, , [e.flds[maxlevel-1]] ] (qnil, qnil, q2)
   *       -- inner cell in list
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_2);
  noll_uid_array *succ_q2 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q2, succ_nil);
  noll_uid_array_push (succ_q2, q2);
  vata_add_transition (ta, q2, symbol_q2_2, succ_q2);
  noll_uid_array_delete (succ_q2);

/*
 * Transition: q2 -> [ <skl1>, , [e.flds[maxlevel-1] ] (q2)
 *
*/
  const noll_ta_symbol_t *symbol_q2_3 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_3);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, q2);
  vata_add_transition (ta, q2, symbol_q2_3, succ_q2);
  noll_uid_array_delete (succ_q2);

  noll_uid_array_delete (mark_in_bkb);

  return qnil;
}


/**
 * Add transitions to @p ta for skl2 of fields @p flds.
 *
 * TA generated:
 *
 * q1 = qinit
 * qout -> [ {out} ] ()
 *    -- out cell
 * qnil -> [ , {nil-0}, ]()
 *    -- nil cell
 * q1 -> [ <skl2>, {in}, [min] ] (qout)
 *    -- one list segment to out
 * q1 -> [ flds, {in}, [min] ] (qnil^(maxlevel-2), qout, qout)
 *    -- one f2 link, inner skl1 empty
 * q1 -> [ flds, {in}, [min] ] (qnil^(maxlevel-2), qout, qout)
 *    -- one f2 link, inner skl1 non empty
 * q1out --skl1--> q13 (-1) = skl1 (q1out, out)
 *    -- skl1 segment to out
 * q1  -> [ flds, {in}, [min] ] (qnil^(maxlevel-2), q2, q12)
 *     -- at least two f2 links, inner skl1 empty
 * q12 -> [ s3(min . f2) ] ()
 *     -- alias to level 2
 * q1  --> [flds, {in}, [min] ] (qnil^(maxlevel-2), q2, q13)
 *     -- at least two f2 links, inner skl1 non-empty
 * q13 --skl1--> q14(-1) = skl1 (q13, min.f1, to s3(min.f2))
 *     -- skl1 segment to q2
 * q1 -> [ <skl2>, {in}, [min] ] (q2)
 *    -- at least one list segment
 *
 * q2 -> [ flds, , [min.f2] ] (qnil^(maxlevel-2), qout, qout)
 *    -- last fields to qout, inner skl1 empty
 * q2 -> [ flds, , [min.f2] ] (qnil^(maxlevel-2), qout, q1out)
 *    -- last fields to qout, inner skl1 non empty
 * q2 -> [ <skl2>, , [min.f2] ] (qout)
 *    -- last list segment to out
 * q2 -> [ flds, , [min.f2] ] (qnil^(maxlevel-2), q2, q12)
 *    -- inner cell with skl1 empty
 * q2 -> [ flds, , [min.f2] ] (qnil^(maxlevel-2), q2, q14)
 *    -- inner cell with skl1 non empty
 * q2 -> [ <skl2>, , [min . f2] ] (q2)
 *    -- inner list segment
 *
 * q14 --skl1--> qlast=skl1(q14, [min.f2.f1], s3(min.f2))
 *       -- non-empty nested skl1 from inner cell
 */
uint_t
noll_pred2ta_skl2 (noll_ta_t * ta,
                   const noll_pred_t * pred,
                   const noll_uid_array * flds,
                   uint_t maxlevel,
                   uint_t qinit,
                   const noll_uid_array * vars_in,
                   const noll_uid_array * mark_in,
                   const noll_ta_symbol_t * out_symbol)
{
  NOLL_DEBUG
    ("WARNING: Generating a nested TA for the predicate skl2 - max level %d\n",
     maxlevel);

  assert (NULL != ta);
  assert (2 <= maxlevel);
  assert (NULL != flds);
  assert (NULL != mark_in);     // at least eps
  assert (NULL != out_symbol);

  /* states of the automaton */
  uint_t q1 = qinit;
  uint_t qnil = qinit + 1;
  uint_t qout = qnil + 1;
  uint_t q2 = qout + 1;
  uint_t q12 = q2 + 1;
  uint_t q1out = q12 + 1;
  uint_t q2out = UNDEFINED_ID;  // should be computed by calling skl1(q1out)
  uint_t q13 = UNDEFINED_ID;    // should be computed by calling skl1(q2out)
  uint_t q14 = UNDEFINED_ID;    // should be computed by calling skl1(q13)
  uint_t qlast = UNDEFINED_ID;  // should be computed by calling skl1(q14)

  /* the selectors */
  const noll_uid_array *selectors = flds;

  /* the backbone and nested field for this predicate */
  uint_t b_fid = noll_vector_at (flds, maxlevel - 2);
  uint_t n_fid = noll_vector_at (flds, maxlevel - 1);

  /* states for levels > 2 */
  noll_uid_array *succ_nil = noll_uid_array_new ();
  for (uint_t i = 2; i < maxlevel; i++)
    noll_uid_array_push (succ_nil, qnil);

  /* the called predicate skl1 */
  noll_pred_t *pred_skl1 = noll_vector_at (preds_array, 0);
  assert (strcmp (pred_skl1->pname, "skl1") == 0);

  /* the marking used mark_in_bkb = mark_in . b_fid */
  noll_uid_array *mark_in_bkb = noll_uid_array_new ();
  assert (NULL != mark_in_bkb);
  noll_uid_array_copy (mark_in_bkb, mark_in);
  noll_marking_push (mark_in_bkb, b_fid);

  /* the marking used mark_in_nst = mark_in . n_fid */
  noll_uid_array *mark_in_nst = noll_uid_array_new ();
  assert (NULL != mark_in_nst);
  noll_uid_array_copy (mark_in_nst, mark_in);
  noll_marking_push (mark_in_nst, n_fid);

  /* the marking used mark_in_bkb_nst = mark_in . b_fid . n_fid */
  noll_uid_array *mark_in_bkb_nst = noll_uid_array_new ();
  assert (NULL != mark_in_bkb_nst);
  noll_uid_array_copy (mark_in_bkb_nst, mark_in_bkb);
  noll_marking_push (mark_in_bkb_nst, n_fid);

  /*
   * Transition: qnil -> [ , {nil-0}, ] ()
   *       -- nil node is 0
   */
  const noll_ta_symbol_t *symbol_qnil =
    noll_ta_symbol_get_unique_aliased_var (0);
  assert (NULL != symbol_qnil);
  vata_add_transition (ta, qnil, symbol_qnil, NULL);

  /*
   * Transition: qout -> [ {out} ] ()
   *    -- out cell
   */
  vata_add_transition (ta, qout, out_symbol, NULL);

  /*
   * Transition: q12 -> [ s3(min . f2) ] ()
   *     -- alias to level 2
   */
  const noll_ta_symbol_t *symbol_q12 =
    noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_in_bkb);
  assert (NULL != symbol_q12);
  vata_add_transition (ta, q12, symbol_q12, NULL);

  /*
   * Transition: q1 -> [ <skl2>, {in}, [min] ] (qout)
   *       -- one list segment to out
   */
  const noll_ta_symbol_t *symbol_q1_1 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_in);
  assert (NULL != symbol_q1_1);
  noll_uid_array *succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, qout);
  vata_add_transition (ta, q1, symbol_q1_1, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [ <skl2>, {in}, [min] ] (q2)
   *       -- at least one list segment
   */
  const noll_ta_symbol_t *symbol_q1_2 =
    noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_in);
  assert (NULL != symbol_q1_2);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_push (succ_q1, q2);
  vata_add_transition (ta, q1, symbol_q1_2, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [ flds, {in}, [min] ] (qnil, qout, qout)
   *    -- one f2 link, inner skl1 empty
   */
  const noll_ta_symbol_t *symbol_q1_3 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_3);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q1, succ_nil);
  noll_uid_array_push (succ_q1, qout);
  noll_uid_array_push (succ_q1, qout);
  vata_add_transition (ta, q1, symbol_q1_3, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [ flds, {in}, [min] ] (qnil, qout, q1out)
   *    -- one f2 link, inner skl1 non empty
   */
  const noll_ta_symbol_t *symbol_q1_4 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_3);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q1, succ_nil);
  noll_uid_array_push (succ_q1, qout);
  noll_uid_array_push (succ_q1, q1out);
  vata_add_transition (ta, q1, symbol_q1_4, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transition: q1 -> [ flds, {in}, [min] ] (qnil, q2, q12)
   *     -- at least two f2 links, inner skl1 empty
   */
  const noll_ta_symbol_t *symbol_q1_5 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_5);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q1, succ_nil);
  noll_uid_array_push (succ_q1, q2);
  noll_uid_array_push (succ_q1, q12);
  vata_add_transition (ta, q1, symbol_q1_5, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transitions: q1out --skl1--> q13 (-1) = skl1 (q1out, out)
   *    -- skl1 segment to out
   */
  q2out = noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, q1out, NULL,
                             mark_in_nst, out_symbol);
  assert (q2out > q1out);
  q2out++;

  /*
   * Transitions: q2out --skl1--> q19 (-1) = skl1 (q2out, out)
   *    -- skl1 segment to out
   */
  q13 = noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, q2out, NULL,
                           mark_in_bkb_nst, out_symbol);
  assert (q13 > q2out);
  q13++;

  /*
   * Transition: q1 -> [flds, {in}, [min] ] (qnil, q2, q13)
   *     -- at least two f2 links, inner skl1 non-empty
   */
  const noll_ta_symbol_t *symbol_q1_6 =
    noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
  assert (NULL != symbol_q1_6);
  succ_q1 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q1, succ_nil);
  noll_uid_array_push (succ_q1, q2);
  noll_uid_array_push (succ_q1, q13);
  vata_add_transition (ta, q1, symbol_q1_6, succ_q1);
  noll_uid_array_delete (succ_q1);

  /*
   * Transitions: q13 --skl1--> q14(-1) = skl1 (q13, min.f1, to s3(min.f2))
   *     -- skl1 segment to q2
   */
  const noll_ta_symbol_t *mark_in_bkb_symb =
    noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_in_bkb);
  assert (NULL != mark_in_bkb_symb);
  q14 = noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, q13, NULL,
                           mark_in_nst, mark_in_bkb_symb);
  assert (q14 > q13);
  q14++;

  /*
   * Transition: q2 -> [ flds, , [min.f2] ] (qnil, qout, qout)
   *    -- last fields to qout, inner skl1 empty
   */
  const noll_ta_symbol_t *symbol_q2_1 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_1);
  noll_uid_array *succ_q2 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q2, succ_nil);
  noll_uid_array_push (succ_q2, qout);
  noll_uid_array_push (succ_q2, qout);
  vata_add_transition (ta, q2, symbol_q2_1, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [ flds, , [min.f2] ] (qnil, qout, q2out)
   *    -- last fields to qout, inner skl1 non empty
   */
  const noll_ta_symbol_t *symbol_q2_2 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_2);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q2, succ_nil);
  noll_uid_array_push (succ_q2, qout);
  noll_uid_array_push (succ_q2, q2out);
  vata_add_transition (ta, q2, symbol_q2_2, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [ <skl2>, , [min.f2] ] (qout)
   *    -- last list segment to out
   */
  const noll_ta_symbol_t *symbol_q2_3 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_3);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, qout);
  vata_add_transition (ta, q2, symbol_q2_3, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [ <skl2>, , [min . f2] ] (q2)
   *    -- inner list segment
   */
  const noll_ta_symbol_t *symbol_q2_4 =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_4);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_push (succ_q2, q2);
  vata_add_transition (ta, q2, symbol_q2_4, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [ flds, , [min.f2] ] (qnil, q2, q12)
   *    -- inner cell with skl1 empty
   */
  const noll_ta_symbol_t *symbol_q2_5 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_5);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q2, succ_nil);
  noll_uid_array_push (succ_q2, q2);
  noll_uid_array_push (succ_q2, q12);
  vata_add_transition (ta, q2, symbol_q2_5, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * Transition: q2 -> [ flds, , [min.f2] ] (qnil, q2, q14)
   *    -- inner cell with skl1 non empty
   */
  const noll_ta_symbol_t *symbol_q2_6 =
    noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_bkb);
  assert (NULL != symbol_q2_6);
  succ_q2 = noll_uid_array_new ();
  noll_uid_array_copy (succ_q2, succ_nil);
  noll_uid_array_push (succ_q2, q2);
  noll_uid_array_push (succ_q2, q14);
  vata_add_transition (ta, q2, symbol_q2_6, succ_q2);
  noll_uid_array_delete (succ_q2);

  /*
   * q14 --skl1--> qlast=skl1(q14, [min.f2.f1], s3(min.f2))
   *       -- non-empty nested skl1 from inner cell
   */
  qlast =
    noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, q14, NULL,
                       mark_in_bkb_nst, mark_in_bkb_symb);
  assert (qlast > q14);

  noll_uid_array_delete (mark_in_bkb);
  noll_uid_array_delete (mark_in_bkb_nst);
  noll_uid_array_delete (mark_in_nst);

  return qlast;
}

/**
 * Add transitions to @p ta for skl3 of fields @p flds.
 *
 * TA generated:
 *
 * qi3 = qinit
 *
 * qout -> [ (out,alias_out) ] ()
 *      -- last cell
 *
 * --- Initial to out ---
 * qi3 -> [ <skl3>, {in}, [min] ] (qout)
 *    -- one skl3 segment to out
 * qi3 -> [ flds, {in}, [min] ] (qout, qout, qout)
 *    -- one f3 link to out, inner skl2 and skl1 empty
 * qi3 -> [ flds, {in}, [min] ] (qout, qout, qi1out)
 *    -- one f3 link to out, inner skl2 empty, inner skl1 non empty
 * qi1out --skl1--> qi2out(-1) = skl1 (qi1out, [min.f1], out, aliasout)
 *    -- inner skl1 to out from start cell
 * qi3 -> [ flds, {in}, [min] ] (qout, qi2out, qiref2)
 *    -- one f3 link to out, inner skl2 non empty, inner skl1 empty
 * qi2out --skl2--> qiref2(-1) = skl2 (qi2out, [min.f2], out, aliasout)
 *    -- inner skl2 to out from start cell
 * qiref2 -> [ s3(min.f2) ]()
 *    -- reference to level2 from start cell
 * qi3 -> [ flds, {in}, [min] ] (qout, qi2out, qi1ref2)
 *    -- one f3 link to out, inner skl2 and skl1 non empty
 * qi1ref2 --skl1--> qi1ref3(-1) = skl1 (qi1ref2, [min.f1], [min.f2], 3)
 *    -- inner skl1 to level 2 in the start cell
 *
 * --- Initial to inner ---
 * qi3 -> [ <skl3>, {in}, [min] ] (qn3)
 *    -- at least one skl3 segment
 * qi3 -> [ flds, {in}, [min] ] (qn3, qnref3, qnref3)
 *    -- one f3 link inner, inner skl2 and skl1 empty
 * qnref3 -> [ s3(min.f3) ]()
 *    -- reference to inner node
 * qi3 -> [ flds, {in}, [min] ] (qn3, qnref3, qi1ref3)
 *    -- one f3 link to inner, inner skl2 empty, inner skl1 non empty
 * qi1ref3 --skl1--> qi2ref3(-1) = skl1 (qi1ref3, [min.f1], [min.f3], s3)
 *    -- inner skl1 to inner from start cell
 * qi3 -> [ flds, {in}, [min] ] (qn3, qi2ref3, qiref2)
 *    -- one f3 link to inner, inner skl2 non empty, inner skl1 empty
 * qi2ref3 --skl2--> qn1out(-1) = skl2 (qi2ref3, [min.f2], [min.f3], s3)
 *    -- inner skl2 to inner from start cell
 * qi3 -> [ flds, {in}, [min] ] (qn3, qi2ref3, qi1ref2)
 *    -- one f3 link to inner, inner skl2 and skl1 non empty
 *
 * --- Inner to out ---
 * qn3 -> [ <skl3>, , [min.f3] ] (qout)
 *    -- last skl3 segment to out
 * qn3 -> [ flds, , [min.f3] ] (qout, qout, qout)
 *    -- one f3 link to out, inner skl2 and skl1 empty
 * qn3 -> [ flds, , [min.f3] ] (qout, qout, qn1out)
 *    -- one f3 link to out, inner skl2 empty, inner skl1 non empty
 * qn1out --skl1--> qn2out(-1) = skl1 (qn1out, [min.f3.f1], out, aliasout)
 *    -- inner skl1 to out from inner cell
 * qn3 -> [ flds, , [min.f3] ] (qout, qn2out, qnref2)
 *    -- one f3 link to out, inner skl2 non empty, inner skl1 empty
 * qn2out --skl2--> qnref2(-1) = skl2 (qn2out, [min.f3.f2], out, aliasout)
 *    -- inner skl2 to out from inner cell
 * qnref2 -> [ s3(min.f3.f2) ]()
 *    -- reference to level2 from inner cell
 * qn3 -> [ flds, , [min.f3] ] (qout, qn2out, qn1ref2)
 *    -- one f3 link to out, inner skl2 and skl1 non empty
 * qn1ref2 --skl1--> qn1ref3(-1) = skl1 (qn1ref2, [min.f3.f1], [min.f3.f2], 3)
 *    -- inner skl1 to level 2 in the inner cell
 *
 * --- Inner to inner ---
 * qn3 -> [ <skl3>, , [min.f3] ] (qn3)
 *    -- inner skl3 segment
 * qn3 -> [ flds, , [min.f3] ] (qn3, qnref3, qnref3)
 *    -- field f3 to inner, inner skl2 and skl1 empty
 * qn3 -> [ flds, , [min.f3] ] (qn3, qnref3, qn1ref3)
 *    -- field f3 to out, inner skl2 empty, inner skl1 non empty
 * qn1ref3 --skl1--> qn2ref3(-1) = skl1 (qn1ref3, [min.f3.f1], [min.f3], 3)
 *    -- inner skl1 to level 3 in inner cell
 * qn3 -> [ flds, , [min.f3] ] (qn3, qn2ref3, qnref2)
 *    -- one f3 link to inner, inner skl2 non empty, inner skl1 empty
 * qn2ref3 --skl2--> qlast = skl2 (qn2ref3, [min.f3.f2], [min.f3], 3)
 *    -- inner skl2 to level 3 from inner cell
 * qn3 -> [ flds, , [min.f3] ] (qn3, qn2ref3, qn1ref2)
 *    -- one f3 link to out, inner skl2 and skl1 non empty
 */
uint_t
noll_pred2ta_skl3 (noll_ta_t * ta,
                   const noll_pred_t * pred,
                   const noll_uid_array * flds,
                   uint_t maxlevel,
                   uint_t qinit,
                   const noll_uid_array * vars_in,
                   const noll_uid_array * mark_in,
                   const noll_ta_symbol_t * out_symbol)
{
  NOLL_DEBUG
    ("WARNING: Generating a nested TA for the predicate skl3 - max level %d\n",
     maxlevel);

  assert (NULL != ta);
  assert (3 <= maxlevel);
  assert (NULL != flds);
  assert (NULL != mark_in);     // at least eps
  assert (NULL != out_symbol);

  /* states of the automaton */
  uint_t qi3 = qinit;
  uint_t qout = qi3 + 1;
  uint_t qn3 = qout + 1;
  uint_t qlast = qn3;
  /* other states defined locally */

  /* the selectors */
  const noll_uid_array *selectors = flds;

  /* the backbone and nested field for this predicate */
  uint_t f3_fid = noll_vector_at (flds, maxlevel - 3);
  uint_t f2_fid = noll_vector_at (flds, maxlevel - 2);
  uint_t f1_fid = noll_vector_at (flds, maxlevel - 1);

  /* the called predicates skl1, skl2 */
  noll_pred_t *pred_skl1 = noll_vector_at (preds_array, 0);
  assert (strcmp (pred_skl1->pname, "skl1") == 0);
  noll_pred_t *pred_skl2 = noll_vector_at (preds_array, 1);
  assert (strcmp (pred_skl2->pname, "skl2") == 0);


  /* the marking used mark_in_f3 = min . f3 */
  noll_uid_array *mark_in_f3 = noll_uid_array_new ();
  assert (NULL != mark_in_f3);
  noll_uid_array_copy (mark_in_f3, mark_in);
  noll_marking_push (mark_in_f3, f3_fid);

  /* the marking used mark_in_f2 = min . f2 */
  noll_uid_array *mark_in_f2 = noll_uid_array_new ();
  assert (NULL != mark_in_f2);
  noll_uid_array_copy (mark_in_f2, mark_in);
  noll_marking_push (mark_in_f2, f2_fid);

  /* the marking used mark_in_f1 = min . f1_fid */
  noll_uid_array *mark_in_f1 = noll_uid_array_new ();
  assert (NULL != mark_in_f1);
  noll_uid_array_copy (mark_in_f1, mark_in);
  noll_marking_push (mark_in_f1, f1_fid);

  /* the marking used mark_in_f3_f2 = min . f3 . f2 */
  noll_uid_array *mark_in_f3_f2 = noll_uid_array_new ();
  assert (NULL != mark_in_f3_f2);
  noll_uid_array_copy (mark_in_f3_f2, mark_in_f3);
  noll_marking_push (mark_in_f3_f2, f2_fid);

  /* the marking used mark_in_f3_f1 = min . f3 . f1 */
  noll_uid_array *mark_in_f3_f1 = noll_uid_array_new ();
  assert (NULL != mark_in_f3_f1);
  noll_uid_array_copy (mark_in_f3_f1, mark_in_f3);
  noll_marking_push (mark_in_f3_f1, f1_fid);

  /*
   * Transition: qout -> [, {out}, ] ()
   *       -- end of the list
   */
  vata_add_transition (ta, qout, out_symbol, NULL);

  /* --- Initial to out --- */
  /*
   * Transition: qi3 -> [ <skl3>, {in}, [min] ] (qout)
   *    -- one skl3 segment to out
   */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_in);
    // TODO: how to add { in } ?
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qout);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

  /*
   * Transition: qi3 -> [ flds, {in}, [min] ] (qout, qout, qout)
   *    -- one f3 link to out, inner skl2 and skl1 empty
   */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qout);
    noll_uid_array_push (succ_qi3, qout);
    noll_uid_array_push (succ_qi3, qout);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

  /*
   * Transition: qi3 -> [ flds, {in}, [min] ] (qout, qout, qi1out)
   *    -- one f3 link to out, inner skl2 empty, inner skl1 non empty
   */
  uint_t qi1out = ++qlast;
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qout);
    noll_uid_array_push (succ_qi3, qout);
    noll_uid_array_push (succ_qi3, qi1out);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

  /*
   * Transition: qi1out --skl1--> skl1 (qi1out, [min.f1], out, aliasout)
   *    -- inner skl1 to out from start cell
   */
  qlast =
    noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, qi1out, NULL,
                       mark_in_f1, out_symbol);
  assert (qlast > qi1out);

  uint_t qiref2 = ++qlast;
  /*
   * Transition: qiref2 -> [ s3(min.f2) ]()
   *    -- reference to level2 from start cell
   */
  {
    const noll_ta_symbol_t *symbol_qiref2 =
      noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_in_f2);
    assert (NULL != symbol_qiref2);
    vata_add_transition (ta, qiref2, symbol_qiref2, NULL);
  }

  uint_t qi2out = ++qlast;
  /*
   * Transitions:  qi2out --skl2--> qi1ref2(-1) = skl2 (qi2out, [min.f2], out, aliasout)
   *    -- inner skl2 to out from start cell
   */
  qlast = noll_pred2ta_skl2 (ta, pred_skl2, flds, maxlevel, qi2out, NULL,
                             mark_in_f2, out_symbol);
  assert (qlast > qi2out);

  /*
   * Transition: qi3 -> [ flds, {in}, [min] ] (qout, qi2out, qiref2)
   *    -- one f3 link to out, inner skl2 non empty, inner skl1 empty
   */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qout);
    noll_uid_array_push (succ_qi3, qi2out);
    noll_uid_array_push (succ_qi3, qiref2);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

  uint_t qi1ref2 = ++qlast;
  /*
   * Transitions:  qi1ref2 --skl1-->  skl1 (qi1ref2, [min.f1], [min.f2], 3)
   *    -- inner skl1 to level 2 in the start cell
   */
  const noll_ta_symbol_t *mark_in_f2_symb =
    noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_in_f2);
  qlast =
    noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, qi1ref2, NULL,
                       mark_in_f1, mark_in_f2_symb);
  assert (qlast > qi1ref2);

  /*
   * Transition: qi3 -> [ flds, {in}, [min] ] (qout, qi2out, qi1ref2)
   *    -- one f3 link to out, inner skl2 and skl1 non empty
   *
   */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qout);
    noll_uid_array_push (succ_qi3, qi2out);
    noll_uid_array_push (succ_qi3, qi1ref2);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

/* --- Initial to inner --- */
/*
 * Transition: qi3 -> [ <skl3>, {in}, [min] ] (qn3)
 *    -- at least one skl3 segment
 */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_higher_pred (pred, vars_in, mark_in);
    // TODO: how to add { in } ?
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qn3);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

  uint_t qnref3 = ++qlast;
  /*
   * Transition: qnref3 -> [ s3(min.f3) ]()
   *    -- reference to inner node
   */
  {
    const noll_ta_symbol_t *symbol_qnref3 =
      noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_in_f3);
    assert (NULL != symbol_qnref3);
    vata_add_transition (ta, qnref3, symbol_qnref3, NULL);
  }

  /*
   * Transition: qi3 -> [ flds, {in}, [min] ] (qn3, qnref3, qnref3)
   *    -- one f3 link inner, inner skl2 and skl1 empty
   */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qn3);
    noll_uid_array_push (succ_qi3, qnref3);
    noll_uid_array_push (succ_qi3, qnref3);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

  uint_t qi1ref3 = ++qlast;
  /*
   * Transition: qi3 -> [ flds, {in}, [min] ] (qn3, qnref3, qi1ref3)
   *    -- one f3 link to inner, inner skl2 empty, inner skl1 non empty
   */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qn3);
    noll_uid_array_push (succ_qi3, qnref3);
    noll_uid_array_push (succ_qi3, qi1ref3);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

  /*
   * Transitions: qi1ref3 --skl1--> skl1 (qi1ref3, [min.f1], [min.f3], s3)
   *    -- inner skl1 to inner from start cell
   */
  const noll_ta_symbol_t *mark_in_f3_symb =
    noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_in_f3);
  assert (NULL != mark_in_f3_symb);
  qlast = noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, qi1ref3, NULL,
                             mark_in_f1, mark_in_f3_symb);
  assert (qlast > qi1ref3);

  uint_t qi2ref3 = ++qlast;
  /*
   * Transition: qi3 -> [ flds, {in}, [min] ] (qn3, qi2ref3, qiref2)
   *    -- one f3 link to inner, inner skl2 non empty, inner skl1 empty
   */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qn3);
    noll_uid_array_push (succ_qi3, qi2ref3);
    noll_uid_array_push (succ_qi3, qiref2);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }

  /*
   * Transitions: qi2ref3 --skl2--> skl2 (qi2ref3, [min.f2], [min.f3], s3)
   *    -- inner skl2 to inner from start cell
   */
  qlast = noll_pred2ta_skl2 (ta, pred_skl2, flds, maxlevel, qi2ref3, NULL,
                             mark_in_f2, mark_in_f3_symb);
  assert (qlast > qi2ref3);

  /*
   * qi3 -> [ flds, {in}, [min] ] (qn3, qi2ref3, qi1ref2)
   *    -- one f3 link to inner, inner skl2 and skl1 non empty
   */
  {
    const noll_ta_symbol_t *symbol_qi3 =
      noll_ta_symbol_get_unique_allocated (selectors, vars_in, mark_in);
    assert (NULL != symbol_qi3);
    noll_uid_array *succ_qi3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qi3, qn3);
    noll_uid_array_push (succ_qi3, qi2ref3);
    noll_uid_array_push (succ_qi3, qi1ref2);
    vata_add_transition (ta, qi3, symbol_qi3, succ_qi3);
    noll_uid_array_delete (succ_qi3);
  }


  /* --- Inner to out --- */

  /*
   * Transition: qn3 -> [ <skl3>, , [min.f3] ] (qout)
   *    -- last skl3 segment to out
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qout);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  /*
   * Transition: qn3 -> [ flds, , [min.f3] ] (qout, qout, qout)
   *    -- one f3 link to out, inner skl2 and skl1 empty
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qout);
    noll_uid_array_push (succ_qn3, qout);
    noll_uid_array_push (succ_qn3, qout);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  uint_t qn1out = ++qlast;
  /*
   * Transition: qn3 -> [ flds, , [min.f3] ] (qout, qout, qn1out)
   *    -- one f3 link to out, inner skl2 empty, inner skl1 non empty
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qout);
    noll_uid_array_push (succ_qn3, qout);
    noll_uid_array_push (succ_qn3, qn1out);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  /*
   * Transition: qn1out --skl1--> skl1 (qn1out, [min.f3.f1], out, aliasout)
   *    -- inner skl1 to out from inner cell
   */
  qlast =
    noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, qn1out, NULL,
                       mark_in_f3_f1, out_symbol);
  assert (qlast > qn1out);

  uint_t qnref2 = ++qlast;
  uint_t qn2out = ++qlast;
  /*
   * Transition: qn3 -> [ flds, , [min.f3] ] (qout, qn2out, qnref2)
   *    -- one f3 link to out, inner skl2 non empty, inner skl1 empty
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qout);
    noll_uid_array_push (succ_qn3, qn2out);
    noll_uid_array_push (succ_qn3, qnref2);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  /*
   * Transition: qnref2 -> [ s3(min.f3.f2) ]()
   *    -- reference to level2 from inner cell
   */
  {
    const noll_ta_symbol_t *symbol_qnref2 =
      noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_in_f3_f2);
    assert (NULL != symbol_qnref2);
    vata_add_transition (ta, qnref2, symbol_qnref2, NULL);
  }

  /*
   * Transition: qn2out --skl2--> skl2 (qn2out, [min.f3.f2], out, aliasout)
   *    -- inner skl2 to out from inner cell
   */
  qlast =
    noll_pred2ta_skl2 (ta, pred_skl2, flds, maxlevel, qn2out, NULL,
                       mark_in_f3_f2, out_symbol);
  assert (qlast > qn2out);

  uint_t qn1ref2 = ++qlast;
  /*
   * Transition: qn3 -> [ flds, , [min.f3] ] (qout, qn2out, qn1ref2)
   *    -- one f3 link to out, inner skl2 and skl1 non empty
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qout);
    noll_uid_array_push (succ_qn3, qn2out);
    noll_uid_array_push (succ_qn3, qn1ref2);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  /*
   * Transition: qn1ref2 --skl1--> skl1 (qn1ref2, [min.f3.f1], [min.f3.f2], 3)
   *    -- inner skl1 to level 2 in the inner cell
   */
  const noll_ta_symbol_t *mark_in_f3_f2_symb =
    noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_in_f3_f2);
  qlast = noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, qn1ref2, NULL,
                             mark_in_f3_f1, mark_in_f3_f2_symb);
  assert (qlast > qn1ref2);

  /* --- Inner to inner --- */
  /*
   * Transition: qn3 -> [ <skl3>, , [min.f3] ] (qn3)
   *    -- inner skl3 segment
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_higher_pred (pred, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qn3);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  /*
   * Transition: qn3 -> [ flds, , [min.f3] ] (qn3, qnref3, qnref3)
   *    -- field f3 to inner, inner skl2 and skl1 empty
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qn3);
    noll_uid_array_push (succ_qn3, qnref3);
    noll_uid_array_push (succ_qn3, qnref3);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  uint_t qn1ref3 = ++qlast;
  /*
   * Transition: qn3 -> [ flds, , [min.f3] ] (qn3, qnref3, qn1ref3)
   *    -- field f3 to out, inner skl2 empty, inner skl1 non empty
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qn3);
    noll_uid_array_push (succ_qn3, qnref3);
    noll_uid_array_push (succ_qn3, qn1ref3);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  /*
   * Transition: qn1ref3 --skl1--> skl1 (qn1ref3, [min.f3.f1], [min.f3], 3)
   *    -- inner skl1 to level 3 in inner cell
   */
  qlast =
    noll_pred2ta_skl1 (ta, pred_skl1, flds, maxlevel, qn1ref3, NULL,
                       mark_in_f3_f1, mark_in_f3_symb);
  assert (qlast > qn1ref3);

  uint_t qn2ref3 = ++qlast;
  /*
   * Transition: qn3 -> [ flds, , [min.f3] ] (qn3, qn2ref3, qnref2)
   *    -- one f3 link to inner, inner skl2 non empty, inner skl1 empty
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qn3);
    noll_uid_array_push (succ_qn3, qn2ref3);
    noll_uid_array_push (succ_qn3, qnref2);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  /*
   * Transition: qn2ref3 --skl2--> qlast = skl2 (qn2ref3, [min.f3.f2], [min.f3], 3)
   *    -- inner skl2 to level 3 from inner cell
   */
  qlast =
    noll_pred2ta_skl2 (ta, pred_skl2, flds, maxlevel, qn2ref3, NULL,
                       mark_in_f3_f2, mark_in_f3_symb);
  assert (qlast > qn2ref3);

  /*
   * Transition: qn3 -> [ flds, , [min.f3] ] (qn3, qn2ref3, qn1ref2)
   *    -- one f3 link to out, inner skl2 and skl1 non empty
   */
  {
    const noll_ta_symbol_t *symbol_qn3 =
      noll_ta_symbol_get_unique_allocated (selectors, NULL, mark_in_f3);
    assert (NULL != symbol_qn3);
    noll_uid_array *succ_qn3 = noll_uid_array_new ();
    noll_uid_array_push (succ_qn3, qn3);
    noll_uid_array_push (succ_qn3, qn2ref3);
    noll_uid_array_push (succ_qn3, qn1ref2);
    vata_add_transition (ta, qn3, symbol_qn3, succ_qn3);
    noll_uid_array_delete (succ_qn3);
  }

  noll_uid_array_delete (mark_in_f3);
  noll_uid_array_delete (mark_in_f2);
  noll_uid_array_delete (mark_in_f1);
  noll_uid_array_delete (mark_in_f3_f1);
  noll_uid_array_delete (mark_in_f3_f2);

  return qlast;
}

/**
 * Add to the @p ta the transitions encoding the skl(@p level) predicate,
 * starting from state @p qinit, labeling the first state by @p vars_in,
 * ending in @p vars_out, and marking the first state by @p mark_in.
 *
 * @param ta        the TA to which transitions are added
 * @param pred      the predicate generated
 * @param level     the level of the predicate <= @p maxlevel
 * @param flds      the fields to be used as selector
 * @param maxlevel  the size of the @p flds
 * @param qinit     the initial state to which transitions are added
 * @param vars_in   labeling of initial state
 * @param mark_in   marking of the initial state
 * @param out_symbol  symbol for the output transition
 * @return          the number of the last state generated for @p ta
 */
uint_t
noll_pred2ta_skl (noll_ta_t * ta,
                  const noll_pred_t * pred,
                  uint_t level,
                  const noll_uid_array * flds,
                  uint_t maxlevel,
                  uint_t qinit,
                  const noll_uid_array * vars_in,
                  const noll_uid_array * mark_in,
                  const noll_ta_symbol_t * out_symbol)
{
  NOLL_DEBUG
    ("WARNING: Generating a nested TA for the predicate skl%d (of %d fields)\n",
     level, maxlevel);

  if (level == 1)
    return noll_pred2ta_skl1 (ta, pred, flds, maxlevel, qinit, vars_in,
                              mark_in, out_symbol);

  if (level == 2)
    return noll_pred2ta_skl2 (ta, pred, flds, maxlevel, qinit, vars_in,
                              mark_in, out_symbol);

  if (level == 3)
    return noll_pred2ta_skl3 (ta, pred, flds, maxlevel, qinit, vars_in,
                              mark_in, out_symbol);

  assert (false);

  return qinit;
}



/**
 * Get the TA for the @p edge.
 *
 * @param edge    A predicate edge
 * @return        A TA recorgnizing the tree encodings for this edge
 */
noll_ta_t *
noll_edge2ta (const noll_edge_t * edge)
{
  assert (NULL != edge);
  assert (NOLL_EDGE_PRED == edge->kind);
  assert (2 <= noll_vector_size (edge->args));

  const uid_t pid = edge->label;
  const noll_pred_t *pred = noll_pred_getpred (edge->label);
  assert (NULL != pred);
  assert (NULL != pred->pname);
  assert (NULL != pred->def);
  assert (noll_vector_size (edge->args) == pred->def->fargs);

  NOLL_DEBUG
    ("********************************************************************************\n");
  NOLL_DEBUG
    ("*                                 EDGE -> TA                                   *\n");
  NOLL_DEBUG
    ("********************************************************************************\n");

  vata_ta_t *ta = NULL;
  if ((ta = vata_create_ta ()) == NULL)
    {
      return NULL;
    }

  NOLL_DEBUG ("Edge: args = %u\n", noll_vector_size (edge->args));
  NOLL_DEBUG ("  args[0] = %u\n", noll_vector_at (edge->args, 0));
  NOLL_DEBUG ("  args[1] = %u\n", noll_vector_at (edge->args, 1));

  NOLL_DEBUG ("Exposing the predicate structure\n");
  NOLL_DEBUG ("Name: %s\n", pred->pname);
  const noll_pred_binding_t *def = pred->def;
  assert (NULL != def);
  NOLL_DEBUG ("definition:\n");
  NOLL_DEBUG ("  arguments: %zu\n", def->pargs);
  NOLL_DEBUG ("  formal arguments: %u\n", def->fargs);

  assert (NULL != def->sigma_0);
  NOLL_DEBUG ("Sigma_0 kind: %u\n", def->sigma_0->kind);
  NOLL_DEBUG ("Sigma_0 is precise: %s\n",
              def->sigma_0->is_precise ? "true" : "false");

  //MS: changed to support nll!
  if (NULL == def->sigma_1)
    NOLL_DEBUG ("Sigma_1: empty\n");
  else
    {
      NOLL_DEBUG ("Sigma_1: predicate with nesting\n");
      NOLL_DEBUG ("Sigma_1 kind: %u\n", def->sigma_1->kind);
      NOLL_DEBUG ("Sigma_1 is precise: %s\n",
                  def->sigma_1->is_precise ? "true" : "false");
    }

  if ((0 == strcmp (pred->pname, "lso")) || (0 == strcmp (pred->pname, "ls")))
    {                           // this is the "ls" predicate

      ta = noll_edge2ta_ls (edge);
    }
  else if (0 == strcmp (pred->pname, "lsso"))
    {
      ta = noll_edge2ta_lss (edge);
    }
  else if (0 == strcmp (pred->pname, "dll"))
    {
      ta = noll_edge2ta_dll (edge);
    }
  else if (0 == strcmp (pred->pname, "nll"))
    {
      ta = noll_edge2ta_nll (edge);
    }
  else if (0 == strcmp (pred->pname, "nlcl"))
    {
      ta = noll_edge2ta_nlcl (edge);
    }
  else if (0 == strncmp (pred->pname, "skl", 3))
    {
      ta = noll_edge2ta_skl (edge);
    }
  else
    {
      /* init of global arrays */
      noll_pred2graph_init ();
      noll_pred2tree_init ();
      /* apply the general algorithm */
      ta = noll_edge2ta_gen (edge);
      if (NULL == ta)
        {
          NOLL_DEBUG ("ERROR: translation for predicate %s failed!\n",
                      pred->pname);
          assert (false);
        }
    }

  NOLL_DEBUG ("Generated TA for edge:\n");
#ifndef NDEBUG
  vata_print_ta (ta);
#endif
  NOLL_DEBUG ("*** END EDGE -> TA\n");


  return ta;
}
