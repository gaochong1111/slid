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
 * Defines translation between heap graph to tree automata 
 * for any predicate definition.
 */

#include "noll.h"
#include "libvata_noll_iface.h"
#include "noll2graph.h"
#include "noll_pred2ta.h"
#include "noll_graph2ta.h"
#include "noll_ta_symbols.h"

/**
 * @brief Compute parameters for the next nested predicate
 *        (next call of noll_edge2ta_gen_aux)
 * 
 * @param
 */
void
noll_edge2ta_gen_param (noll_tree_t * tree,
                      const noll_pred_t * pred,
                      const noll_tree_node_t *node_i,
                      size_t i,
                      uid_t q_src, uid_t q_dst,
                      uid_t init_node, uid_t end_node,
                      uint_t offset,
                      const noll_ta_symbol_array *y,
                      uid_t *pid_i,
                      uid_t *q_i, uid_t *q_j,
                      noll_ta_symbol_array *vmap_i)
{
      *pid_i = noll_ta_symbol_get_pid (node_i->symbol);
      const noll_pred_t *pred_i = noll_pred_getpred (*pid_i);
      assert (i != init_node);
      assert (i != end_node);
      *q_i = i + offset;

      uid_t j = noll_vector_at (node_i->children, 0);
      const noll_tree_node_t *node_j = noll_vector_at (tree->nodes, j);

      *q_j = j;
      if (*q_j == init_node)
        *q_j = q_src;
      else if (*q_j == end_node)
        *q_j = q_dst;
      else
        *q_j = j + offset;

      // TODO: update with good values when the args of a
      // predicate label are filled
      /*noll_uid_array_push (vmap_i, 0); // null mapped to null 
      noll_uid_array_push (vmap_i, *q_i);
      noll_uid_array_push (vmap_i, *q_j);*/
      // null mapped to null 
      noll_ta_symbol_array_push (vmap_i,
        noll_ta_symbol_get_unique_aliased_var (0)); 
      // first arg mapeed to node_i 
      noll_ta_symbol_array_push (vmap_i,  
        noll_ta_symbol_get_unique_aliased_symbol(node_i->symbol, y));
      // first arg mapeed to node_j 
      noll_ta_symbol_array_push (vmap_i,  
        noll_ta_symbol_get_unique_aliased_symbol(node_j->symbol, y));
    
      // border arguments
      // TODO: update when tree symbols store predicate args
      for (size_t i = 2; i < pred->def->fargs; i++)
        noll_ta_symbol_array_push (vmap_i, 
          noll_ta_symbol_get_unique_aliased_var (i)); // not correct!

}

/**
 * @brief Builds the TA with the specified arguments.
 *
 * @param ta         the TA to which transitions are added
 * @param pid        the predicate identifier
 * @param q_src      the initial state
 * @param src_symbol symbol for the initial state
 * @param q_dst      the end state
 * @param y          array of actual param symbols with y[0] is null
 * @param offset     used to add more states in the TA
 * @return           the number of the last state generated
 */
uint_t
noll_edge2ta_gen_aux (noll_ta_t * ta,
                      const uid_t pid,
                      uint_t q_src,
                      const noll_ta_symbol_t * src_symbol,
                      uint_t q_dst, 
                      const noll_ta_symbol_array * y,
                      uint_t offset)
{
  NOLL_DEBUG ("\nWARNING: Generating a nested TA for %s\n",
              noll_pred_name (pid));

  assert (NULL != ta);
  assert (NULL != y);

  /* informations about the predicate in the global tables */
  const noll_pred_t *pred = noll_pred_getpred (pid);
  noll_graph_t *graph = noll_pred2graph (pred);
  noll_tree_t *tree = noll_pred2tree (pred);

  uid_t init_node = graph->var2node[1];
  uid_t end_node = graph->var2node[2];
  uid_t x_tl_node = graph->var2node[1 + pred->def->fargs];
  uid_t q_x_tl = x_tl_node + offset;
  uid_t q_last = noll_vector_size (tree->nodes) + offset - 1;

#ifndef NDEBUG
  fprintf (stdout, "\nwith params :\n"
           "\tpid : %d\n"
           "\tq src : %d\n"
           "\tq dst : %d\n"
           "\tsrc symbol : <%s>\n"
           "\toffset : %d\n\n"
           "\tinitial_node = node(%d)\n"
           "\tend_node = node(%d)\n"
           "\txtl_node = node(%d)\n"
           "\tstate q_xtl = %d\n"
           "\tstate q_last = %d\n",
           pid, q_src, q_dst,
           noll_ta_symbol_get_str (src_symbol), offset,
           init_node, end_node, x_tl_node, q_x_tl, q_last);
  fflush (stdout);
#endif

  /* 1) Skeleton of TA */
  /* For each node of the tree */
  for (size_t i = 0; i < noll_vector_size (tree->nodes); ++i)
    {
      const noll_tree_node_t *node = noll_vector_at (tree->nodes, i);
      if (NULL == node)
        /* some nodes are not filled in the tree, e.g., null */
        continue;

      assert (NULL != node->symbol);

      NOLL_DEBUG ("\n\t- node symbol <%s>\n",
                  noll_ta_symbol_get_str (node->symbol));
      uid_t q_i = 0;
      if (i == init_node)
        q_i = q_src;
      else if (i == end_node)
        q_i = q_dst;
      else
        q_i = i + offset;

      noll_uid_array *q_children = NULL;
      if (node->children != NULL)
        {
          q_children = noll_uid_array_new ();
          // push all node->children in q_children with offset
          // except init_node, end_node which are push with 
          // resp q_src and q_dst
          for (size_t j = 0; j < noll_vector_size (node->children); j++)
            {
              uid_t child = noll_vector_at (node->children, j);
              if (child == init_node)
                noll_uid_array_push (q_children, q_src);
              else if (child == end_node)
                noll_uid_array_push (q_children, q_dst);
              else
                noll_uid_array_push (q_children, child + offset);
            }
        }

      /* Alias transitions (6) */
      if (noll_ta_symbol_is_alias (node->symbol))
        {
          NOLL_DEBUG ("Node %zu : alias\n", i);
          if ((i != end_node) || (offset == 0))
            {
              /* alias is added on the end node only at then topmost level */
              /* rename formal param to actual parameter */
              NOLL_DEBUG ("\t - added trasition\n");
              const noll_ta_symbol_t *asymbol =
                noll_ta_symbol_get_unique_renamed (node->symbol,
                                                   (offset ==
                                                    0) ? true : false,
                                                   y, NULL);
              vata_add_transition (ta, q_i, asymbol, NULL);
            }
        }
      /* Predicate transitions (7) */
      else if (noll_ta_symbol_is_pred (node->symbol))
        {
          NOLL_DEBUG ("Node %zu : pred with %d border params\n", i,
                      (node->children == NULL) ? 0 : noll_vector_size(node->children));
          /* rename node symbol arguments with markings wrt 
           * the source node of the edge */
          /* TODO: compute the marking wrt source node */
          const noll_ta_symbol_t *asymbol =
            noll_ta_symbol_get_unique_renamed (node->symbol,
                                               (offset == 0) ? true : false,
                                               y, NULL);
          vata_add_transition (ta, q_i, asymbol, q_children);
        }
      /* Points-to edges (8)(9) */
      else if (noll_ta_symbol_is_pto (node->symbol))
        {
          NOLL_DEBUG ("Node %zu : pto\n", i);
          if (i == tree->root)
            {
              NOLL_DEBUG ("Node %zu (root): add pto loops in %d\n", i,
                          x_tl_node);
              // Transitions (9')
              vata_add_transition (ta, q_x_tl,
                                   noll_vector_at (tree->nodes,
                                                   x_tl_node)->symbol,
                                   q_children);
            }
          if (i == x_tl_node)
            {
              NOLL_DEBUG ("Node %zu: add pto in %d\n", i, init_node);
              // Transitions (9'')
              /* rename formal parameters to actual parameters */
              const noll_ta_symbol_t *asymbol =
                noll_ta_symbol_get_unique_renamed (noll_vector_at
                                                   (tree->nodes,
                                                    init_node)->symbol,
                                                   (offset ==
                                                    0) ? true : false,
                                                   y, NULL);
              vata_add_transition (ta, q_src, asymbol, q_children);
            }
          // Transitions (8)
          const noll_ta_symbol_t *asymbol = node->symbol;
          if ((offset != 0) && (i == init_node))
            asymbol = noll_ta_symbol_get_unique_renamed (noll_vector_at
                                                         (tree->nodes,
                                                          init_node)->symbol,
                                                         false, y, NULL);
          vata_add_transition (ta, q_i, asymbol, q_children);
        }
    }

  /* Transitions (13-14): predicate edge from q(node(x_tl)) */
  const noll_uid_array *x_tl_mark =
    noll_ta_symbol_get_marking (noll_vector_at (tree->nodes,
                                                x_tl_node)->symbol);
  assert (NULL != x_tl_mark);
  /* TODO: push arguments into the symbol */
  const noll_ta_symbol_t *pred_symbol_tl =
    noll_ta_symbol_get_unique_higher_pred (pred, NULL, x_tl_mark);
  assert (NULL != pred_symbol_tl);
  /* compute the children */
  noll_uid_array *pred_children1 = noll_uid_array_new ();
  noll_uid_array *pred_children2 = noll_uid_array_new ();
  noll_uid_array_push (pred_children1, q_x_tl);
  noll_uid_array_push (pred_children2, q_dst);
  // Transitions (13)
  vata_add_transition (ta, q_x_tl, pred_symbol_tl, pred_children1);
  // Transitions (14)
  vata_add_transition (ta, q_x_tl, pred_symbol_tl, pred_children2);

  /* Transitions (15): predicate edge from q(node(init)) */
  const noll_uid_array *init_vars = noll_ta_symbol_get_vars (src_symbol);
  const noll_uid_array *init_mark = noll_ta_symbol_get_marking (src_symbol);
  assert (NULL != init_mark);
  const noll_ta_symbol_t *pred_symbol_init =
    noll_ta_symbol_get_unique_higher_pred (pred, init_vars, init_mark);
  // Transitions (15)
  vata_add_transition (ta, q_src, pred_symbol_init, pred_children1);

  noll_uid_array_delete (pred_children1);
  noll_uid_array_delete (pred_children2);
  
  
  /* 2) Include the ta of called preds */
  /* For each node of the tree */
  for (uint_t i = 0; i < noll_vector_size (tree->nodes); ++i)
    {
      const noll_tree_node_t *node_i = noll_vector_at (tree->nodes, i);
      if (NULL == node_i)
        /* some nodes are not filled in the tree, e.g., null */
        continue;

      assert (NULL != node_i->symbol);
      if (!noll_ta_symbol_is_pred (node_i->symbol))
        continue;
      
      uid_t pid_i = UNDEFINED_ID;
      uid_t q_i = UNDEFINED_ID, q_j = UNDEFINED_ID;
      noll_ta_symbol_array *vmap_i = noll_ta_symbol_array_new ();
      /* from i starts an edge with a predicate call,
       * call recursively the function to include the 
       * transitions of the matrix of this predicate
       */
      noll_edge2ta_gen_param (tree, pred, node_i, i,
                              q_src, q_dst,
                              init_node, end_node, offset,
                              y,
                              &pid_i, &q_i, &q_j,
                              vmap_i);
                              
      q_last = noll_edge2ta_gen_aux (ta, pid_i,
                                     q_i, node_i->symbol, q_j,
                                     vmap_i, q_last);
    }

  /* 3) If nested call, insert alias to q_dst from q_src */
  if (offset != 0)
    {
      // TODO: fill with alias var only if the parameter is an aliased var
      // otherwise use an aliased marking
      const noll_ta_symbol_t *asymbol = noll_vector_at (y, 2);
      assert (asymbol != NULL);
      vata_add_transition (ta, q_src, asymbol, NULL);
    }

  return q_last;
}


/**
 * @brief Get the TA for the @p edge.
 *
 * @param  edge  A predicate edge
 * @return       A TA recognizing the tree encodings for this edge
 */
noll_ta_t *
noll_edge2ta_gen (const noll_edge_t * edge)
{
  assert (NULL != edge);
  assert (NOLL_EDGE_PRED == edge->kind);
  assert (2 <= noll_vector_size (edge->args));

  /* identifier of the predicate */
  const uid_t pid = edge->label;
  /* informations about the predicate in the global table */
  const noll_pred_t *pred = noll_pred_getpred (pid);
  /* check that these informations are filled and correct */
  assert (NULL != pred);
  assert (NULL != pred->pname);
  assert (NULL != pred->def);
  assert (noll_vector_size (edge->args) == pred->def->fargs);

  /* the formal parameters are in pred->def->vars[1,pred->def->fargs], 
   * @see noll_preds.h */
  /* the actual parameters (their identifiers) are in edge->args, 
   * @see noll_graph.h */

  NOLL_DEBUG ("\nBuild the symbols for actual params\n");
  /*
   * The formals vars in pred->def->vars[0,pred->def->fargs] 
   * are mapped to 0(null) o edge->args
   */
  noll_ta_symbol_array *vmap = noll_ta_symbol_array_new ();
  noll_ta_symbol_array_push (vmap, 
  noll_ta_symbol_get_unique_aliased_var (0));     // null mapped to null
  for (size_t i = 0; i < noll_vector_size (edge->args); i++)
    noll_ta_symbol_array_push (vmap, 
    noll_ta_symbol_get_unique_aliased_var (noll_vector_at (edge->args, i)));

  /* 
   * The matrix of the predicate is stored in
   * pred->def->sigma0 (points-to)
   * pred->def->sigma1 (nested predicate calls)
   */
#ifndef NDEBUG
  fprintf (stdout, "Exposing the predicate matrix:\n\t- pto part:\n");
  noll_space_fprint (stdout, pred->def->vars, NULL, pred->def->sigma_0);
  fprintf (stdout, "\n\t- nested calls part:\n");
  noll_space_fprint (stdout, pred->def->vars, NULL, pred->def->sigma_1);
  fflush (stdout);
#endif

  /* Get the graph */
  noll_graph_t *gp = noll_pred2graph (pred);
  assert (NULL != gp);
  /* Get the tree */
  noll_tree_t *treep = noll_pred2tree (pred);
  assert (NULL != treep);

  NOLL_DEBUG ("\nBuild the TA recognizing the tree\n");
  vata_ta_t *tap = NULL;
  if ((tap = vata_create_ta ()) == NULL)
    {
      return NULL;
    }
  /* set the root = root of tree */
  vata_set_state_root (tap, treep->root);

  /* node identifiers */
  uid_t initial_node = gp->var2node[1];
  assert (initial_node == treep->root);
  uid_t end_node = gp->var2node[2];
  uid_t x_tl_node = gp->var2node[1 + noll_vector_size (edge->args)];

#ifndef NDEBUG
  fprintf (stdout, "- initial_node = node(%d)\n", initial_node);
  fprintf (stdout, "- end_node = node(%d)\n", end_node);
  fflush (stdout);
#endif

  uid_t q_last = noll_edge2ta_gen_aux (tap,
                                       pid,
                                       initial_node,
                                       noll_vector_at (treep->nodes,
                                                       initial_node)->symbol,
                                       end_node,
                                       vmap,
                                       0);

#ifndef NDEBUG
  fprintf (stdout, "Returned q_last = %d\n", q_last);
  fflush (stdout);
#endif

  noll_ta_symbol_array_delete (vmap);

  return tap;
}


/**
 * @brief  Returns or builds (if not exist) the graph translating the predicate.
 * 
 * @param[in]  pred  The predicate
 * 
 * @returns The unique graph translated from the predicate
 */
noll_graph_t *
noll_pred2graph (const noll_pred_t * pred)
{
  noll_graph_t *g = noll_vector_at (pred2graph_array, pred->pid);
  if (g != NULL)
    return g;

  /*
   * Build a graph from the predicate matrix by calling noll_graph_of_form
   * - first build the formula matrix(in,x_tl) * matrix (x_tl,out)
   * - then call noll_graph_of_form
   */
  NOLL_DEBUG ("\nBuild the graph of the predicate matrix\n");
  noll_form_t *phip = noll_pred_get_matrix (pred->pid);
  g = noll_graph_of_form (phip, true);
  assert ((pred->def->fargs + 1) <= noll_vector_size (g->lvars));
#ifndef NDEBUG
  noll_graph_fprint (stdout, g);
  fflush (stdout);
#endif

  /* save it for a possible reuse */
  NOLL_VECTOR_ARRAY (pred2graph_array)[pred->pid] = g;
  return g;
}


/**
 * @brief  Returns or builds (if not exist) the tree encoding the predicate.
 * 
 * @param[in]  pred  The predicate
 * 
 * @returns The unique tree encodings the predicate
 */
noll_tree_t *
noll_pred2tree (const noll_pred_t * pred)
{
  noll_tree_t *t = noll_vector_at (pred2tree_array, pred->pid);
  if (t != NULL)
    return t;

  NOLL_DEBUG ("\nBuild the tree of the predicate matrix\n");
  /*
   * To create the tree, we need the homomorphism mapping 
   * the i-th argument to a node in the graph.
   * Because the formal args are in the gp->lvars, starting with null,
   * then with first arg, etc., we add +1 to index of arg.
   */
  noll_uid_array *hid = noll_uid_array_new ();
  /* push node of the first arg */
  noll_uid_array_push (hid,
                       noll_vector_at (pred2graph_array,
                                       pred->pid)->var2node[1]);
  /* push node of the second arg */
  noll_uid_array_push (hid,
                       noll_vector_at (pred2graph_array,
                                       pred->pid)->var2node[2]);
  /* push nodes for border args */
  for (size_t i = 2; i < pred->def->fargs; i++)
    noll_uid_array_push (hid,
                         noll_vector_at (pred2graph_array,
                                         pred->pid)->var2node[i + 1]);
  /* create the TA for this graph */
  t = noll_graph2ta (noll_vector_at (pred2graph_array, pred->pid), hid);
#ifndef NDEBUG
  fprintf (stdout, "\n- tree of matrix\n");
  noll_tree_fprint (stdout, t);
  fflush (stdout);
#endif

  /* save it for a possible reuse */
  NOLL_VECTOR_ARRAY (pred2tree_array)[pred->pid] = t;
  return t;
}
