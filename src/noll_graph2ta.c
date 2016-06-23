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
 */

#include <limits.h>

#include "noll.h"
#include "noll_graph2ta.h"
#include "noll_preds.h"
#include "noll_ta_symbols.h"
#include "noll_tree.h"
#include "noll_vector.h"

/* ====================================================================== */
/* Data types */
/* ====================================================================== */

// a list of markings (associated to very node)
NOLL_VECTOR_DECLARE (noll_marking_list, noll_uid_array *)
NOLL_VECTOR_DEFINE (noll_marking_list, noll_uid_array *)
// mapping of nodes to lists of paths
  NOLL_VECTOR_DECLARE (noll_nodes_to_paths, noll_marking_list *)
NOLL_VECTOR_DEFINE (noll_nodes_to_paths, noll_marking_list *)
/* ====================================================================== */
/* Macros */
/* ====================================================================== */
#define MIN(x, y) (((x) > (y))? (y) : (x))
/* ====================================================================== */
/* Globals */
/* ====================================================================== */
     static size_t noll_unique_cnt = 10000;

     static size_t noll_get_unique (void)
{
  assert (noll_unique_cnt < SSIZE_MAX);

  return noll_unique_cnt++;
}


/* ====================================================================== */
/* Debugging functions */
/* ====================================================================== */

static void
noll_debug_print_one_mark (const noll_uid_array * mark)
{
  if (NULL == mark)
    {
      NOLL_DEBUG ("NULL");
      return;
    }

  char *str = noll_marking_tostring (mark);
  assert (NULL != str);
  NOLL_DEBUG ("%s", str);
  free (str);
}


/**
 * @brief  Debugging output of markings
 *
 * @param[in]  markings  The markings to be printed
 */
static void
noll_debug_print_markings (const noll_marking_list * markings)
{
  assert (NULL != markings);

  for (size_t j = 0; j < noll_vector_size (markings); ++j)
    {
      const noll_uid_array *mark = noll_vector_at (markings, j);

      NOLL_DEBUG ("Node %zu: ", j);
      if (NULL == mark)
        {
          NOLL_DEBUG ("empty");
        }
      else
        {
          noll_debug_print_one_mark (mark);
        }
      NOLL_DEBUG ("\n");
    }
}


/* ====================================================================== */
/* Auxiliary functions */
/* ====================================================================== */


/**
 * @brief  Determines the longest common prefix of a pair of markings
 *
 * @param[in]  lhs  The first marking
 * @param[in]  rhs  The other marking
 *
 * @returns  The longest common prefix of @p lhs and @p rhs. The caller is
 *           responsible for the deallocation of the returned structure.
 */
static noll_uid_array *
noll_longest_common_prefix (const noll_uid_array * lhs,
                            const noll_uid_array * rhs)
{
  assert (NULL != lhs);
  assert (NULL != rhs);

  noll_uid_array *lcp = noll_uid_array_new ();
  assert (NULL != lcp);

  size_t size_shorter = MIN (noll_vector_size (lhs), noll_vector_size (rhs));

  for (size_t i = 0; i < size_shorter; ++i)
    {
      if (noll_vector_at (lhs, i) != noll_vector_at (rhs, i))
        {
          break;
        }

      noll_uid_array_push (lcp, noll_vector_at (lhs, i));
    }

  return lcp;
}


/**
 * @brief  Does the array contain the given element?
 *
 * Checks for the presence of the element @p elem in the (unordered) array @p
 * arr.
 *
 * @param[in]  arr   The array to check
 * @param[in]  elem  The element to check for
 *
 * @returns  @p true iff @p arr contains @p elem, @p false otherwise
 */
static bool
noll_uid_array_contains (const noll_uid_array * arr, uid_t elem)
{
  assert (NULL != arr);

  for (size_t i = 0; i < noll_vector_size (arr); ++i)
    {
      if (noll_vector_at (arr, i) == elem)
        {
          return true;
        }
    }

  return false;
}


/**
 * @brief  Implementation of the <= relation over record fields
 *
 * @param[in]  lhs  The left hand side field
 * @param[in]  rhs  The right hand side field
 *
 * @returns  @p true iff lhs < rhs w.r.t. the field ordering, @p false
 *           otherwise
 */
static bool
noll_fields_order_lt (uid_t lhs, uid_t rhs)
{
  if (NOLL_MARKINGS_EPSILON == lhs)
    {
      return true;
    }

  if (NOLL_MARKINGS_EPSILON == rhs)
    {
      return false;
    }

  if (lhs == rhs)
    {                           // noll_field_lt does not allow lhs == rhs
      return false;
    }

  /* NOLL_DEBUG("Calling noll_field_lt() with %u and %u\n", lhs, rhs); */
  return noll_field_lt (lhs, rhs);
}


static bool
noll_fields_is_main_backbone (uid_t field)
{
  return noll_pred_is_main_backbone_field (field);
}


/**
 * @brief  The lexicographic ordering on markings
 *
 * @param[in]  lhs  The left-hand side
 * @param[in]  rhs  The left-hand side
 *
 * @returns  @p true iff lhs < rhs lexicographically, @p false otherwise
 */
static bool
noll_marking_lexico_lt (const noll_uid_array * lhs,
                        const noll_uid_array * rhs)
{
  assert (NULL != lhs);
  assert (NULL != rhs);

  assert (0 < noll_vector_size (lhs));
  assert (0 < noll_vector_size (rhs));

  assert (NOLL_MARKINGS_EPSILON == noll_vector_first (lhs));
  assert (NOLL_MARKINGS_EPSILON == noll_vector_first (rhs));

  size_t limit = MIN (noll_vector_size (lhs), noll_vector_size (rhs));
  for (size_t i = 1; i < limit; ++i)
    {
      if (noll_fields_order_lt
          (noll_vector_at (lhs, i), noll_vector_at (rhs, i)))
        {
          return true;
        }
      else if (noll_vector_at (lhs, i) == noll_vector_at (rhs, i))
        {
          // just continue to next iteration
        }
      else
        {
          return false;
        }
    }

  NOLL_DEBUG (__func__);
  NOLL_DEBUG (": treating lexical ordering as strict\n");

  return noll_vector_size (lhs) < noll_vector_size (rhs);
}


/**
 * @brief  Implementation of the <= relation over nodes' markings
 *
 * @param[in]  lhs  The left hand side marking
 * @param[in]  rhs  The right hand side marking
 *
 * @returns  @p true iff lhs <= rhs w.r.t. the marking ordering, @p false
 *           otherwise
 */
static bool
noll_marking_order_lt (const noll_uid_array * lhs, const noll_uid_array * rhs)
{
  assert (NULL != lhs);
  assert (NULL != rhs);

  assert (!noll_vector_empty (lhs));
  assert (!noll_vector_empty (rhs));
  assert (NOLL_MARKINGS_EPSILON == noll_vector_first (lhs));
  assert (NOLL_MARKINGS_EPSILON == noll_vector_first (rhs));

  NOLL_DEBUG ("Checking whether ");
  noll_debug_print_one_mark (lhs);
  NOLL_DEBUG (" < ");
  noll_debug_print_one_mark (rhs);
  NOLL_DEBUG (": ");

  if ((1 == noll_vector_size (lhs)) && (2 <= noll_vector_size (rhs)))
    {                           // lhs = e != rhs
      NOLL_DEBUG ("true 1\n");
      return true;
    }

  if ((2 <= noll_vector_size (lhs)) && (2 <= noll_vector_size (rhs)))
    {                           // lhs != e != rhs
      if (noll_fields_order_lt
          (noll_vector_last (lhs), noll_vector_last (rhs)))
        {                       // last(lhs) < last(rhs)
          NOLL_DEBUG ("true 2\n");
          return true;
        }

      if (noll_marking_lexico_lt (lhs, rhs))
        {                       // lhs < rhs (lexicographically)
          NOLL_DEBUG ("true 3\n");
          return true;
        }
    }

  NOLL_DEBUG ("false\n");
  return false;
}


/**
 * @brief  The "marking is a prefix or equal" predicate
 *
 * This binary predicate holds true iff @p pred is a prefix (not necessarily
 * proper) of @p succ.
 *
 * @param[in]  pred  The potential predecessor
 * @param[in]  succ  The potential successor
 *
 * @returns  @p true iff @p pred is a prefix of @p succ
 */
static bool
noll_marking_is_prefix_or_equal (const noll_uid_array * pred,
                                 const noll_uid_array * succ)
{
  // check for sanity of the inputs
  assert (NULL != pred);
  assert (NULL != succ);

  if (noll_vector_size (pred) > noll_vector_size (succ))
    {                           // if the lengths are wrong
      return false;
    }

  for (size_t i = 0; i < noll_vector_size (pred); ++i)
    {                           // check that 'succ' is the same as 'pred' up to the length of 'pred'
      if (noll_vector_at (pred, i) != noll_vector_at (succ, i))
        {
          return false;
        }
    }

  return true;
}


/**
 * @brief  Updates the marking of a node
 *
 * Updates the marking of @p node according to the marking of the node @p src
 * according to the @p edge_lab. The markings are stored in @p markings_list.
 * Returns @p true if something has been changed, @p false otherwise.
 *
 * @param[in]      node           The node to have updated marking
 * @param[in]      src            The source according to which the marking to
 *                                be computed
 * @param[in]      edge_lab       The label to update the marking with
 * @param[in,out]  markings_list  The list of markings
 *
 * @returns  @p true if the marking has changed, @p false otherwise
 */
static bool
update_marking_from (uint_t node,
                     uint_t src,
                     uid_t edge_lab, noll_nodes_to_paths * markings_list)
{
  assert (NULL != markings_list);
  assert (noll_vector_size (markings_list) > src);
  assert (noll_vector_size (markings_list) > node);

  bool changed = false;

  NOLL_DEBUG ("Updating the marking of %u \"", node);
  NOLL_DEBUG ("{");
  for (size_t j = 0;
       j < noll_vector_size (noll_vector_at (markings_list, node)); ++j)
    {
      noll_debug_print_one_mark (noll_vector_at
                                 (noll_vector_at (markings_list, node), j));
      NOLL_DEBUG (", ");
    }
  NOLL_DEBUG ("}");
  NOLL_DEBUG ("\" from the marking of %u \"", src);
  NOLL_DEBUG ("{");
  for (size_t j = 0;
       j < noll_vector_size (noll_vector_at (markings_list, src)); ++j)
    {
      noll_debug_print_one_mark (noll_vector_at
                                 (noll_vector_at (markings_list, src), j));
      NOLL_DEBUG (", ");
    }
  NOLL_DEBUG ("}");
  NOLL_DEBUG ("\" over %s.\n", noll_field_name (edge_lab));

  // get markings of the source and destination nodes
  const noll_marking_list *src_markings = noll_vector_at (markings_list, src);
  noll_marking_list *node_markings = noll_vector_at (markings_list, node);
  for (size_t j = 0; j < noll_vector_size (src_markings); ++j)
    {
      noll_uid_array *new_marking = noll_uid_array_new ();
      noll_uid_array_copy (new_marking, noll_vector_at (src_markings, j));
      assert (0 < noll_vector_size (new_marking));
      /* if ((noll_vector_last(new_marking) == edge_lab) */
      /*      && noll_fields_is_main_backbone(edge_lab)) */
      /* { */
      /*      // we keep the same marking */
      /* } */
      /* else if (noll_fields_order_lt(noll_vector_last(new_marking), edge_lab)) */
      /* { */
      // we add the field at the end of the marking
      noll_uid_array_push (new_marking, edge_lab);
      /* } */
      /* else */
      /* {    // in the case the 'edge_lab' is greater than the last of */
      /*      // new_marking, this marking will surely be removed so we do not need */
      /*      // to add it */
      /*      noll_uid_array_delete(new_marking); */
      /*      continue; */
      /* } */

      bool found = false;
      for (size_t k = 0; k < noll_vector_size (node_markings); ++k)
        {                       // check whether the marking is not already there
          const noll_uid_array *dst_mark = noll_vector_at (node_markings, k);
          assert (NULL != dst_mark);
          if (noll_uid_array_equal (new_marking, dst_mark))
            {
              found = true;
              break;
            }
        }

      if (!found)
        {
          changed = true;
          noll_marking_list_push (node_markings, new_marking);
        }
      else
        {
          noll_uid_array_delete (new_marking);
        }
    }

  if (changed)
    {
      NOLL_DEBUG ("Changed markings to\n");
      // print the computed markings
      for (size_t i = 0; i < noll_vector_size (markings_list); ++i)
        {
          const noll_marking_list *list = noll_vector_at (markings_list, i);
          assert (NULL != list);
          NOLL_DEBUG ("Node %zu: {", i);
          for (size_t j = 0; j < noll_vector_size (list); ++j)
            {
              noll_debug_print_one_mark (noll_vector_at (list, j));
              NOLL_DEBUG (", ");
            }
          NOLL_DEBUG ("}\n");
        }
    }

  return changed;
}


/// TODO
static void
rec_compute_paths (uint_t node,
                   const noll_graph_t * graph,
                   noll_uid_array * workstack,
                   noll_nodes_to_paths * nodes_to_paths)
{
  assert (NULL != graph);
  assert (node < graph->nodes_size);
  assert (NULL != workstack);
  assert (NULL != nodes_to_paths);
  assert (noll_vector_size (nodes_to_paths) == graph->nodes_size);
  assert (noll_vector_size (workstack) > 0);

  const noll_uid_array *edges_from_node = graph->mat[node];
  if (NULL == edges_from_node)
    {                           // in the case 'node' has no outgoing edges
      return;
    }

  for (size_t i = 0; i < noll_vector_size (edges_from_node); ++i)
    {
      uid_t edge_id = noll_vector_at (edges_from_node, i);
      NOLL_DEBUG ("Found edge %u\n", edge_id);

      const noll_edge_t *ed = noll_vector_at (graph->edges, edge_id);
      assert (NULL != ed);
      assert (2 <= noll_vector_size (ed->args));
      NOLL_DEBUG ("  src = %u\n", noll_vector_at (ed->args, 0));
      NOLL_DEBUG ("  dst = %u\n", noll_vector_at (ed->args, 1));
      assert (noll_vector_at (ed->args, 0) == node);
      uid_t post_node = noll_vector_at (ed->args, 1);
      assert (post_node < graph->nodes_size);
      if (!noll_uid_array_contains (workstack, post_node))
        {                       // if 'post_node' is not already on this path from initial node (this
          // would create a cycle), call recursively
          uid_t edge_lab;
          if (NOLL_EDGE_PTO == ed->kind)
            {                   // for points-to edges
              edge_lab = ed->label;
            }
          else
            {                   // for higher-order predicate edges
              assert (NOLL_EDGE_PRED == ed->kind);
              edge_lab = noll_pred_get_minfield (ed->label);
            }

          noll_uid_array_push (workstack, post_node);
          update_marking_from (post_node, node, edge_lab, nodes_to_paths);
          rec_compute_paths (post_node, graph, workstack, nodes_to_paths);
          assert (!noll_vector_empty (workstack)
                  && (noll_vector_last (workstack) == post_node));
          noll_uid_array_pop (workstack);
          assert (!noll_vector_empty (workstack)
                  && (noll_vector_last (workstack) == node));
        }
    }
}


/**
 * @brief  Computes simple paths to nodes of graphs
 *
 * Given a @p graph, this function computes all simple paths from @p initial_node to all nodes
 * of @p graph, which is stored into @p paths.
 *
 * @param[in]   graph           The input graph
 * @param[in]   initial_node    The initial node of @p graph
 * @param[out]  nodes_to_paths  The computed paths
 */
static void
compute_simple_paths (const noll_graph_t * graph,
                      uint_t initial_node,
                      noll_nodes_to_paths * nodes_to_paths)
{
  assert (NULL != graph);
  assert (initial_node < graph->nodes_size);
  assert (NULL != nodes_to_paths);

  noll_nodes_to_paths_resize (nodes_to_paths, graph->nodes_size);       // resize should allocate enough mem
  for (size_t i = 0; i < noll_vector_size (nodes_to_paths); ++i)
    {                           // we allocate empty list of markings for every node now
      noll_vector_at (nodes_to_paths, i) = noll_marking_list_new ();
      assert (NULL != noll_vector_at (nodes_to_paths, i));
    }

  NOLL_DEBUG ("Computing simple paths of nodes of the graph\n");

  // initialize the marking of the initial node to be 'epsilon'
  // TODO: the NOLL_MARKINGS_EPSILON symbol is useless here, but it makes some
  // things easier (such as that *_last() will not fail)
  noll_uid_array *epsilon_marking = noll_uid_array_new ();
  assert (NULL != epsilon_marking);
  noll_uid_array_push (epsilon_marking, NOLL_MARKINGS_EPSILON);
  noll_marking_list *initial_node_markings =
    noll_vector_at (nodes_to_paths, initial_node);
  assert (NULL != initial_node_markings);
  noll_marking_list_push (initial_node_markings, epsilon_marking);

  // now, we start a DFS
  noll_uid_array *workstack = noll_uid_array_new ();
  assert (NULL != workstack);
  noll_uid_array_push (workstack, initial_node);

  rec_compute_paths (initial_node, graph, workstack, nodes_to_paths);
}

/**
 * @brief  Computes markings of nodes of a graph
 *
 * Given a @p graph, this function computes the minimum marker for every node
 * of @p graph, which is stored into @p markings.
 *
 * @param[in]   graph         The input graph
 * @param[in]   initial_node  The initial node of @p graph
 * @param[out]  markings      The computed markings
 */
static void
compute_markings (const noll_graph_t * graph,
                  uint_t initial_node, noll_marking_list * markings)
{
  assert (NULL != graph);
  assert (NULL != markings);
  assert (initial_node < graph->nodes_size);

  noll_nodes_to_paths *nodes_to_paths = noll_nodes_to_paths_new ();
  assert (NULL != nodes_to_paths);
  compute_simple_paths (graph, initial_node, nodes_to_paths);

  size_t num_nodes = graph->nodes_size;
  assert (0 < num_nodes);
  noll_marking_list_resize (markings, num_nodes);

  NOLL_DEBUG ("Paths of nodes of the graph computed\n");
  NOLL_DEBUG ("Paths:\n");

  // print the computed markings
  for (size_t i = 0; i < noll_vector_size (nodes_to_paths); ++i)
    {
      const noll_marking_list *list = noll_vector_at (nodes_to_paths, i);
      assert (NULL != list);
      NOLL_DEBUG ("Node %zu: {", i);
      for (size_t j = 0; j < noll_vector_size (list); ++j)
        {
          noll_debug_print_one_mark (noll_vector_at (list, j));
          NOLL_DEBUG (", ");
        }
      NOLL_DEBUG ("}\n");
    }

  // compute the least marking for every node
  for (size_t i = 0; i < noll_vector_size (nodes_to_paths); ++i)
    {
      NOLL_DEBUG ("Going over node %zu\n", i);
      const noll_marking_list *list = noll_vector_at (nodes_to_paths, i);
      assert (NULL != list);
      if (0 == noll_vector_size (list))
        {                       // if there is a node with no marking, this means that it is not reachable
          noll_vector_at (markings, i) = NULL;
          continue;
        }

      assert (noll_vector_size (list) > 0);
      noll_uid_array **ptr_least_marking = &noll_vector_at (list, 0);
      assert (NULL != ptr_least_marking);
      assert (NULL != *ptr_least_marking);
      for (size_t j = 1; j < noll_vector_size (list); ++j)
        {
          noll_uid_array **mark = &noll_vector_at (list, j);
          assert (NULL != mark);
          assert (NULL != *mark);
          if (noll_marking_order_lt (*mark, *ptr_least_marking))
            {
              ptr_least_marking = mark;
            }
        }

      noll_vector_at (markings, i) = *ptr_least_marking;
      *ptr_least_marking = NULL;
    }

  NOLL_DEBUG ("Before killing\n");
  // print the computed markings
  for (size_t i = 0; i < noll_vector_size (nodes_to_paths); ++i)
    {
      const noll_marking_list *list = noll_vector_at (nodes_to_paths, i);
      assert (NULL != list);
      NOLL_DEBUG ("Node %zu: {", i);
      for (size_t j = 0; j < noll_vector_size (list); ++j)
        {
          noll_debug_print_one_mark (noll_vector_at (list, j));
          NOLL_DEBUG (", ");
        }
      NOLL_DEBUG ("}\n");
    }

  // delete markings
  for (size_t i = 0; i < noll_vector_size (nodes_to_paths); ++i)
    {                           // we allocate empty markings for every node now
      noll_marking_list *list = noll_vector_at (nodes_to_paths, i);
      assert (NULL != list);
      for (size_t j = 0; j < noll_vector_size (list); ++j)
        {
          if (NULL != noll_vector_at (list, j))
            {
              noll_uid_array_delete (noll_vector_at (list, j));
            }
        }
      noll_marking_list_delete (list);
    }
  noll_nodes_to_paths_delete (nodes_to_paths);

  // as the last step, remove duplicities from the paths to obtain real markings
  for (size_t i = 0; i < noll_vector_size (markings); ++i)
    {
      noll_uid_array *mark = noll_vector_at (markings, i);
      if (NULL != mark)
        {                       // if there is some marking
          size_t l = 0;
          for (size_t k = 1; k < noll_vector_size (mark); ++k)
            {
              if (noll_vector_at (mark, k) != noll_vector_at (mark, l))
                {               // if the fields differ
                  ++l;
                  noll_vector_at (mark, l) = noll_vector_at (mark, k);
                }
            }

          noll_uid_array_resize (mark, l + 1);
        }
    }
}


/**
 * @brief  Checks whether a marking corresponds to a successor of another one
 *
 * This function checks that the marking @p node_marking of some node @p n can
 * be achieved by extending the marking @p pred_marking of its predecessor @p p
 * with the symbol @p symbol. This is used to check whether @p symbol denotes
 * the @p backbone edge from @p n to @p p.
 *
 * @param[in]  node_marking  Marking of node @p n
 * @param[in]  pred_marking  Marking of node @p p
 * @param[in]  symbol        The symbol of the edge between @p p and @p n
 *
 * @returns  @p true if @p node_marking is the successor of @p prev_marking
 *           over the edge labelled with @p symbol
 */
static bool
noll_marking_is_succ_of_via (const noll_uid_array * node_marking,
                             const noll_uid_array * pred_marking,
                             uid_t symbol)
{
  // check whether the parameters are sane
  assert (NULL != node_marking);
  assert (NULL != pred_marking);
  assert (0 != noll_vector_size (node_marking));
  assert (0 != noll_vector_size (pred_marking));

  NOLL_DEBUG ("Testing whether marking ");
  noll_debug_print_one_mark (node_marking);
  NOLL_DEBUG (" is a successor of ");
  noll_debug_print_one_mark (pred_marking);
  NOLL_DEBUG (" via %s: ", noll_field_name (symbol));

  if (noll_vector_last (node_marking) != symbol)
    {                           // in the case the last symbol of the marking is not the checked symbol
      NOLL_DEBUG ("false\n");
      return false;
    }

  int diff =
    noll_vector_size (node_marking) - noll_vector_size (pred_marking);
  if ((0 != diff) && (1 != diff))
    {                           // if the backboneness is impossible
      NOLL_DEBUG ("false\n");
      return false;
    }

  for (size_t i = 0; i < noll_vector_size (pred_marking); ++i)
    {
      if (noll_vector_at (pred_marking, i) !=
          noll_vector_at (node_marking, i))
        {                       // in the case there is a mismatch
          NOLL_DEBUG ("false\n");
          return false;
        }
    }

  NOLL_DEBUG ("true\n");
  return true;
}


/**
 * @brief  A function checking that node @p dst is reachable from node @p src
 *
 * This function checks whether the node @p dst is reachable from the node @p
 * src in the @p graph along a path where the marker @p mark is not used (while
 * not including @p dst to this check).
 *
 * @param[in]  graph     The graph
 * @param[in]  markings  The markings of nodes of @p graph
 * @param[in]  dst       The destination node
 * @param[in]  src       The source node
 * @param[in]  mark      The marking to be checked for
 *
 * @returns  @p true iff @p dst is reachable from @p src on a path without @p
 *           mark
 */
static bool
reachable_from_through_path_wo_marker (const noll_graph_t * graph,
                                       const noll_marking_list * markings,
                                       uid_t dst,
                                       uid_t src, const noll_uid_array * mark)
{
  assert (NULL != graph);
  assert (NULL != mark);
  assert (src < graph->nodes_size);
  assert (dst < graph->nodes_size);

  noll_uid_array *workstack = noll_uid_array_new ();
  assert (NULL != workstack);

  // an ordinary array for processed nodes
  noll_uid_array *processed = noll_uid_array_new ();
  assert (NULL != processed);

  noll_uid_array_push (workstack, src);

  bool found_dst = false;
  while (!noll_vector_empty (workstack) && !found_dst)
    {
      uid_t node = noll_vector_last (workstack);
      noll_uid_array_pop (workstack);
      assert (node < graph->nodes_size);
      assert (!noll_uid_array_contains (processed, node));
      noll_uid_array_push (processed, node);

      const noll_uid_array *edges_from_node = graph->mat[node];
      if (NULL == edges_from_node)
        {                       // in the case 'node' has no outgoing edges
          continue;
        }

      for (size_t i = 0; i < noll_vector_size (edges_from_node); ++i)
        {
          uid_t edge_id = noll_vector_at (edges_from_node, i);
          NOLL_DEBUG ("Found edge %u\n", edge_id);

          const noll_edge_t *ed = noll_vector_at (graph->edges, edge_id);
          assert (NULL != ed);
          assert (2 <= noll_vector_size (ed->args));
          NOLL_DEBUG ("  src = %u\n", noll_vector_at (ed->args, 0));
          NOLL_DEBUG ("  dst = %u\n", noll_vector_at (ed->args, 1));
          assert (noll_vector_at (ed->args, 0) == node);
          uid_t post_node = noll_vector_at (ed->args, 1);

          if (post_node == dst)
            {                   // if we found the destination
              found_dst = true;
              break;
            }

          if (noll_uid_array_equal
              (noll_vector_at (markings, post_node), mark))
            {                   // if we hit 'mark', do not expand
              continue;
            }

          if (!noll_uid_array_contains (processed, post_node) &&
              !noll_uid_array_contains (workstack, post_node))
            {                   // if it has sense to add 'post_node' to processing
              noll_uid_array_push (workstack, post_node);
            }
        }
    }
  noll_uid_array_delete (workstack);
  noll_uid_array_delete (processed);

  return found_dst;
}


/**
 * @brief  Finds the first ancestor of a node with a given marking
 *
 * Finds the first ancestor of @p node in @p graph that has the given @p
 * marking. Markings are passed in the @p marking_list.
 *
 * @param[in]  node          The starting node (for which we wish to find the ancestor)
 * @param[in]  marking       The marking we are looking for
 * @param[in]  graph         The graph
 * @param[in]  marking_list  List of all markings of nodes (addressed by the node number)
 *
 * @returns  The first ancestor of @p node with the given @p marking
 */
static uid_t
find_first_ancestor_with_marking (uid_t node,
                                  const noll_uid_array * marking,
                                  const noll_graph_t * graph,
                                  const noll_marking_list * marking_list)
{
  assert (NULL != marking);
  assert (NULL != graph);
  assert (NULL != marking_list);
  assert (node < graph->nodes_size);
  assert (noll_vector_size (marking_list) == graph->nodes_size);

  uid_t parent_node = node;
  const noll_uid_array *parent_node_mark =
    noll_vector_at (marking_list, parent_node);
  while (!noll_uid_array_equal (marking, parent_node_mark))
    {
      const noll_uid_array *rev_edges = graph->rmat[parent_node];
      assert (NULL != rev_edges);

      NOLL_DEBUG ("Node %u, parent edges: %u\n", parent_node,
                  noll_vector_size (rev_edges));

      uid_t parent_edge_id = (uid_t) - 1;
      const noll_edge_t *parent_edge = NULL;
      // now, we pick the main backbone parent edge
      for (size_t rev_i = 0; rev_i < noll_vector_size (rev_edges); ++rev_i)
        {
          uid_t rev_edge_id = noll_vector_at (rev_edges, rev_i);
          const noll_edge_t *edge_candid =
            noll_vector_at (graph->edges, rev_edge_id);
          assert (NULL != edge_candid);

          uid_t edge_symbol = (uid_t) - 1;
          if (NOLL_EDGE_PTO == edge_candid->kind)
            {
              edge_symbol = edge_candid->label;
            }
          else if (NOLL_EDGE_PRED == edge_candid->kind)
            {
              edge_symbol = noll_pred_get_minfield (edge_candid->label);
            }
          else
            {
              NOLL_DEBUG ("ERROR: Unsupported edge type\n");
              assert (false);
            }

          assert ((uid_t) - 1 != edge_symbol);

          if ((uid_t) - 1 == parent_edge_id)
            {
              assert (0 == rev_i);
              parent_edge_id = rev_edge_id;
              parent_edge = edge_candid;
              continue;
            }

          assert (NULL != parent_edge);
          if (noll_field_lt (edge_symbol, parent_edge->label))
            {
              parent_edge_id = rev_edge_id;
              parent_edge = edge_candid;
            }
        }

      assert ((uid_t) - 1 != parent_edge_id);
      assert (NULL != parent_edge);

      // move a level up
      assert (NULL != parent_edge->args);
      parent_node = noll_vector_at (parent_edge->args, 0);
      parent_node_mark = noll_vector_at (marking_list, parent_node);
    }

  return parent_node;
}


/**
 * @brief  Checks whether a node is the first successor of a node with given marking
 *
 * This function checks whether the node @p dst is the first successor of the
 * node @p src with the given @p marking in the given @p graph. The markings of
 * nodes of @p graph are given in @p marking_list.
 *
 * @param[in]  dst           The target node
 * @param[in]  src           The source node
 * @param[in]  marking       The marking to be checked
 * @param[in]  graph         The considered graph
 * @param[in]  marking_list  The list of markings (addressed by the node number)
 *
 * @returns  @p true iff @p dst is the first successor of @p src with the given
 *           @p marking
 */
static bool
is_the_first_successor_of_with_marking (uid_t dst,
                                        uid_t src,
                                        const noll_uid_array * marking,
                                        const noll_graph_t * graph,
                                        const noll_marking_list *
                                        marking_list)
{
  assert (NULL != marking);
  assert (NULL != graph);
  assert (NULL != marking_list);
  assert (dst < graph->nodes_size);
  assert (src < graph->nodes_size);
  assert (noll_vector_size (marking_list) == graph->nodes_size);
  assert (noll_uid_array_equal (marking, noll_vector_at (marking_list, dst)));

  if (dst != dst)
    return false; /* to remove warning on unused parameter */

  const noll_uid_array *src_marking = noll_vector_at (marking_list, src);
  assert (NULL != src_marking);

  NOLL_DEBUG
    ("Checking whether %d is the first successor of %d with the marking ",
     dst, src);
  noll_debug_print_one_mark (marking);
  NOLL_DEBUG ("\n");

  NOLL_DEBUG (__func__);
  NOLL_DEBUG (": approximating the result for depth 1\n");

  // TODO: this is only temporary, and checks that 'next_child' is the
  // successor of 'proc_node' over some field
  if ((noll_vector_size (src_marking) + 1 < noll_vector_size (marking)) ||
      (noll_vector_size (src_marking) > noll_vector_size (marking)))
    {
      NOLL_DEBUG ("WARNING: ");
      NOLL_DEBUG (__func__);
      NOLL_DEBUG (": soundly approximating to FALSE for a strange marking\n");
      return false;
    }

  uint_t continuation_field = noll_vector_last (marking);

  const noll_uid_array *mat_src = graph->mat[src];
  assert (NULL != mat_src);
  for (size_t mat_src_i = 0;
       mat_src_i < noll_vector_size (mat_src); ++mat_src_i)
    {
      uint_t par_edge_id = noll_vector_at (mat_src, mat_src_i);
      assert (par_edge_id < noll_vector_size (graph->edges));

      const noll_edge_t *edge_from_par =
        noll_vector_at (graph->edges, par_edge_id);
      assert (NULL != edge_from_par);
      assert (NOLL_EDGE_PTO == edge_from_par->kind);

      if (edge_from_par->label == continuation_field)
        {
          return true;
        }
    }

  return false;
}


/**
 * @brief  Checks whether a node is the last successor of a node with given marking
 *
 * This function checks whether the node @p dst is the last successor of the
 * node @p src with the given @p marking in the given @p graph. The markings of
 * nodes of @p graph are given in @p marking_list.
 *
 * @param[in]  dst           The target node
 * @param[in]  src           The source node
 * @param[in]  marking       The marking to be checked
 * @param[in]  graph         The considered graph
 * @param[in]  marking_list  The list of markings (addressed by the node number)
 *
 * @returns  @p true iff @p dst is the last successor of @p src with the given
 *           @p marking
 */
static bool
is_the_last_successor_of_with_marking (uid_t dst,
                                       uid_t src,
                                       const noll_uid_array * marking,
                                       const noll_graph_t * graph,
                                       const noll_marking_list * marking_list)
{
  assert (NULL != marking);
  assert (NULL != graph);
  assert (NULL != marking_list);
  assert (dst < graph->nodes_size);
  assert (src < graph->nodes_size);
  assert (noll_vector_size (marking_list) == graph->nodes_size);
  assert (noll_uid_array_equal (marking, noll_vector_at (marking_list, dst)));

  if ((dst != dst) ||
      (src != src) ||
      (marking != marking) ||
      (graph != graph) ||
      (marking_list != marking_list))
    return false; /* to remove warning on unused parameter */

  NOLL_DEBUG ("WARNING: ");
  NOLL_DEBUG (__func__);
  NOLL_DEBUG (": unimplemented - soundly approximating to FALSE\n");

  return false;
}


/**
 * @brief  Retrieves marking symbol for a node w.r.t. a given base node
 *
 * @param[in]  node       The target node we wish to represent using a marking
 * @param[in]  base_node  The @em base node w.r.t. which we wish to compute the
 *                        marking of @p node
 * @param[in]  graph      The graph in which we are operating
 * @param[in]  vars       List of variables
 * @param[in]  markings   Markings of nodes
 *
 * @returns  The symbol representing the alias marking if it is expressible in
 *           the framework, @p NULL otherwise
 *
 */
static const noll_ta_symbol_t *
get_marking_symbol_of_node_wrt_base (uint_t node,
                                     uint_t base_node,
                                     const noll_graph_t * graph,
                                     const noll_uid_array * vars,
                                     const noll_marking_list * markings)
{
  assert (NULL != graph);
  assert (graph->nodes_size > node);
  assert (graph->nodes_size > base_node);
  assert (NULL != vars);
  assert (NULL != markings);
  assert (noll_vector_size (markings) == graph->nodes_size);

  if (noll_uid_array_contains (vars, node))
    {                           // if next_child is pointed by a variable
      NOLL_DEBUG ("Detected aliasing of variable (node) %u\n", node);

      // now, we create the corresponding symbol
      const noll_ta_symbol_t *leaf_symbol =
        noll_ta_symbol_get_unique_aliased_var (node);
      assert (NULL != leaf_symbol);

      return leaf_symbol;
    }

  const noll_uid_array *mark_node = noll_vector_at (markings, node);
  assert (NULL != mark_node);
  const noll_uid_array *mark_base = noll_vector_at (markings, base_node);
  assert (NULL != mark_base);

  if (noll_marking_is_prefix_or_equal (mark_node, mark_base))
    {                           // in the case the source is a predecessor of the target (this is the
      // case e.g. for a doubly-linked segment)
      NOLL_DEBUG ("The source ");
      noll_debug_print_one_mark (mark_node);
      NOLL_DEBUG (" is a PREFIX of the target ");
      noll_debug_print_one_mark (mark_base);
      NOLL_DEBUG ("\n");

      NOLL_DEBUG
        ("Now, we check whether node %u is reachable from node %u on a path that does not use the marking ",
         base_node, node);
      noll_debug_print_one_mark (mark_node);
      NOLL_DEBUG ("\n");

      // TODO: first test marking, then the reachability
      if (reachable_from_through_path_wo_marker
          (graph, markings, base_node, node, mark_node))
        {                       // in case 'base_node' is reachable from 'node' via a path where the
          // marker '\mu(n)' is not used
          NOLL_DEBUG ("  reachable\n");
          if (!noll_uid_array_equal (mark_node, mark_base))
            {                   // in case $\mu(n') != \mu(n)$, mark the leaf with 's1(\mu(n))'
              NOLL_DEBUG ("Detected an s1() marker\n");

              // now, we create the corresponding symbol
              const noll_ta_symbol_t *leaf_symbol =
                noll_ta_symbol_get_unique_aliased_marking_up (mark_node);
              assert (NULL != leaf_symbol);

              return leaf_symbol;
            }
          else
            {                   // in case $\mu(n') = \mu(n)$, mark the leaf with 's2(\mu(n))'
              NOLL_DEBUG ("Detected an s2() marker\n");

              // now, we create the corresponding symbol
              const noll_ta_symbol_t *leaf_symbol =
                noll_ta_symbol_get_unique_aliased_marking_up_up (mark_node);
              assert (NULL != leaf_symbol);
              return leaf_symbol;
            }
        }
      else
        {
          NOLL_DEBUG ("  unreachable\n");
        }
    }

  NOLL_DEBUG ("The source ");
  noll_debug_print_one_mark (mark_node);
  NOLL_DEBUG (" is NOT a PREFIX of the target ");
  noll_debug_print_one_mark (mark_base);
  NOLL_DEBUG ("\n");

  // get the longest prefix
  noll_uid_array *lcp = noll_longest_common_prefix (mark_node, mark_base);
  assert (NULL != lcp);
  assert (!noll_vector_empty (lcp));

  NOLL_DEBUG ("Their longest common prefix is ");
  noll_debug_print_one_mark (lcp);
  NOLL_DEBUG ("\n");

  // here, we find the first parent of 'i' that has the marking 'lcp'
  uid_t parent_node = find_first_ancestor_with_marking (
                                                         /* node */ base_node,
                                                         /* found marking */
                                                         lcp,
                                                         /* graph */ graph,
                                                         /* list of markings */
                                                         markings);
  assert (parent_node < graph->nodes_size);
  noll_uid_array_delete (lcp);

  // now, we need to check that which successor of 'parent_node' 'next_child' is
  // TODO: implement checking of other than the s3 marker
  if (is_the_first_successor_of_with_marking (node,
                                              parent_node,
                                              mark_node, graph, markings))
    {
      NOLL_DEBUG ("Detected an s3() marker\n");

      // now, we create the corresponding symbol
      const noll_ta_symbol_t *leaf_symbol =
        noll_ta_symbol_get_unique_aliased_marking_up_down_fst (mark_node);
      assert (NULL != leaf_symbol);
      return leaf_symbol;
    }
  else if (is_the_last_successor_of_with_marking (node,
                                                  parent_node,
                                                  mark_node, graph, markings))
    {
      NOLL_DEBUG ("Detected an s4() marker\n");
      NOLL_DEBUG ("ERROR: Unimplemented\n");
      assert (false);
    }
  else
    {
      NOLL_DEBUG ("Could not find a marking!!!\n");
    }
  return NULL;
}


/* ====================================================================== */
/* Translators */
/* ====================================================================== */

/**
 *  Translates g into a tree automaton.
 *  @return TA built or NULL
 */
noll_tree_t *
noll_graph2ta (const noll_graph_t * graph, const noll_uid_array * homo)
{
  // check sanity of input parameters
  assert (NULL != graph);
  assert (NULL != graph->lvars);
  assert (NULL != graph->svars);
  assert (NULL != graph->var2node);
  assert (NULL != graph->edges);
  assert (NULL != homo);
  assert (2 <= noll_vector_size (homo));

  NOLL_DEBUG
    ("********************************************************************************\n");
  NOLL_DEBUG
    ("*                                 GRAPH -> TA                                  *\n");
  NOLL_DEBUG
    ("********************************************************************************\n");

  NOLL_DEBUG ("graph = %p\n", graph);
  NOLL_DEBUG ("number of nodes in graph = %d\n", graph->nodes_size);
  NOLL_DEBUG ("LVars:\n");
  for (size_t i = 0; i < noll_vector_size (graph->lvars); ++i)
    {
      NOLL_DEBUG ("  (*graph->lvars)[%zu] = %p, ", i,
                  noll_vector_at (graph->lvars, i));
      const noll_var_t *var = noll_vector_at (graph->lvars, i);
      assert (NULL != var);
      NOLL_DEBUG ("name = %s, vid = %u, ", var->vname, var->vid);
      NOLL_DEBUG ("points to node -> %u\n", graph->var2node[i]);
    }
  NOLL_DEBUG ("SVars:\n");
  for (size_t i = 0; i < noll_vector_size (graph->svars); ++i)
    {
      NOLL_DEBUG ("  (*graph->svars)[%zu] = %p, ", i,
                  noll_vector_at (graph->svars, i));
      const noll_var_t *var = noll_vector_at (graph->svars, i);
      assert (NULL != var);
      NOLL_DEBUG ("name = %s, vid = %u, \n", var->vname, var->vid);
    }
  NOLL_DEBUG ("Edges:\n");
  for (size_t i = 0; i < noll_vector_size (graph->edges); ++i)
    {
      NOLL_DEBUG ("  (*graph->edges)[%zu] = %p, ", i,
                  noll_vector_at (graph->edges, i));
      const noll_edge_t *edge = noll_vector_at (graph->edges, i);
      assert (NULL != edge);
      NOLL_DEBUG ("from = %u, to = %u, id = %u, kind = %u, label = %u\n",
                  noll_vector_at (edge->args, 0),
                  noll_vector_at (edge->args, 1),
                  edge->id, edge->kind, edge->label);
    }

  NOLL_DEBUG ("The homo morphism:\n");
  NOLL_DEBUG ("  src -> %u\n", noll_vector_at (homo, 0));
  NOLL_DEBUG ("  dst -> %u\n", noll_vector_at (homo, 1));
  for (size_t i = 2; i < noll_vector_size (homo); ++i)
    {
      NOLL_DEBUG ("  param_%zu -> %u\n", i, noll_vector_at (homo, i));
    }


  // Now, we compute for every node 'n' a set of markings 'pi(n)'. These is a
  // least fix point computation.
  uint_t initial_node = noll_vector_at (homo, 0);
  assert (graph->nodes_size > initial_node);

  noll_marking_list *markings = noll_marking_list_new ();
  assert (NULL != markings);
  compute_markings (graph, initial_node, markings);

  NOLL_DEBUG ("Least markings:\n");

  // print the computed markings
  noll_debug_print_markings (markings);

  NOLL_DEBUG ("Generating the tree for the graph\n");
  noll_tree_t* tree = noll_tree_new();
  assert(NULL != tree);

  // set the initial node as the root state
  noll_tree_set_root(tree, initial_node);

  // we transform the graph into a TA representing a tree (i.e. the language of
  // the TA is a singleton set) such that node 'i' is represented by the TA
  // state 'i'
  // the following counter maintains the newly added (leaf) nodes
  uint_t last_leaf = graph->nodes_size;
  for (size_t i = 0; i < graph->nodes_size; ++i)
    {
      const noll_uid_array *edges = graph->mat[i];
      if (NULL == edges)
        {                       // if there are no edges leaving 'i'
          if (noll_uid_array_contains (homo, i))
            {                   // in the case 'i' is a boundary node on some tree branch
              NOLL_DEBUG ("Found a boundary node %zu\n", i);

              const noll_ta_symbol_t *symbol =
                noll_ta_symbol_get_unique_aliased_var (noll_graph_get_var(graph,i));
              noll_tree_create_node(
                tree,        // the tree
                i,           // the node index
                symbol,      // the symbol
                NULL);       // the children
            }
          else
            {
              NOLL_DEBUG
                ("WARNING: found a non-boundary node %zu without output edges\n",
                 i);
            }

          continue;
        }

      noll_uid_array *children = noll_uid_array_new ();
      assert (NULL != children);
      noll_uid_array *selectors = noll_uid_array_new ();
      assert (NULL != selectors);
      noll_uid_array *vars = noll_uid_array_new ();
      assert (NULL != vars);

      if (noll_uid_array_contains (homo, i))
        {                       // in the case 'i' is pointed by a variable
          NOLL_DEBUG ("  adding variable ref %zu\n", i);
          noll_uid_array_push (vars, i);
        }

      const noll_uid_array *mark_i = noll_vector_at (markings, i);
      assert (NULL != mark_i);

      bool is_pred_edge = false;
      uid_t pred_id = (uid_t) - 1;
      const noll_edge_t *pred_edge = NULL;
      for (size_t j = 0; j < noll_vector_size (edges); ++j)
        {
          const noll_edge_t *ed =
            noll_vector_at (graph->edges, noll_vector_at (edges, j));
          assert (NULL != ed);

          const char *field_name = noll_field_name (ed->label);
          uid_t field_symbol = (uid_t) - 1;
          if (NOLL_EDGE_PTO == ed->kind)
            {
              assert (2 == noll_vector_size (ed->args));

              field_name = noll_field_name (ed->label);
              field_symbol = ed->label;
            }
          else if (NOLL_EDGE_PRED == ed->kind)
            {
              // TODO: should this be the only edge leaving src?
              // MS: yes, if not a two dir predicate
              // use noll_pred_is_one_dir
              assert (2 <= noll_vector_size (ed->args));
              assert (!is_pred_edge);
              assert ((uid_t) - 1 == pred_id);
              assert (NULL == pred_edge);

              const noll_pred_t *edge_pred = noll_pred_getpred (ed->label);
              assert (NULL != edge_pred);
              assert (NULL != edge_pred->typ);
              // two-dir => args >= 4
              assert (!edge_pred->typ->isTwoDir
                      || (4 <= noll_vector_size (ed->args)));
              assert (1 == noll_vector_size (edges)
                      || (edge_pred->typ->isTwoDir
                          && (2 == noll_vector_size (edges))));

              field_name = noll_pred_name (ed->label);
              assert (NULL != field_name);
              field_symbol = noll_pred_get_minfield (ed->label);

              is_pred_edge = true;
              pred_id = ed->label;
              pred_edge = ed;
            }
          else
            {
              NOLL_DEBUG ("ERROR: Unsupported predicate type.\n");
              assert (false);
            }

          assert (NULL != field_name);
          assert ((uid_t) - 1 != field_symbol);
          assert (noll_vector_at (ed->args, 0) == i);
          uid_t next_child = noll_vector_at (ed->args, 1);
          NOLL_DEBUG ("An edge from the node %lu to the node %u over %s\n", i,
                      next_child, field_name);

          bool is_border_var = noll_uid_array_contains (homo, next_child);
          // marking of the child
          const noll_uid_array *mark_next_child =
            noll_vector_at (markings, next_child);
          assert (is_border_var || (NULL != mark_next_child));

          // adding the selector
          noll_uid_array_push (selectors, field_symbol);

          NOLL_DEBUG
            ("Now, we check whether the edge %s is a backbone edge from %lu to %u\n",
             field_name, i, next_child);
          if (noll_marking_is_succ_of_via
              (mark_next_child, mark_i, field_symbol))
            {                   // if 'ed' is a backbone edge
              NOLL_DEBUG ("We are on the backbone!\n");
              noll_uid_array_push (children, next_child);
            }
          else
            {                   // If 'ed' is not a backbone edge. This means that the edge will not be
              // represented in the direct way, but needs to be represented using a
              // path that traverses the backbone in an indirect way. So we need to
              // classify the type of the needed path (there are only some
              // considered) and use a node labelled by this in the transition
              NOLL_DEBUG ("We are NOT on the backbone...\n");

              const noll_ta_symbol_t *alias_symb =
                get_marking_symbol_of_node_wrt_base (next_child,
                                                     i,
                                                     graph,
                                                     homo,
                                                     markings);

              if (NULL == alias_symb)
                {               // in the case the marking could not be deduced, we are out of power
                  noll_tree_free (tree);

                  NOLL_DEBUG ("WARNING: leaving ");
                  NOLL_DEBUG (__func__);
                  NOLL_DEBUG ("() without cleaning up!\n");

                  return NULL;
                }

              size_t leaf_node = last_leaf++; // noll_get_unique ();
              noll_tree_create_node(
                tree,        // the tree
                leaf_node,   // the node index
                alias_symb,  // the symbol
                NULL);       // the children
              noll_uid_array_push (children, leaf_node);
            }
        }

      assert (noll_vector_size (selectors) == noll_vector_size (children));

      const noll_ta_symbol_t *symbol = NULL;
      if (is_pred_edge)
        {                       // for a predicate edge
          assert ((uid_t) - 1 != pred_id);
          assert (NULL != pred_edge);
          const noll_pred_t *ed_pred = noll_pred_getpred (pred_id);
          assert (NULL != ed_pred);
          assert (NULL != ed_pred->typ);
          assert (NULL != pred_edge);
          assert (NULL != pred_edge->args);

          // at this point we process additional parameters of the edge
          size_t it_param;
          if (ed_pred->typ->isTwoDir)
            {                   // for doubly linked segments
              it_param = 4;
            }
          else
            {                   // for singly linked segments
              it_param = 2;
            }

          assert ((noll_vector_size (children) == 1)
                  || (ed_pred->typ->isTwoDir
                      && (noll_vector_size (children) == 2)));

          if (ed_pred->typ->isTwoDir)
            {
              assert (noll_vector_size (children) == 2);

              // move the target of the predicate edge to the first position
              if (noll_vector_at (children, 0) !=
                  noll_vector_at (pred_edge->args, 1))
                {
                  assert (noll_vector_at (children, 1) ==
                          noll_vector_at (pred_edge->args, 1));
                  NOLL_DEBUG ("Sorting children of predicate edge!\n");
                  noll_vector_at (children, 1) = noll_vector_at (children, 0);
                  noll_vector_at (children, 0) =
                    noll_vector_at (pred_edge->args, 1);
                }
            }

          for (; it_param < noll_vector_size (pred_edge->args); ++it_param)
            {
              uint_t param_node = noll_vector_at (pred_edge->args, it_param);
              NOLL_DEBUG
                ("Processing border variable of a predicate edge %s: %u\n",
                 noll_pred_name (pred_id), param_node);
              const noll_ta_symbol_t *param_symb =
                get_marking_symbol_of_node_wrt_base (param_node, i, graph,
                                                     homo, markings);

              NOLL_DEBUG ("  This node is marked as %s\n",
                          noll_ta_symbol_get_str (param_symb));
              size_t leaf_node = last_leaf++; // noll_get_unique ();
              noll_tree_create_node(
                tree,        // the tree
                leaf_node,   // the node index
                param_symb,  // the symbol
                NULL);       // the children
              noll_uid_array_push (children, leaf_node);
            }

          symbol =
            noll_ta_symbol_get_unique_higher_pred (noll_pred_getpred
                                                   (pred_id), vars, mark_i);
        }
      else
        {                       // for a points-to edge
          symbol =
            noll_ta_symbol_get_unique_allocated (selectors, vars, mark_i);
        }

      assert (NULL != symbol);

      NOLL_DEBUG ("Inserting transition q%lu -> %s", i,
                  noll_ta_symbol_get_str (symbol));
      NOLL_DEBUG ("(");
      for (size_t j = 0; j < noll_vector_size (children); ++j)
        {
          NOLL_DEBUG ("q%u, ", noll_vector_at (children, j));
        }
      NOLL_DEBUG (")\n");

      NOLL_DEBUG ("Adding transition over %s\n",
                  noll_ta_symbol_get_str (symbol));

      noll_tree_create_node(
        tree,        // the tree
        i,           // the node index
        symbol,      // the symbol
        children);   // the children

      noll_uid_array_delete (children);
      noll_uid_array_delete (selectors);
      noll_uid_array_delete (vars);
    }

  noll_marking_list_delete (markings);

  return tree;
}
