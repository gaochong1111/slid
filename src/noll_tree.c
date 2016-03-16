/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure - the data structure for a tree               */
/*                                                                        */
/*  Copyright (C) 2013                                                    */
/*    LIAFA (University of Paris Diderot and CNRS)                        */
/*    VeriFIT (Brno University of Technology)                             */
/*                                                                        */
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

#include "noll.h"
#include "noll_tree.h"

NOLL_VECTOR_DEFINE(noll_tree_node_list, noll_tree_node_t *)

noll_ta_t* noll_tree_to_ta(const noll_tree_t* tree)
{
	assert(NULL != tree);
  assert(NULL != tree->nodes);

  noll_ta_t* ta = vata_create_ta();
  vata_set_state_root(ta, tree->root);

  for (size_t i = 0; i < noll_vector_size(tree->nodes); ++i)
  { // go over all nodes in the tree
    const noll_tree_node_t* node = noll_vector_at(tree->nodes, i);
    if (NULL == node)
    { // if the node is not interesting
      continue;
    }

    assert(NULL != node->children);
    assert(NULL != node->symbol);

    vata_add_transition(
      ta,               // tree automaton
      i,                // the parent state
      node->symbol,     // the symbol
      node->children);  // children states
  }

  return ta;
}


noll_tree_t* noll_tree_new(void)
{
  noll_tree_t* tree = malloc(sizeof(*tree));
  assert(NULL != tree);

  tree->nodes = noll_tree_node_list_new();
  assert(NULL != tree->nodes);

  return tree;
}


void noll_tree_set_root(noll_tree_t* tree, uid_t root)
{
  assert(NULL != tree);

  tree->root = root;
}


void noll_tree_free(noll_tree_t* tree)
{
  assert(NULL != tree);

  for (size_t i = 0; i < noll_vector_size(tree->nodes); ++i)
  {
    noll_tree_node_t* node = noll_vector_at(tree->nodes, i);
    if (NULL != node)
    {
      assert(NULL != node->children);
      noll_uid_array_delete(node->children);
    }

    free(node);
  }

  noll_tree_node_list_delete(tree->nodes);
  free(tree);
}


void noll_tree_create_node(
  noll_tree_t*             tree,
  uid_t                    node_index,
  const noll_ta_symbol_t*  symbol,
  const noll_uid_array*    children)
{
  assert(NULL != tree);
  assert(NULL != symbol);

  while (noll_vector_size(tree->nodes) <= node_index)
  { // extend the array if necessary
    noll_tree_node_list_push(tree->nodes, NULL);
  }

  assert(NULL == noll_vector_at(tree->nodes, node_index));

  noll_tree_node_t* new_node = malloc(sizeof(*new_node));
  assert(NULL != new_node);

  new_node->children = noll_uid_array_new();

  if (NULL != children)
  { // if there were some children passed
    noll_uid_array_copy(new_node->children, children);
  }

  assert(NULL != new_node->children);
  new_node->symbol = symbol;

  noll_vector_at(tree->nodes, node_index) = new_node;
}


void noll_tree_fprint(FILE* f, noll_tree_t* tree) {
	assert (NULL != f);
	if (NULL == tree)
	  fprintf (f, "Tree(NULL)");
	  
	fprintf (f, "Tree (root = %d):\n", tree->root);
	for (uint_t i = 0; i < noll_vector_size(tree->nodes); i++) {
		fprintf (f, "\t Node[%d] --> ", i);
		noll_tree_node_t* ni = noll_vector_at(tree->nodes, i);
		if (ni == NULL) {
			fprintf (f, "NULL\n");
			continue;
		}
		if (ni->symbol != NULL)
		  fprintf (f, "<%s>", noll_ta_symbol_get_str(ni->symbol));
		else 
		  fprintf (f, "<null>");
		fprintf (f, "(");
		if (ni->children != NULL) {
		for (uint_t j = 0; j < noll_vector_size (ni->children); j++) 
		   fprintf (f, "n%d,", noll_vector_at(ni->children, j));
	   }
		 fprintf (f, ")\n");
	}
	fflush (f);
	return;
}
