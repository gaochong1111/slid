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

#ifndef _NOLL_TREE_H_
#define _NOLL_TREE_H_

#include "noll_ta_symbols.h"
#include "libvata_noll_iface.h"


/**
 * @brief  A tree node
 *
 * Contains a symbol and references to children
 */
typedef struct noll_tree_node_s
{
  /// The symbol in the node
  const noll_ta_symbol_t *symbol;

  /// Children of the node (ordered)
  noll_uid_array *children;
} noll_tree_node_t;


/// Inflatable array of tree nodes
NOLL_VECTOR_DECLARE (noll_tree_node_list, noll_tree_node_t *)
/**
 * @brief  The tree
 *
 * The tree is an array of nodes (which are linked via their children
 * attributes), where one is designated as the root. We don't check that the
 * tree is really a tree (acyclic, etc.). If it is not, strange things may
 * start to happen (such as demons flying out of your nose etc.).
 */
     typedef struct noll_tree_s
     {
       /// The array of nodes
       noll_tree_node_list *nodes;

       /// Index of the root node
       uid_t root;
     } noll_tree_t;


/**
 * @brief  Creates a new tree
 *
 * Allocates the internal data structures.
 *
 * @returns  A new tree
 */
     noll_tree_t *noll_tree_new (void);


/**
 * @brief  Creates a new node in a tree
 *
 * This function creates a new node in @p tree, on the index @p node_index,
 * with the symbol @p symbol, and with @p children as its children.
 *
 * @param[in,out]  tree           The tree to be manipulated
 * @param[in]      node_index     Index of the node
 * @param[in]      symbol         The symbol of the node
 * @param[in]      children       The children of the node
 */
     void noll_tree_create_node (noll_tree_t * tree,
                                 uid_t node_index,
                                 const noll_ta_symbol_t * symbol,
                                 const noll_uid_array * children);


/**
 * @brief  Converts a tree into a tree automaton
 *
 * The tree automaton accepts exactly the input tree
 *
 * @param[in]  tree  The tree to be converted into a tree automaton
 *
 * @returns  A tree automaton accepting exactly @p tree
 */
     noll_ta_t *noll_tree_to_ta (const noll_tree_t * tree);


/**
 * @brief  Sets the root node of the tree
 *
 * @param[in,out]  tree  The tree to be changed
 * @param[in]      root  Index of the new root node
 */
     void noll_tree_set_root (noll_tree_t * tree, uid_t root);


/**
 * @brief  Frees a tree
 *
 * Recursively frees all nodes of a tree.
 *
 * @param[in]  tree  The tree to be freed (the pointer is invalid afterwards)
 */
     void noll_tree_free (noll_tree_t * tree);

/**
 * @brief  Prints a tree
 *
 * Print the tree into a file.
 *
 * @param[in]  f     The file, should be opened
 * @param[in]  tree  The tree to be printed
 */
     void noll_tree_fprint (FILE * f, noll_tree_t * tree);



#endif /* _NOLL_TREE_H_ */
