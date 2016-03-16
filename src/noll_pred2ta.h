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
#ifndef NOLL_PRED2TA_H_
#define NOLL_PRED2TA_H_

#include "noll_preds.h"
#include "noll_graph2ta.h"



/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

/** Type of the global array of trees. */
NOLL_VECTOR_DECLARE (noll_tree_array, noll_tree_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

/**
 * @brief Global store mapping predicate identifiers 
 *        to the tree of its matrix 
 */
extern noll_tree_array *pred2tree_array;

void noll_pred2tree_init (void);
/* Initialize global arrays of trees */

/**
 * @brief Global store mapping predicate identifiers 
 *        to the graph of its matrix 
 */
extern noll_graph_array *pred2graph_array;

void noll_pred2graph_init (void);
/* Initialize global arrays of graphs */

/* ====================================================================== */
/* Translators */
/* ====================================================================== */

/**
 * @brief  Translates a higher-order predicate edge into a TA
 *
 * @param[in]  edge  The edge to be translated
 *
 * @returns  A TA representing all models that the edge denotes
 */
noll_ta_t *noll_edge2ta (const noll_edge_t * edge);

/**
 * @brief Apply the general algorithm for the predicate translation.
 *
 * @param[in]  edge  The edge to be translated
 *
 * @return  A TA representing all models that the edge denotes
 */
noll_ta_t *noll_edge2ta_gen (const noll_edge_t * edge);

/* ====================================================================== */
/* Other methods */
/* ====================================================================== */

/**
 * @brief  Returns or builds (if not exist) the graph translating the predicate.
 * 
 * @param[in]  pred  The predicate
 * 
 * @returns The unique graph translated from the predicate
 */
noll_graph_t *noll_pred2graph (const noll_pred_t * pred);

/**
 * @brief  Returns or builds (if not exist) the tree encoding the predicate.
 * 
 * @param[in]  pred  The predicate
 * 
 * @returns The unique tree encodings the predicate
 */
noll_tree_t *noll_pred2tree (const noll_pred_t * pred);

#endif /* NOLL_PRED2TA_H_ */
