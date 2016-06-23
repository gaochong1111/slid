/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
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

/**
 * Defines translation between heap graph to tree automata
 */
#ifndef NOLL_GRAPH2TA_H_
#define NOLL_GRAPH2TA_H_

#include "noll_graph.h"
#include "noll_tree.h"
#include "libvata_noll_iface.h"

/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */


/* ====================================================================== */
/* Translators */
/* ====================================================================== */

/**
 * @brief  Translates a graph into a TA
 *
 * Given a graph @p graph and a homomorphism @p homo, this function transforms
 * @p graph into a tree automaton accepting a singleton set the element of
 * which corresponds to @p graph. This is to be used when checking whether the
 * graph is a model of a predicate edge. The @p homo array maps the arguments
 * of the predicate edge to nodes of the graph, namely @p homo[0] corresponds
 * to the source of the edge, @p homo[1] to the destination of the edge, and
 * the rest of @p homo are the arguments in the same order as in the
 * instantiation of the predicate.
 *
 * @param[in]  graph  The graph to be translated to a TA
 * @param[in]  homo   The mapping of arguments of a predicate edge to nodes of
 *                    @p graph
 *
 * @returns  The TA encoding @p graph
 */
noll_tree_t *noll_graph2ta (const noll_graph_t * graph,
                            const noll_uid_array * homo);

#endif /* NOLL_GRAPH2TA_H_ */
