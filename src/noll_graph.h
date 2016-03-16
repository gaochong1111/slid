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

#ifndef _NOLL_GRAPH_H_
#define _NOLL_GRAPH_H_

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include "noll_form.h"
#include "noll_vars.h"
#include "noll_types.h"
#include "noll_preds.h"

/* Type of edges */
typedef enum
{
  NOLL_EDGE_DIFF = 0, NOLL_EDGE_PTO, NOLL_EDGE_PRED, NOLL_EDGE_OTHER
} noll_edge_e;

/* Type for edges */
typedef struct noll_edge_s
{
  noll_edge_e kind;             // kind of edge
  noll_uid_array *args;         // array of nodes args[0] = src node, args[1] = dst node
  uint_t label;                 // index of the field or of the predicate
  uint_t bound_svar;            // index of the set variable in slocs_array bounded to the edge, or UNDEFINED_ID
  uint_t id;                    // TODO: id of this edge
  noll_uid_array *impl;         // array of edges implying this one or NULL (related to overlapping)
  noll_uid_array *ssep;         // array of edges strongly separated from this one or NULL
} noll_edge_t;

NOLL_VECTOR_DECLARE (noll_edge_array, noll_edge_t *);

typedef struct noll_graph_t
{
  uint_t nodes_size;            // the number of nodes in the graph
  noll_var_array *lvars;        // graph environment
  noll_var_array *svars;
  uint_t *var2node;             // variables to node labels, array of size of lvars
  noll_edge_array *edges;       // the set of edges in the graph, excluding difference
  noll_uid_array **mat;         // adjacency matrix, mat[i] is the list of edge identifiers from node i
  noll_uid_array **rmat;        // reverse adjacency matrix, rmat[i] is the list of edge identifiers to node i
  bool **diff;                  // low-diagonal matrix, diff[n1][n2] = true iff n1 != n2 and n1 > n2
  noll_dform_array *data;       // data constraints over lvars
  bool isDataComplete;          // all diff and quality constraints are pushed in data ?
  uint_t *sloc2edge;            // mapping set variables to edges in graph
  noll_share_array *share;      // TODO: sharing constraints (on set variables) (related to overlapping)
  bool isComplete;              // if all implicit constraints have been computed
  bool is_precise;              // if graph is precise
} noll_graph_t;

NOLL_VECTOR_DECLARE (noll_graph_array, noll_graph_t *);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

noll_edge_t *noll_edge_alloc (noll_edge_e kind, uint_t src, uint_t dst,
                              uint_t label);
void noll_edge_free (noll_edge_t * e);
noll_edge_t *noll_edge_copy (noll_edge_t * e);

noll_graph_t *noll_graph_alloc (noll_var_array * lvars,
                                noll_var_array * svars, uint_t nodes,
                                uint_t edges, uint_t * vars);
void noll_graph_free (noll_graph_t * g);

noll_graph_t *noll_graph_copy_nodes (noll_graph_t * g);

/* ====================================================================== */
/* Getters/setters */
/* ====================================================================== */

uint_t noll_graph_get_var (const noll_graph_t * g, uint_t n);
/* Get the first location variable labeling this node */

int noll_edge_in_label (noll_edge_t * e, uint_t label);
/* Returns 1 if the edge e has its label in the set of labels
 * of the predicate label */

uint_t noll_graph_get_edge (noll_graph_t * g, noll_edge_e kind, uint_t label,
                            noll_uid_array * args, noll_dform_array * df);
/* Return edge id with label, kind and arguments given. */

noll_typ_t noll_graph_get_node_type (noll_graph_t * g, uint_t n);
/* Return the type of node @p n */

void noll_graph_sat_dform (noll_graph_t * g);
/* Update the data constraints in @g with eq constraints */

bool noll_graph_is_diff (noll_graph_t * g, uint_t n1, uint_t n2);
/* Return true if difference edge between nodes */

bool noll_graph_is_node_data (noll_graph_t * g, uint_t n);
/* Return true if @p n is a node represeting some data var */

bool noll_graph_is_ptosrc (noll_graph_t * g, uint_t n);
/* Return true if @p n is the source of a pto edge */

/* ====================================================================== */
/* Others */
/* ====================================================================== */

void noll_graph_dll (noll_graph_t * g, uid_t pid);
/* Add explicit edges for dll */

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void noll_graph_fprint (FILE * f, noll_graph_t * g);
/* Print to file in text --debug format */
void noll_graph_fprint_dot (char *fname, noll_graph_t * g);
/* Print to file in dot format */
void noll_graph_fprint_sl (char *fname, noll_graph_t * g);
/* Print to file in SL format */

#endif /* _NOLL_GRAPH_H_ */
