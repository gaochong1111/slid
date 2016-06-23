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
 * Homomorphism definition and computation.
 */


#ifndef NOLL_HOM_H_
#define NOLL_HOM_H_

#include <stdio.h>
#include "noll_graph.h"
#include "noll_graph2ta.h"


/* ====================================================================== */
/* Datatypes */
/* ====================================================================== */

typedef struct noll_shom_s
{
  size_t ngraph;                /* idx of the negative graph in prob */

  bool is_empty;                /* true if no hom found */
  /* if false, the elements below are empty */
  /* the fields below maps 
   * an element from ngraph 
   * to one or a set of elements from pgraph */
  uint_t *node_hom;             /* node mapping */
  noll_uid_array *pto_hom;      /* pto edge mapping */
  noll_graph_array *ls_hom;     /* list segment (predicate) edge mapping */

  noll_uid_array *pused;        /* edges of pgraph used in this hom 
                                 * of size size(noll_prob->pgraph->edges) */
  noll_dform_array *data;       /* data constraints generated */
} noll_shom_t;

NOLL_VECTOR_DECLARE (noll_shom_array, noll_shom_t *);

typedef struct noll_hom_s
{
  bool is_empty;                /* true if hom is not found */
  /* if false, the array below is not complete */

  noll_shom_array *shom;        /* array of size ngraph of simple hom */
} noll_hom_t;

typedef noll_uid_array noll_uid_map;    /* used to represent maps uid_t -> uid_t */


/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

noll_hom_t *noll_hom_alloc (void);
/* Allocate a homeomorphism for the crt problem. */
void noll_hom_delete (noll_hom_t * h);
/* Free the homeomorphism */

noll_uid_map *noll_uid_map_new (uint_t size);
/* Alocate a map and initialize elements to UNDEFINED_ID */
void noll_uid_map_delete (noll_uid_map * m);
/* Free the map */

/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

#define noll_uid_map_set(m,idx,value) noll_uid_array_set(m,idx,value)

/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void noll_hom_fprint (FILE * f, noll_hom_t * h);
void noll_uid_map_fprint (FILE * f, noll_uid_map * h);

/* ====================================================================== */
/* Solver */
/* ====================================================================== */

int noll_hom_build (void);
/* Search a homeomorphism to prove noll_prob 
 * from prob->ngraph to noll_prob->pgraph. */
/*
 * Returns 0 if there is no homeomorphism from g1 to g2,
 * otherwise (TODO) it updates
 * sharing constraints in g2 with the substitution given by the
 * edge mapping in the homeomorphism.
 */


#endif /* NOLL_HOM_H_ */
