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

#ifndef _NOLL2GRAPH_H_
#define _NOLL2GRAPH_H_

#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include "noll_form.h"
#include "noll_vars.h"
#include "noll_graph.h"

noll_graph_t *noll_graph_of_form (noll_form_t * phi, bool isMatrix);
/* Translation of formulas to graphs. */

#endif /* _NOLL2GRAPH_H_ */
