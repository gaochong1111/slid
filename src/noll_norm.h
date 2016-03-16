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

#ifndef NOLL_NORM_H_
#define NOLL_NORM_H_

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "noll_vars.h"
#include "noll_types.h"
#include "noll_form.h"
#include "noll_preds.h"
#include "noll2sat.h"

/* ====================================================================== */
/* Normalize formula using noll2sat */
/* ====================================================================== */

/*
 * Because the old version for building BoolAbstr is not modular,
 * it also contains the normalization.
 *
 * @see noll2bool::normalize and noll2bool::normalize_incremental
 */

/* ====================================================================== */
/* Normalize formula using noll2sat */
/* ====================================================================== */

noll_sat_t *noll_normalize (noll_form_t * form, char *fname, bool incr,
                            bool destructive);
/* Updates form to its normal form and
 * put in the file "file" the boolean abstraction;
 * use incremental minisat if incr = true */

#endif /* NOLL_NORM_H_ */
