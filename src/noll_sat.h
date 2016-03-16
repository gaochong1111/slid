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

#ifndef NOLL_SAT_H_
#define NOLL_SAT_H_

#include <sys/time.h>
#include <stdio.h>
#include <stdlib.h>

#include "noll_vars.h"
#include "noll_types.h"
#include "noll_form.h"
#include "noll_preds.h"
#include "noll2sat.h"
#include "noll_norm.h"

/* ====================================================================== */
/* Sat checking and diagnosis */
/* ====================================================================== */

int noll_sat_solve (noll_form_t * form);
/* Check satisfiability and print diagnosis if required */

void noll_sat_diag_unsat (noll_form_t * form, noll_sat_t * fsat);
/* Print the unsat core */

void noll_sat_diag_sat (noll_form_t * form, noll_sat_t * fsat);
/* Print a sat model */

/* ====================================================================== */
/* Utilities */
/* ====================================================================== */

int
time_difference (struct timeval *result, struct timeval *t2,
                 struct timeval *t1);


#endif /* NOLL_SAT_H_ */
