#ifndef CSLTP_SAT_H
#define CSLTP_SAT_H

#include "noll_form.h"
#include "noll_preds.h"
#include "csltp_order_graph.h"



/**
 *@return 1, if sat
 0, if unsat
 -1,if undef
*/
int csltp_sat_check(noll_form_t *);


/**
 * compute lfp(pred)
 * @param pred: the predicate definition
 * @return ogset: the least fixed point: order graph set
 */
OrderGraphSet lfp(noll_pred_t* pred);


#ifdef __cplusplus
extern "C" {
#endif
// declare some c-like functions which may be useed by cpp file

#ifdef __cplusplus
}
#endif


#endif // csltp_sat.h
