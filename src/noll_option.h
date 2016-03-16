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
 * Options for the decision procedure.
 */

#ifndef NOLL_OPTION_H_
#define NOLL_OPTION_H_

#include <stdbool.h>
#include <stdio.h>

/* ====================================================================== */
/* Getting/Setting/resetting options */
/* ====================================================================== */

/**
 * @brief Select the version of boolean abstraction to be used.
 *
 * Default version is 1 (newest version).
 */
void noll_option_set_tosat (int version);

/**
 * @brief Return the version of the boolean abstraction.
 */
bool noll_option_is_tosat (int version);

/**
 * @brief Select builtin definition of tree automata for predicate defs.
 *
 * Default is false (i.e., use the general definition).
 */
void noll_option_set_preds (bool isbuiltin);

/**
 * @brief True if builtin encoding of predicates is used.
 */
bool noll_option_is_preds_builtin (void);

/**
 * @brief Select the procedure to be used for the ls predicate.
 *
 * Default version is 1 (use tree automata)
 * Other versions are:
 *   - 0: use explicit check
 */
void noll_option_set_checkLS (int version);

/**
 * @brief Return the version of the procedure used for ls predicate
 */
bool noll_option_is_checkLS (int version);

/**
 * @brief Select the decision procedure.
 *
 * Default version is 1 (use tree automata).
 * Other versions are:
 *   - 0: use syntactic check for LS
 *   - 2: use syntactic check for all
 */
void noll_option_set_check (int version);

/**
 * @brief Return true iff the procedure uses TA
 */
bool noll_option_is_checkTA (void);

/**
 * @brief Return true iff the procedure uses syntactic check
 */
bool noll_option_is_checkSY (void);

/**
 * @brief Trigger the level of optimisation to be used for the
 *        algorithm building tree automata.
 *
 * Default is  0 (i.e., no optimization).
 */
void noll_option_set_pred2ta_opt (int lelev);

/**
 * @brief Level of the optimisation for pred2ta
 */
int noll_option_get_pred2ta_opt (void);


/**
 * @brief Trigger verbosity level.
 *
 * Default is 0 (i.e., no message).
 */
void noll_option_set_verb (int level);

/**
 * @brief Level of verbosity.
 */
int noll_option_get_verb (void);


/**
 * @brief Trigger diagnosis feature.
 *
 * Default is false (i.e., no diagnosis).
 */
void noll_option_set_diag (void);

/**
 * @brief Status of the diagnosis.
 */
bool noll_option_is_diag (void);

/**
 * @brief Set option using the input string of the form '-'optioncode.
 */
int noll_option_set (char *option);

/**
 * @brief Print options.
 */
void noll_option_print (FILE * f);



#endif /* NOLL_OPTION_H_ */
