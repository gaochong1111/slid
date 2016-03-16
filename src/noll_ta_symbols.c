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

#include "noll.h"
#include "noll_ta_symbols.h"

/* ====================================================================== */
/* Data types */
/* ====================================================================== */

/// Enumeration of possible aliasing of nodes
enum noll_tree_label_type_t
{
  NOLL_TREE_LABEL_ALLOCATED,    ///< the node is allocated: no aliasing is used
  NOLL_TREE_LABEL_ALIASING_VARIABLE,    ///< a node with a program variable is aliased
  NOLL_TREE_LABEL_ALIASING_MARKING,     ///< marking is used as the relation
  NOLL_TREE_LABEL_HIGHER_PRED,  ///< higher-order predicate
};

/// Enumeration of possible alias marking relations
enum noll_alias_marking_rel_t
{
  NOLL_ALIAS_MARKING_REL_UP,    ///< the alias UP relation
  NOLL_ALIAS_MARKING_REL_UP_UP, ///< the alias UP UP relation
  NOLL_ALIAS_MARKING_REL_UP_DOWN_FIRST  ///< the alias UP DOWN relation
};

/**
 * @brief  The symbol used in the tree encoding and in tree automata
 */
typedef struct noll_ta_symbol
{
  /// The type of the label (see enum @p noll_tree_label_type_t)
  unsigned char label_type;

  union
  {
    /// The structure used for allocated nodes (for label_type ==
    /// NOLL_TREE_LABEL_ALLOCATED)
    struct
    {
      /// The selectors
      noll_uid_array *sels;

      /// Variables that might alias with the node
      noll_uid_array *vars;

      /// The (least) marking of the node
      noll_uid_array *marking;
    } allocated;

    /// Marking of the aliased node (for label_type ==
    /// NOLL_TREE_LABEL_ALIASING_MARKING)
    struct
    {
      /// The marking
      noll_uid_array *marking;

      /// Identifier of the relation (of the type noll_alias_marking_rel_t)
      unsigned char id_relation;
    } alias_marking;

    /// Name of the variable the node is aliased to (for label_type ==
    /// NOLL_TREE_LABEL_ALIASING_VARIABLE)
    uid_t alias_var;

    /// Higher-order predicate (for label_type == NOLL_TREE_LABEL_HIGHER_PRED)
    struct
    {
      /// the higher-order predicate represented by the symbol
      const noll_pred_t *pred;

      /// Variables that might alias with the node
      noll_uid_array *vars;

      /// The (least) marking of the node
      noll_uid_array *marking;
    } higher_pred;
  };

  /// The string representation (for humans)
  char *str;
} noll_ta_symbol_t;

// a database of symbols
NOLL_VECTOR_DEFINE (noll_ta_symbol_array, const noll_ta_symbol_t *)

/* ====================================================================== */
/* Globals */
/* ====================================================================== */
/// The global database of symbols
/// @todo: it would be more efficient to have 3 databases for every label_type
     static noll_ta_symbol_array *g_ta_symbols;

/* ====================================================================== */
/* Functions */
/* ====================================================================== */

     char *noll_marking_tostring (const noll_uid_array * marking)
{
  assert (NULL != marking);

  static const size_t BUFFER_SIZE = 128;

  char *buffer = malloc (BUFFER_SIZE);
  size_t index = 0;

  assert (index < BUFFER_SIZE);
  buffer[index++] = '[';

  for (size_t i = 0; i < noll_vector_size (marking); ++i)
    {
      if (noll_vector_at (marking, i) == NOLL_MARKINGS_EPSILON)
        {
          assert (0 == i);
          assert (index < BUFFER_SIZE);
          index += snprintf (&buffer[index], BUFFER_SIZE - index, "e, ");
        }
      else
        {
          assert (index < BUFFER_SIZE);
          index += snprintf (&buffer[index],
                             BUFFER_SIZE - index,
                             "%s, ",
                             noll_field_name (noll_vector_at (marking, i)));
        }
    }

  if (noll_vector_size (marking) > 0)
    {
      index -= 2;               // move at the position of the last ','
    }

  assert (index < BUFFER_SIZE);
  buffer[index++] = ']';
  assert (index < BUFFER_SIZE);
  buffer[index] = '\0';

  return buffer;
}


/**
 * @brief  Gets a string for an UID array
 *
 * @param[in]  arr   The UID array
 *
 * @returns  A string representing @p arr. It is a responsibility of the caller
 *           to dispose of the returned memory.
 */
static char *
noll_uid_array_tostring (const noll_uid_array * arr)
{
  assert (NULL != arr);
  static const size_t BUFFER_SIZE = 128;

  char *buffer = malloc (BUFFER_SIZE);
  size_t index = 0;
  assert (index < BUFFER_SIZE);

  for (size_t i = 0; i < noll_vector_size (arr); ++i)
    {
      assert (index < BUFFER_SIZE);
      index += snprintf (&buffer[index],
                         BUFFER_SIZE - index,
                         "%d, ", noll_vector_at (arr, i));
    }

  if (noll_vector_size (arr) > 0)
    {
      index -= 2;               // move at the position of the last ','
    }

  assert (index < BUFFER_SIZE);
  buffer[index] = '\0';

  return buffer;
}


/**
 * @brief  Checks whether every element of @p lhs is also in @p rhs
 *
 * Checks whether the set of elements of @p lhs is a subset (or equal) to the
 * set of elements of rhs. The number of occurrences of an element is
 * neglected.
 *
 * @param[in]  smaller  The @e smaller array
 * @param[in]  bigger   The @e bigger array
 *
 * @returns  @p true iff every element of @p smaller is also in @p bigger, @p
 *           false otherwise
 */
static bool
noll_uid_array_subseteq (const noll_uid_array * smaller,
                         const noll_uid_array * bigger)
{
  assert (NULL != smaller);
  assert (NULL != bigger);

  for (size_t i = 0; i < noll_vector_size (smaller); ++i)
    {                           // for every element in 'smaller' ...
      bool found = false;
      for (size_t j = 0; j < noll_vector_size (bigger); ++j)
        {                       // ... we check whether it is also in 'bigger'
          if (noll_vector_at (smaller, i) == noll_vector_at (bigger, j))
            {
              found = true;
              break;
            }
        }

      if (!found)
        {
          return false;
        }
    }

  return true;
}

/**
 * @brief  Checks whether two symbols match
 *
 * @param[in]  lhs  The left-hand side
 * @param[in]  rhs  The right-hand side
 *
 * @returns  @p true if @p lhs and @p rhs match, @p false otherwise
 */
static bool
noll_ta_symbol_match (const noll_ta_symbol_t * lhs,
                      const noll_ta_symbol_t * rhs)
{
  // check that the parameters are sane
  assert (NULL != lhs);
  assert (NULL != rhs);

  if (lhs->label_type != rhs->label_type)
    {                           // if the types do not match
      return false;
    }

  switch (lhs->label_type)
    {
    case NOLL_TREE_LABEL_ALLOCATED:
      {
        assert (NULL != lhs->allocated.sels);
        assert (NULL != rhs->allocated.sels);
        if (!noll_uid_array_equal (lhs->allocated.sels, rhs->allocated.sels))
          {
            return false;
          }

        // TODO: this might be better if the variables are always sorted
        assert (NULL != lhs->allocated.vars);
        assert (NULL != rhs->allocated.vars);
        if (!noll_uid_array_subseteq
            (lhs->allocated.vars, rhs->allocated.vars)
            || !noll_uid_array_subseteq (rhs->allocated.vars,
                                         lhs->allocated.vars))
          {
            return false;
          }

        assert (NULL != lhs->allocated.marking);
        assert (NULL != rhs->allocated.marking);
        if (!noll_uid_array_equal
            (lhs->allocated.marking, rhs->allocated.marking))
          {
            return false;
          }

        return true;
      }

    case NOLL_TREE_LABEL_ALIASING_VARIABLE:
      {
        return lhs->alias_var == rhs->alias_var;
      }

    case NOLL_TREE_LABEL_ALIASING_MARKING:
      {
        if (lhs->alias_marking.id_relation != rhs->alias_marking.id_relation)
          {
            return false;
          }

        return noll_uid_array_equal (lhs->alias_marking.marking,
                                     rhs->alias_marking.marking);
      }

    case NOLL_TREE_LABEL_HIGHER_PRED:
      {
        if (lhs->higher_pred.pred != rhs->higher_pred.pred)
          {
            return false;
          }

        // TODO: this might be better if the variables are always sorted
        assert (NULL != lhs->higher_pred.vars);
        assert (NULL != rhs->higher_pred.vars);
        if (!noll_uid_array_subseteq
            (lhs->higher_pred.vars, rhs->higher_pred.vars)
            || !noll_uid_array_subseteq (rhs->higher_pred.vars,
                                         lhs->higher_pred.vars))
          {
            return false;
          }

        assert (NULL != lhs->higher_pred.marking);
        assert (NULL != rhs->higher_pred.marking);
        if (!noll_uid_array_equal
            (lhs->higher_pred.marking, rhs->higher_pred.marking))
          {
            return false;
          }

        return true;
      }

    default:
      {
        NOLL_DEBUG ("ERROR: invalid symbol label type!\n");
        assert (false);
      }
    }
  return false;
}


const noll_uid_array *
noll_ta_symbol_get_vars (const noll_ta_symbol_t * symb)
{
  // check input
  assert (NULL != symb);

  switch (symb->label_type)
    {
    case NOLL_TREE_LABEL_ALLOCATED:
      return symb->allocated.vars;
    case NOLL_TREE_LABEL_ALIASING_VARIABLE: {
      noll_uid_array* r = noll_uid_array_new();
      noll_uid_array_push (r, symb->alias_var);
      return r;
  }
    case NOLL_TREE_LABEL_HIGHER_PRED:
      return symb->higher_pred.vars;
    default:
      break;
    }
  return noll_uid_array_new ();
}


const noll_uid_array *
noll_ta_symbol_get_marking (const noll_ta_symbol_t * symb)
{
  // check input
  assert (NULL != symb);

  switch (symb->label_type)
    {
    case NOLL_TREE_LABEL_ALLOCATED:
      return symb->allocated.marking;
    case NOLL_TREE_LABEL_ALIASING_MARKING:
      return symb->alias_marking.marking;
    case NOLL_TREE_LABEL_HIGHER_PRED:
      return symb->higher_pred.marking;
    default:
      break;
    }
  return noll_uid_array_new ();
}


uid_t
noll_ta_symbol_get_pid (const noll_ta_symbol_t * symb)
{
  // check input
  assert (NULL != symb);

  if (symb->label_type == NOLL_TREE_LABEL_HIGHER_PRED)
    return symb->higher_pred.pred->pid;

  return UNDEFINED_ID;
}

const char *
noll_ta_symbol_get_str (const noll_ta_symbol_t * symb)
{
  // check inputs
  assert (NULL != symb);
  assert (NULL != symb->str);

  return symb->str;
}


/**
 * @brief  Generates a string for a selectors
 *
 * This function generates a human-readable string for a textual representation
 * of a vector of selectors. The function returns a non-shared dynamically
 * allocated memory block---it is the responsibility of the caller to dispose
 * of it.
 *
 * @param[in]  sels  The selectors from which the symbol is to be composed
 *
 * @returns  Pointer to a dynamically allocated memory block with the
 *           human-readable representation of the selectors. After the return,
 *           the caller is responsible for deallocating this block.
 */
static char *
noll_sels_to_string_symbol (const noll_uid_array * sels)
{
  assert (NULL != sels);

  // compute the necessary memory for the string
  size_t str_len = 1;           // for '\0'
  str_len += (noll_vector_size (sels) - 1) * 2; // for (n-1) * ", "
  for (size_t i = 0; i < noll_vector_size (sels); ++i)
    {
      const char *field_name = noll_field_name (noll_vector_at (sels, i));
      assert (NULL != field_name);
      NOLL_DEBUG ("Processing field %u with the name %s\n",
                  noll_vector_at (sels, i), field_name);

      str_len += strlen (field_name);
    }

  char *str_symbol = malloc (str_len);
  assert (NULL != str_symbol);


  size_t cnt = 0;               // where to start copying
  for (size_t i = 0; i < noll_vector_size (sels); ++i)
    {
      if (0 != cnt)
        {                       // if we are not at the beginning
          str_symbol[cnt++] = ',';
          str_symbol[cnt++] = ' ';
        }

      const char *field_name = noll_field_name (noll_vector_at (sels, i));
      strcpy (&str_symbol[cnt], field_name);
      cnt += strlen (field_name);
    }

  // check that everything is correct
  assert (cnt == str_len - 1);

  str_symbol[str_len - 1] = '\0';

  return str_symbol;
}


void
noll_ta_symbol_init ()
{
  g_ta_symbols = noll_ta_symbol_array_new ();
  noll_ta_symbol_array_reserve (g_ta_symbols, 10);
}


/**
 * @brief  A function to safely deallocate a TA symbol
 *
 * This function releases the memory allocated by a TA symbol. After the call
 * to the function, @p sym is invalid and the memory deallocated.
 *
 * @param[in,out]  sym  The symbol to be killed
 */
static void
noll_ta_symbol_kill (noll_ta_symbol_t * sym)
{
  assert (NULL != sym);

  switch (sym->label_type)
    {
    case NOLL_TREE_LABEL_ALLOCATED:
      {
        assert (NULL != sym->allocated.sels);
        noll_uid_array_delete (sym->allocated.sels);
        assert (NULL != sym->allocated.marking);
        noll_uid_array_delete (sym->allocated.marking);
        assert (NULL != sym->allocated.vars);
        noll_uid_array_delete (sym->allocated.vars);

        break;
      }

    case NOLL_TREE_LABEL_ALIASING_VARIABLE:
      {
        // nothing spectacular
        break;
      }

    case NOLL_TREE_LABEL_ALIASING_MARKING:
      {
        assert (NULL != sym->alias_marking.marking);
        noll_uid_array_delete (sym->alias_marking.marking);

        break;
      }

    case NOLL_TREE_LABEL_HIGHER_PRED:
      {
        assert (NULL != sym->higher_pred.marking);
        noll_uid_array_delete (sym->higher_pred.marking);
        assert (NULL != sym->higher_pred.vars);
        noll_uid_array_delete (sym->higher_pred.vars);

        break;
      }

    default:
      {
        NOLL_DEBUG ("ERROR: invalid symbol label type!\n");
        assert (false);
      }
    }

  if (NULL != sym->str)
    {                           // the string may not be allocated
      free (sym->str);
    }

  free (sym);
}


void
noll_ta_symbol_destroy ()
{
  assert (NULL != g_ta_symbols);

  for (size_t i = 0; i < noll_vector_size (g_ta_symbols); ++i)
    {
      const noll_ta_symbol_t *smb = noll_vector_at (g_ta_symbols, i);
      assert (NULL != smb);
      noll_ta_symbol_kill (smb);
    }

  noll_ta_symbol_array_delete (g_ta_symbols);
}


bool
noll_ta_symbol_is_alias (const noll_ta_symbol_t * symb)
{
  return symb->label_type == NOLL_TREE_LABEL_ALIASING_VARIABLE
    || symb->label_type == NOLL_TREE_LABEL_ALIASING_MARKING;
}


bool
noll_ta_symbol_is_pred (const noll_ta_symbol_t * symb)
{
  return symb->label_type == NOLL_TREE_LABEL_HIGHER_PRED;
}


bool
noll_ta_symbol_is_pto (const noll_ta_symbol_t * symb)
{
  return symb->label_type == NOLL_TREE_LABEL_ALLOCATED;
}


/**
 * @brief  Attempts to find a given symbol in the global database
 *
 * @param[in]  symb  The symbol to be sought
 *
 * @returns  Either a pointer to the unique representation of the symbol @p
 *           symb if it exists, or @p NULL if it does not exist
 */
static const noll_ta_symbol_t *
noll_ta_symbol_find (const noll_ta_symbol_t * symb)
{
  assert (NULL != symb);
  assert (NULL != g_ta_symbols);

  for (size_t i = 0; i < noll_vector_size (g_ta_symbols); ++i)
    {
      const noll_ta_symbol_t *iter = noll_vector_at (g_ta_symbols, i);
      if (noll_ta_symbol_match (symb, iter))
        {
          return iter;
        }
    }

  return NULL;
}


/**
 * @brief  Retrieves the string for an allocated node
 *
 * @param[in]  sym  The node the string of which is desired
 *
 * @returns  The string representation of the symbol. The caller is responsible
 *           for the deallocation of the returned memory.
 */
static char *
noll_ta_symbol_alloc_str (const noll_ta_symbol_t * sym)
{
  assert (NULL != sym);
  assert (NOLL_TREE_LABEL_ALLOCATED == sym->label_type);
  assert (NULL != sym->allocated.sels);
  assert (NULL != sym->allocated.marking);
  assert (NULL != sym->allocated.vars);

  char *str_sels = noll_sels_to_string_symbol (sym->allocated.sels);
  assert (NULL != str_sels);
  char *str_mark = noll_marking_tostring (sym->allocated.marking);
  assert (NULL != str_mark);
  char *str_vars = noll_uid_array_tostring (sym->allocated.vars);
  assert (NULL != str_vars);

  // TODO: the following might not have to be done if we return the length of
  // the strings from the respective function calls
  size_t len_sels = strlen (str_sels);
  size_t len_mark = strlen (str_mark);
  size_t len_vars = strlen (str_vars);

  size_t total_len = 1 /* '[' */  +
    1 /* '<' */  +
    len_sels + 1 /* '>' */  +
    1 /* ',' */  +
    1 /* ' ' */  +
    len_mark + 1 /* ',' */  +
    1 /* ' ' */  +
    1 /* '{' */  +
    len_vars + 1 /* '}' */  +
    1 /* ']' */  +
    1 /* '\0' */ ;

  char *str = malloc (total_len);
  size_t index = 0;
  str[index++] = '[';
  str[index++] = '<';
  strcpy (&str[index], str_sels);
  index += len_sels;
  str[index++] = '>';
  str[index++] = ',';
  str[index++] = ' ';
  strcpy (&str[index], str_mark);
  index += len_mark;
  str[index++] = ',';
  str[index++] = ' ';
  str[index++] = '{';
  strcpy (&str[index], str_vars);
  index += len_vars;
  str[index++] = '}';
  str[index++] = ']';
  assert (index == total_len - 1);
  str[index] = '\0';

  // remove the temporary strings
  free (str_sels);
  free (str_mark);
  free (str_vars);

  return str;
}


/**
 * @brief  Retrieves the string for a higher-order predicate
 *
 * @param[in]  sym  The node the string of which is desired
 *
 * @returns  The string representation of the symbol. The caller is responsible
 *           for the deallocation of the returned memory.
 */
static char *
noll_ta_symbol_higher_pred_str (const noll_ta_symbol_t * sym)
{
  assert (NULL != sym);
  assert (NOLL_TREE_LABEL_HIGHER_PRED == sym->label_type);
  assert (NULL != sym->higher_pred.pred);
  assert (NULL != sym->higher_pred.pred->pname);
  assert (NULL != sym->higher_pred.marking);
  assert (NULL != sym->higher_pred.vars);

  const char *str_pred = sym->higher_pred.pred->pname;
  char *str_mark = noll_marking_tostring (sym->higher_pred.marking);
  assert (NULL != str_mark);
  char *str_vars = noll_uid_array_tostring (sym->higher_pred.vars);
  assert (NULL != str_vars);

  // TODO: the following might not have to be done if we return the length of
  // the strings from the respective function calls
  size_t len_pred = strlen (sym->higher_pred.pred->pname);
  size_t len_mark = strlen (str_mark);
  size_t len_vars = strlen (str_vars);

  size_t total_len = 1 /* '[' */  +
    1 /* '<' */  +
    1 /* '@' */  +
    1 /* '@' */  +
    len_pred + 1 /* '(' */  +
    1 /* ')' */  +
    1 /* '@' */  +
    1 /* '@' */  +
    1 /* '>' */  +
    1 /* ',' */  +
    1 /* ' ' */  +
    len_mark + 1 /* ',' */  +
    1 /* ' ' */  +
    1 /* '{' */  +
    len_vars + 1 /* '}' */  +
    1 /* ']' */  +
    1 /* '\0' */ ;

  char *str = malloc (total_len);
  size_t index = 0;
  str[index++] = '[';
  str[index++] = '<';
  str[index++] = '@';
  str[index++] = '@';
  strcpy (&str[index], str_pred);
  index += len_pred;
  str[index++] = '(';
  str[index++] = ')';
  str[index++] = '@';
  str[index++] = '@';
  str[index++] = '>';
  str[index++] = ',';
  str[index++] = ' ';
  strcpy (&str[index], str_mark);
  index += len_mark;
  str[index++] = ',';
  str[index++] = ' ';
  str[index++] = '{';
  strcpy (&str[index], str_vars);
  index += len_vars;
  str[index++] = '}';
  str[index++] = ']';
  assert (index == total_len - 1);
  str[index] = '\0';

  // remove the temporary strings
  free (str_mark);
  free (str_vars);

  return str;
}


/**
 * @brief  Retrieves the string for a node aliasing to a variable
 *
 * @param[in]  sym  The node the string of which is desired
 *
 * @returns  The string representation of the symbol. The caller is responsible
 *           for the deallocation of the returned memory.
 */
static char *
noll_ta_symbol_alias_var_str (const noll_ta_symbol_t * sym)
{
  assert (NULL != sym);
  assert (NOLL_TREE_LABEL_ALIASING_VARIABLE == sym->label_type);

  static const size_t BUFFER_SIZE = 16;

  char *buffer = malloc (BUFFER_SIZE);
  size_t index = 0;

  assert (index < BUFFER_SIZE);
  index += snprintf (&buffer[index],
                     BUFFER_SIZE - index, "|var(%u)|", sym->alias_var);

  assert (index < BUFFER_SIZE);
  buffer[index] = '\0';

  return buffer;
}


/**
 * @brief  Retrieves the string for a node aliasing to a marking
 *
 * @param[in]  sym  The node the string of which is desired
 *
 * @returns  The string representation of the symbol. The caller is responsible
 *           for the deallocation of the returned memory.
 */
static char *
noll_ta_symbol_alias_marking_str (const noll_ta_symbol_t * sym)
{
  assert (NULL != sym);
  assert (NOLL_TREE_LABEL_ALIASING_MARKING == sym->label_type);
  assert (NULL != sym->alias_marking.marking);

  char *str_mark = noll_marking_tostring (sym->alias_marking.marking);
  assert (NULL != str_mark);
  size_t len_mark = strlen (str_mark);

  static const size_t BUFFER_SIZE = 256;

  char *buffer = malloc (BUFFER_SIZE);
  size_t index = 0;

  assert (index < BUFFER_SIZE);
  index += snprintf (&buffer[index], BUFFER_SIZE - index, "alias<");

  switch (sym->alias_marking.id_relation)
    {
    case NOLL_ALIAS_MARKING_REL_UP:
      {
        assert (index < BUFFER_SIZE);
        index += snprintf (&buffer[index], BUFFER_SIZE - index, "UP");
        break;
      }

    case NOLL_ALIAS_MARKING_REL_UP_UP:
      {
        assert (index < BUFFER_SIZE);
        index += snprintf (&buffer[index], BUFFER_SIZE - index, "UP UP");
        break;
      }

    case NOLL_ALIAS_MARKING_REL_UP_DOWN_FIRST:
      {
        assert (index < BUFFER_SIZE);
        index += snprintf (&buffer[index],
                           BUFFER_SIZE - index, "UP DOWN fst");
        break;
      }

    default:
      {
        NOLL_DEBUG ("Error: invalid alias marking relation\n");
        assert (false);
      }
    }

  assert (index < BUFFER_SIZE);
  buffer[index++] = '>';
  assert (index < BUFFER_SIZE);
  buffer[index++] = '(';

  assert (index < BUFFER_SIZE - len_mark);
  strcpy (&buffer[index], str_mark);
  index += len_mark;
  assert (index < BUFFER_SIZE);
  buffer[index++] = ')';
  assert (index < BUFFER_SIZE);
  buffer[index++] = ']';
  assert (index < BUFFER_SIZE);
  buffer[index++] = '\0';

  free (str_mark);

  return buffer;
}


/**
 * @brief  Fills the string representation for a symbol
 *
 * This function fills in the string representation data field of a symbol
 * according to the stored data.
 *
 * @param[in,out]  sym  The symbol to be modified
 */
static void
noll_ta_symbol_fill_str (noll_ta_symbol_t * sym)
{
  assert (NULL != sym);

  switch (sym->label_type)
    {
    case NOLL_TREE_LABEL_ALLOCATED:
      {
        sym->str = noll_ta_symbol_alloc_str (sym);
        break;
      }

    case NOLL_TREE_LABEL_ALIASING_VARIABLE:
      {
        sym->str = noll_ta_symbol_alias_var_str (sym);
        break;
      }

    case NOLL_TREE_LABEL_ALIASING_MARKING:
      {
        sym->str = noll_ta_symbol_alias_marking_str (sym);
        break;
      }

    case NOLL_TREE_LABEL_HIGHER_PRED:
      {
        sym->str = noll_ta_symbol_higher_pred_str (sym);
        break;
      }

    default:
      {
        NOLL_DEBUG ("ERROR: invalid symbol label type!\n");
        assert (false);
      }
    }
}


/**
 * @brief  Allocates and pre-fills a TA symbol
 *
 * This function allocates a new TA symbol and pre-fills its data it is the
 * responsibility of the caller to deallocate the returned symbol.
 *
 * @returns  An allocated TA symbol. It is the responsibility of the caller to
 * deallocate it.
 */
static noll_ta_symbol_t *
noll_ta_symbol_create (void)
{
  noll_ta_symbol_t *alloc_symb = calloc (1, sizeof (*alloc_symb));
  assert (NULL != alloc_symb);

  return alloc_symb;
}


/**
 * @brief  Spawns a symbol by either finding in a DB or adding and returning
 *
 * This function, given the symbol @p symb, attempts to find @p symb in the
 * global database of symbols and if it is found, @p symb is deleted and the
 * found instance is returned, if not, then @p symb is added to the global
 * database and pointer to the instance is returned.
 *
 * @param[in]  symb  The symbol to be spawned
 *
 * @returns  The spawned symbol
 */
static const noll_ta_symbol_t *
noll_symbol_spawn (noll_ta_symbol_t * symb)
{
  assert (NULL != symb);

  const noll_ta_symbol_t *ret_symb;
  if ((ret_symb = noll_ta_symbol_find (symb)) != NULL)
    {
      noll_ta_symbol_kill (symb);
      return ret_symb;
    }

  noll_ta_symbol_fill_str (symb);       // compute the string
  assert (NULL != symb->str);

  NOLL_DEBUG ("Inserting new symbol: %s\n", symb->str);

  noll_ta_symbol_array_push (g_ta_symbols, symb);

  return symb;
}


const noll_ta_symbol_t *
noll_ta_symbol_get_unique_allocated (const noll_uid_array * sels,
                                     const noll_uid_array * vars,
                                     const noll_uid_array * marking)
{
  // check for the input parameters
  assert (NULL != sels);
  assert (NULL != marking);

  noll_ta_symbol_t *symb = noll_ta_symbol_create ();
  assert (NULL != symb);

  symb->str = NULL;             // clear the string
  symb->label_type = NOLL_TREE_LABEL_ALLOCATED;
  noll_uid_array *alloc_sels = noll_uid_array_new ();
  assert (NULL != alloc_sels);
  noll_uid_array_copy (alloc_sels, sels);       // copy selectors
  symb->allocated.sels = alloc_sels;

  symb->allocated.vars = noll_uid_array_new ();
  assert (NULL != symb->allocated.vars);
  if (NULL != vars)
    {                           // if there were some variables, copy
      noll_uid_array_copy (symb->allocated.vars, vars);
    }

  symb->allocated.marking = noll_uid_array_new ();
  assert (NULL != symb->allocated.marking);
  noll_uid_array_copy (symb->allocated.marking, marking);

  // get the unique representation of the symbol
  const noll_ta_symbol_t *ret_sym = noll_symbol_spawn (symb);
  assert (NULL != ret_sym);

  return ret_sym;
}


const noll_ta_symbol_t *
noll_ta_symbol_get_unique_aliased_var (uid_t alias_var)
{
  noll_ta_symbol_t *symb = noll_ta_symbol_create ();
  assert (NULL != symb);

  symb->label_type = NOLL_TREE_LABEL_ALIASING_VARIABLE;
  symb->alias_var = alias_var;

  // get the unique representation of the symbol
  const noll_ta_symbol_t *ret_sym = noll_symbol_spawn (symb);
  assert (NULL != ret_sym);
  return ret_sym;
}


const noll_ta_symbol_t *
noll_ta_symbol_get_unique_aliased_marking (unsigned char id_rel,
                                           const noll_uid_array *
                                           alias_marking)
{
  // check for the input parameters
  assert (NULL != alias_marking);
  assert ((NOLL_ALIAS_MARKING_REL_UP == id_rel) ||
          (NOLL_ALIAS_MARKING_REL_UP_UP == id_rel) ||
          (NOLL_ALIAS_MARKING_REL_UP_DOWN_FIRST == id_rel));

  noll_ta_symbol_t *symb = noll_ta_symbol_create ();
  assert (NULL != symb);
  symb->label_type = NOLL_TREE_LABEL_ALIASING_MARKING;
  symb->alias_marking.marking = noll_uid_array_new ();
  assert (NULL != symb->alias_marking.marking);
  noll_uid_array_copy (symb->alias_marking.marking, alias_marking);
  symb->alias_marking.id_relation = id_rel;

  // get the unique representation of the symbol
  const noll_ta_symbol_t *ret_sym = noll_symbol_spawn (symb);
  assert (NULL != ret_sym);
  return ret_sym;
}


const noll_ta_symbol_t *
noll_ta_symbol_get_unique_aliased_marking_up (const noll_uid_array *
                                              alias_marking)
{
  return noll_ta_symbol_get_unique_aliased_marking (NOLL_ALIAS_MARKING_REL_UP,
                                                    alias_marking);
}


const noll_ta_symbol_t *
noll_ta_symbol_get_unique_aliased_marking_up_up (const noll_uid_array *
                                                 alias_marking)
{
  return
    noll_ta_symbol_get_unique_aliased_marking (NOLL_ALIAS_MARKING_REL_UP_UP,
                                               alias_marking);
}


const noll_ta_symbol_t *
noll_ta_symbol_get_unique_aliased_marking_up_down_fst (const noll_uid_array *
                                                       alias_marking)
{
  return
    noll_ta_symbol_get_unique_aliased_marking
    (NOLL_ALIAS_MARKING_REL_UP_DOWN_FIRST, alias_marking);
}


const noll_ta_symbol_t *
noll_ta_symbol_get_unique_higher_pred (const noll_pred_t * pred,
                                       const noll_uid_array * vars,
                                       const noll_uid_array * marking)
{
  assert (NULL != pred);
  assert (NULL != marking);

  noll_ta_symbol_t *symb = noll_ta_symbol_create ();
  assert (NULL != symb);

  symb->str = NULL;             // clear the string
  symb->label_type = NOLL_TREE_LABEL_HIGHER_PRED;
  symb->higher_pred.pred = pred;

  symb->higher_pred.vars = noll_uid_array_new ();
  assert (NULL != symb->higher_pred.vars);
  if (NULL != vars)
    {                           // if there were some variables, copy
      noll_uid_array_copy (symb->allocated.vars, vars);
    }

  symb->higher_pred.marking = noll_uid_array_new ();
  assert (NULL != symb->higher_pred.marking);
  noll_uid_array_copy (symb->higher_pred.marking, marking);

  // get the unique representation of the symbol
  const noll_ta_symbol_t *ret_sym = noll_symbol_spawn (symb);
  assert (NULL != ret_sym);

  return ret_sym;
}


/*
 * @brief Renames components of a symbol
 * 
 * Translates the variables and the markings in the input symbol 
 * using the input mappings.
 * 
 * @param[in] sym     A symbol to be renamed
 * @param[in] vmap    The mapping used for vars
 * @param[in] mmap    The mapping used for markings
 * @return            A new symbol
 */
const noll_ta_symbol_t *
noll_ta_symbol_get_unique_renamed (const noll_ta_symbol_t * sym,
                                   bool doSub,
                                   const noll_ta_symbol_array * vmap,
                                   noll_uid_array * mmap)
{
  // check inputs
  assert (NULL != sym);

  // TODO: mmap not used at the present time, avoid warning
  if (mmap != NULL)
    return sym;

  switch (sym->label_type)
    {
    case NOLL_TREE_LABEL_ALLOCATED:
      {
        // change the vars field
        noll_uid_array *vars = NULL;
        if (doSub)
          {
            vars = noll_uid_array_new ();
            for (uid_t i = 0; i < noll_vector_size (sym->allocated.vars); i++)
              {
                // formal variable in symbol
                uid_t vi = noll_vector_at (sym->allocated.vars, i);
                // actual parameter symbol
                const noll_ta_symbol_t* si = NULL;
                if (vi < noll_vector_size (vmap))
                  si = noll_vector_at (vmap, vi);
                assert (NULL != si);
                // aliased vars in si
                const noll_uid_array* si_vars = noll_ta_symbol_get_vars (si);
                if ((NULL != si_vars) && 
                    (noll_vector_size (si_vars) >= 1))
                   noll_uid_array_push (vars, noll_vector_at(si_vars,0));
              }
          }
        // TODO: change here markings with the mmap

        const noll_ta_symbol_t *ret_sym =
          noll_ta_symbol_get_unique_allocated (sym->allocated.sels, vars,
                                               sym->allocated.marking);
        if (NULL != vars)
          noll_uid_array_delete (vars);
        return ret_sym;
      }

    case NOLL_TREE_LABEL_ALIASING_VARIABLE:
      {
        // formal variable in symbol
        uid_t vi = sym->alias_var;
        // actual parameter symbol
        const noll_ta_symbol_t* si = NULL;
        if (vi < noll_vector_size (vmap))
          {
            si = noll_vector_at (vmap, vi);
            // aliased vars in si
            const noll_uid_array* si_vars = noll_ta_symbol_get_vars (si);
            if ((NULL != si_vars) && noll_vector_size (si_vars) >= 1)
              {
                const noll_ta_symbol_t *ret_sym =
                noll_ta_symbol_get_unique_aliased_var (noll_vector_at (si_vars,0));
                return ret_sym;
              }
            // formal param mapped to a marking
            const noll_uid_array *si_mark = noll_ta_symbol_get_marking (si);
            if (NULL != si_mark)
              {
                const noll_ta_symbol_t *ret_sym = // TODO: check
                noll_ta_symbol_get_unique_aliased_marking_up_down_fst (si_mark);
                return ret_sym;
              }
          }
        return sym;
      }

    case NOLL_TREE_LABEL_ALIASING_MARKING:
      {
        // TODO: change here with the mmap
        return sym;
      }

    case NOLL_TREE_LABEL_HIGHER_PRED:
      {
        // change the vars field
        noll_uid_array *vars = NULL;
        if (doSub)
          {
            // TODO AN: with the model for allocated
            vars = noll_uid_array_new ();
            for (uid_t i = 0; i < noll_vector_size (sym->allocated.vars); i++)
              {
                // formal variable in symbol
                uid_t vi = noll_vector_at (sym->allocated.vars, i);
                // actual parameter symbol
                const noll_ta_symbol_t* si = NULL;
                if (vi < noll_vector_size (vmap))
                  si = noll_vector_at (vmap, vi);
                assert (NULL != si);
                // aliased vars in si
                const noll_uid_array* si_vars = noll_ta_symbol_get_vars (si);
                assert (NULL != si_vars);
                noll_uid_array_push (vars, noll_vector_at(si_vars,0));
              }
          }
        // TODO: change here markings with the mmap

        const noll_ta_symbol_t *ret_sym =
          noll_ta_symbol_get_unique_higher_pred (sym->higher_pred.pred, vars,
                                                 sym->higher_pred.marking);
        if (NULL != vars)
          noll_uid_array_delete (vars);
        return ret_sym;
      }

    default:
      {
        NOLL_DEBUG ("ERROR: invalid symbol label type!\n");
        assert (false);
      }
    }

  return sym;
}

/*
 * A sound? approximation of the desired result 
 */
const noll_ta_symbol_t *
noll_ta_symbol_get_unique_aliased_symbol (const noll_ta_symbol_t * sym,
                                          const noll_ta_symbol_array * vmap)
{
  const noll_ta_symbol_t *ren_sym =
    noll_ta_symbol_get_unique_renamed (sym, true, vmap, NULL);
  if ((sym->label_type == NOLL_TREE_LABEL_ALLOCATED) || 
      (sym->label_type == NOLL_TREE_LABEL_HIGHER_PRED))
    {
      const noll_uid_array* si_vars = noll_ta_symbol_get_vars (ren_sym);
      if ((NULL != si_vars) && 
          (noll_vector_size (si_vars) >= 1))
        {
          const noll_ta_symbol_t *ret_sym =
            noll_ta_symbol_get_unique_aliased_var (noll_vector_at (si_vars,0));
          return ret_sym;
        }
        // formal param mapped to a marking
        const noll_uid_array* si_mark = noll_ta_symbol_get_marking (ren_sym);
        if (NULL != si_mark)
          {
            const noll_ta_symbol_t *ret_sym = // TODO: check
            noll_ta_symbol_get_unique_aliased_marking_up_down_fst (si_mark);
            return ret_sym;
          }
    }

  return ren_sym;
}
