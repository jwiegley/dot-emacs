/**
 * @file merge_ctxt.h
 *
 * Defines a context structure containing information used during the
 * matching and merging process, along with all associated functions.
 */

/*
 * This program is free software: you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either vers* ion 3 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#ifndef MERGE_CTXT_H
#define MERGE_CTXT_H

typedef enum merge_strategy {
  NO_STRATEGY,
  GLOBAL_SEARCH_MERGE,
  LOCAL_LIST_MERGE,
  LOCAL_SEARCH_MERGE
} merge_strategy;

struct gl_list_impl;
typedef struct gl_list_impl * gl_list_t;

struct smerger;
typedef struct smerger smerger;

typedef struct merge_ctxt
{
  smerger *global_smerger;
  gl_list_t priorities;
  merge_strategy strategy;
} merge_ctxt;

/**
 * @brief Initialize a merge context.
 */
void merge_ctxt_init (merge_ctxt *ctxt);

/**
 * @brief Free a merge context and all it's data.
 */
void merge_ctxt_free (merge_ctxt *ctxt);

/**
 * @brief Set any unset values to their defaults.
 */
void merge_ctxt_set_defaults (merge_ctxt *ctxt);

#endif
