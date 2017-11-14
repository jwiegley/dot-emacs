/**
 * @file print_ctxt.h
 *
 * Defines a context used during element printing and all it's
 * associated functions.
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

#ifndef PRINT_CTXT_H
#define PRINT_CTXT_H

#include "stdbool.h"

/**
 * @brief A context for the current printing mode.
 *
 * It acts as a request to print only certain information.  It does
 * not imply what side of a conflict we are printing.
 */
typedef enum print_state
  {
    print_merged,
    print_remote,
    print_local,
    print_ancestor
  } print_state;

/**
 * @brief The current state of conflict markers.
 */
typedef enum conflict_state
  {
    no_conflict = 0,
    local_side  = 1,
    remote_side = 2
  } conflict_state;

/**
 * @brief A context for printing doc_elt's in a tree.
 */
typedef struct print_ctxt
{
  int            depth;              /*< The current depth in a document tree */
  size_t         current_level;      /*< the current level of a document      */
  size_t         rmargin;            /*< The column of the doc's right margin */
  size_t         tab_width;          /*< The column width of a tab character  */
  bool           use_tabs;           /*< Should generated output use tabs?    */
  print_state    print_state;        /*< the current printing mode            */
  bool           nested_conflicts;   /*< if there are nested conflicts        */
  conflict_state structure_conflict; /*< the current state of conflicts       */
  conflict_state content_conflict;   /*< the current state of conflicts       */
  conflict_state movement_conflict;  /*< the current state of conflict        */
  bool           conflict_occurred;  /*< IF a conflict occured                */
} print_ctxt;

/**
 * @brief Create and initialize a print context.
 */
print_ctxt* print_ctxt_create_empty (void);

/**
 * @brief Initialize a print_ctxt.
 */
void print_ctxt_init (print_ctxt *ctxt);

#endif
