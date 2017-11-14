/**
 * @file print.h
 * @brief the print library
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

#ifndef PRINT_H
#define PRINT_H
#include "doc_stream.h"

#include "print_ctxt.h"

/**
 * @todo Find a way to deal with advancing the print mode with the
 * conflict markers
 */

/**
 * @brief enter a certain part of a structural conflict.
 *
 * This function enters a structural conflict.  If it is already in
 * the correct state, it will do nothing.  It will wrap up any movement
 * conflicts before switching
 */
void enter_structural_conflict (print_ctxt *ctxt, conflict_state state,
				char* msg, doc_stream *out);

/**
 * @brief enter a certain part of a movement conflict.
 *
 * This function enters a structural conflict. If it is already in the
 * correct state, it will do nothing. It will wrap up any content
 * conflicts before switching. Movement Conflicts are assumed to be
 * nestable between parents and children. It is up to the parent to
 * ensure that the print ctxt is set up for this.
 */
void enter_movement_conflict (print_ctxt *ctxt, conflict_state state,
                         char* msg, doc_stream *out);

/**
 * @brief enter a certain part of a content conflict.
 *
 * This function enters a content conflict.  If it is already in the
 * correct state, it will do nothing.
 */
void enter_content_conflict (print_ctxt *ctxt, conflict_state state,
			     char* msg, doc_stream *out);

static inline conflict_state print_ctxt_get_content_state (print_ctxt *ctxt);

static inline conflict_state print_ctxt_get_structure_state (print_ctxt *ctxt);

static inline conflict_state print_ctxt_get_movement_state (print_ctxt *ctxt);
static inline void print_ctxt_set_movement_state (print_ctxt *ctxt, conflict_state state);

/*
 * Implementation
 */

static inline conflict_state
print_ctxt_get_content_state (print_ctxt *ctxt)
{
  return ctxt->structure_conflict;
}

static inline conflict_state
print_ctxt_get_structure_state (print_ctxt *ctxt)
{
  return ctxt->content_conflict;
}

static inline conflict_state
print_ctxt_get_movement_state (print_ctxt *ctxt)
{
  return ctxt->movement_conflict;
}

static inline void
print_ctxt_set_movement_state (print_ctxt *ctxt, conflict_state state)
{
  ctxt->movement_conflict = state;
}

#endif /* PRINT_H */
