/**
 * @file parse_ctxt.h
 *
 * Defines a context storing state while parsing, and all it's
 * associated functions.  The parse context also stores configuration
 * variables controlling the parse behaviour of the lexer, parser, and
 * the doc_elts.
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

#ifndef PARSE_CTXT
#define PARSE_CTXT

struct gl_list_impl;
typedef struct gl_list_impl * gl_list_t;

typedef struct parse_ctxt
{
  gl_list_t todo_states;
  size_t current_level;
} parse_ctxt;

/**
 * @brief Initialize a parse context.
 */
void parse_ctxt_init (parse_ctxt *ctxt);

/**
 * @brief Set any unset data to a default value.
 */
void parse_ctxt_set_defaults (parse_ctxt *ctxt);

#endif
