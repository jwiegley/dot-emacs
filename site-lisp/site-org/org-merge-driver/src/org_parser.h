/**
 * @file org_parser.h
 * @brief Parses document elements into a document structure
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

#ifndef ORG_PARSER_H
#define ORG_PARSER_H

#include <stdio.h>
//#include "org_lexer.h"

#include "org_document.h"
#include "parse_ctxt.h"

struct doc_elt;
typedef struct doc_elt doc_elt;



/**
 * @file org_parser.h
 * @brief Implement an Org mode file parser.
 */

/**
 * @brief parse a FILE stream into a doc_tree.
 */
org_document *org_parse_file_stream (FILE * file, doc_src src, parse_ctxt *ctxt);

/**
 * Token declaration for the lexer & parser.
 */
typedef enum TOKEN
  {
    T_QUIT = 0,         /* signal to quit from the lexer */
    T_NOTHING,          /* return nothing (no element) */
    T_ORG_HEADING,      /* a heading */
    T_ORG_TEXT,         /* regular text under a heading */
    T_ORG_PROPERTY,     /* a property */
    T_ORG_DRAWER_BEGIN, /* beginning of a drawer */
    T_ORG_DRAWER_END    /* end of a drawer */
  } TOKEN;

struct extra
{
  doc_elt    *elt;
  doc_elt    *curr_elt;
  TOKEN       curr_type;
  void       *data;
  doc_src     src;
  parse_ctxt *ctxt;
};
#endif
