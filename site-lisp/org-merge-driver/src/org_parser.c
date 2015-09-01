/**
 * @file org_parser.c
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

#include <stdio.h>
#include <assert.h>
#include <stdlib.h>

#include "org_parser.h"
#include "org_lexer.h"

#include "doc_elt.h"
#include "org_document.h"
#include "org_heading.h"
#include "org_text.h"
#include "org_property.h"

static void rec_parse_document (yyscan_t scanner, org_document *this, parse_ctxt *ctxt);

static doc_elt *rec_parse_heading(yyscan_t scanner, org_heading *dc, int level, parse_ctxt *ctxt);

/* This parser needs some serious love.  Right now it assumes that the
 * only type of elements which can be nested are headings.
 */
org_document *
org_parse_file_stream (FILE * file, doc_src src, parse_ctxt *ctxt)
{
  assert (file);
  debug_msg (PARSER, 3, "Parsing File\n");

  /* Initialize flex data structures */
  yyscan_t scanner;
  int err = 0;
  err = yylex_init (&scanner);

  if (err == ENOMEM)
    {
      /* Memory allocation error, abort execution. */
      return NULL;
    }
  else if (err == EINVAL)
    {
      /* Invalid yylex_init argument, abort execution. */
      return NULL;
    }

  /* Set the input stream of the lexer */
  yyset_in (file, scanner);

  /* set up the extra field */
  struct extra e;
  e.elt = NULL;
  e.curr_elt = NULL;
  e.curr_type = T_NOTHING;
  e.src = src;
  e.ctxt = ctxt;
  yyset_extra (&e, scanner);

  /* Initialize doc_tree */
  org_document *document = org_document_create_empty (&org_document_ops);

  /* call the recursive function */
  rec_parse_document (scanner, document, ctxt);

  /* Destroy scanner */
  yylex_destroy (scanner);
  debug_msg (PARSER, 3, "Finished Parsing File\n");
  return document;
}

static void
rec_parse_document (yyscan_t scanner, org_document *this, parse_ctxt *ctxt)
{
  /* 1. get the text element
   * 2 check type
   * 2.1 Non children type: add it to the list of elements
   * 2.2 Children type, check the level
   * 2.2.1 If same level, or higher, return the node
   * 2.2.2 If its a lower level, call this function on it
   */

  bool exit = false;
  doc_elt * ret = 0;

  /* Get the next element from the scanner */
  TOKEN tok = yylex (scanner);
  doc_elt * elt = yyget_extra (scanner)->elt;
  doc_src src = yyget_extra (scanner) -> src;

  /* Parse the file */
  while(!exit)
    {
      ctxt->current_level = 0;

      if (tok == T_NOTHING)
	{
	  debug_msg (PARSER, 3, "Got Nothing\n");
	  /* do nothing */
	}
      else if (tok == T_ORG_HEADING)
	{
	  int next_level = org_heading_get_level ((org_heading *) elt, src);
	  if (next_level <= 0)
	    {
	      debug_msg (PARSER, 3, "heading with level <= 0\n");
	      assert (0);
	      return;
	    }
	  else
	    {
	      debug_msg (PARSER, 3, "Adding Sub-Heading\n");
	      /* next level is at least more than this one */
	      org_document_add_heading_last (this, src, (org_heading *) elt);
              org_heading_set_parse_ctxt ((org_heading *) elt, src, ctxt);

	      elt = (doc_elt *)
		rec_parse_heading(scanner, (org_heading *) elt, next_level, ctxt);
	    }
	}
      else if (tok == T_ORG_TEXT || tok == T_ORG_PROPERTY)
	{
	  debug_msg (PARSER, 3, "Got Text\n");

	  org_document_add_text_last (this, src, (org_text *) elt);

	  /* Get the next element from the scanner */
	  tok = yylex (scanner);
	  elt = yyget_extra (scanner) -> elt;
	}
      else
	{
	  debug_msg (PARSER, 2, "Got unknown element, skipping");
	  /* Get the next element from the scanner */
	  tok = yylex (scanner);
	  elt = yyget_extra (scanner) -> elt;
	}

      if (tok == T_QUIT || elt == NULL)
	{
	  /* break if at the end of the file */
	  ret = NULL;
	  exit = true;
	  tok = T_QUIT;
	  elt = NULL;
	}
    }
  return;
}

static doc_elt *
rec_parse_heading(yyscan_t scanner, org_heading *this, int this_level, parse_ctxt *ctxt)
{
  /* 1. get the text element
   * 2 check type
   * 2.1 Non children type: add it to the list of elements
   * 2.2 Children type, check the level
   * 2.2.1 If same level, or higher, return the node
   * 2.2.2 If its a lower level, call this function on it
   */

  bool exit = false;
  doc_elt * ret = 0;

  /* Get the next element from the scanner */
  TOKEN tok = yylex (scanner);
  doc_elt * elt = yyget_extra (scanner)->elt;
  doc_src src = yyget_extra (scanner) -> src;

  /* Parse the file */
  while(!exit)
    {

      ctxt->current_level = this_level;

      if (tok == T_NOTHING)
	{
	  debug_msg (PARSER, 3, "Got Nothing\n");
	  /* do nothing */
	}
      else if (tok == T_ORG_HEADING)
	{
	  int next_level = org_heading_get_level ((org_heading *)elt, src);
	  //int next_level = 1;
	  if (next_level <= this_level)
	    {
	      debug_msg (PARSER, 4, "-return heading\n");
	      return elt;
	    }
	  else
	    {
	      debug_msg (PARSER, 3, "Adding Sub-Heading\n");
	      /* next level is at least more than this one */
	      org_heading_add_subheading_last (this, src, elt);
              org_heading_set_parse_ctxt ((org_heading *) elt, src, ctxt);
	      elt =
		rec_parse_heading(scanner, (org_heading *)elt, next_level, ctxt);
	    }
	}
      else if (tok == T_ORG_TEXT)
	{
	  debug_msg (PARSER, 3, "Got Text\n");

	  org_heading_add_subtext_last (this, src, elt);
	  /* Get the next element from the scanner */
	  tok = yylex (scanner);
	  elt = yyget_extra (scanner)-> elt;
	}
      else if (tok == T_ORG_PROPERTY)
	{
	  debug_msg (PARSER, 3, "Got property\n");
	  /* if the property was a UID, add it to the heading.  Only
	   * recognize the first ID below a heading */
	  if (doc_elt_get_key((doc_elt *)this)->length == 0)
	    {
	      org_property *p = (org_property *) elt;
	      char *key = org_property_get_key_string (p, src);
	      size_t length = org_property_get_key_length (p, src);
	      if (length == 2) /* length of ID */
		{
		  if (strncmp (key, "id", 2) == 0
		      || strncmp (key, "ID", 2) == 0)
		    {
                      debug_msg (PARSER, 3, "Setting heading key to property");
		      org_heading_set_key (this, org_property_get_value_string (p, src),
                                                 org_property_get_value_length (p, src));
		    }
		}
	    }

	  /* add the property as a text element */
	  org_heading_add_subtext_last (this, src, elt);

	  /* Get the next element from the scanner */
	  tok = yylex (scanner);
	  elt = yyget_extra (scanner)-> elt;
	}
    else
	{
	  debug_msg (PARSER, 2, "Got unknown element, skipping");
	  /* Get the next element from the scanner */
	  tok = yylex (scanner);
	  elt = yyget_extra (scanner) -> elt;
	}

      if (tok == T_QUIT || elt == NULL)
	{
	  /* break if at the end of the file */
	  ret = NULL;
	  exit = true;
	  tok = T_QUIT;
	  elt = NULL;
	}
    }
  return ret;
}
