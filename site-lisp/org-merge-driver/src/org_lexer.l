 /* Org Mode file lexer -*-c-*- */
%{

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

 /* Org Mode lexer */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "doc_elt_util.h"

#include "org_parser.h"
#include "doc_elt.h"
#include "org_heading.h"
#include "org_text.h"
#include "org_property.h"

int yywrap (yyscan_t scanner);
void yyerror (char const  *);

void headline_aoeaoe (org_heading *heading, char *string, size_t len, yyscan_t scanner);

%}

 /* Flex Options */
 /* Generate a reentrant parser */
%option reentrant
%option header-file="org_lexer.h"
%option extra-type="struct extra *"

 /* Rule Start Conditions */
%x heading text property property_skipwhitespace property_value property_finish
%s property_drawer

%% /* Start of rules */

 /*
  * Heading
  * "** Heading blah blah "
  */
 /* start of a heading */
^[*]+" ".*[\n]? {
   debug_msg (LEXER, 4, "heading start\n");

   /* Create a temporary data store */
   TOKEN temp = yyextra->curr_type;
   yyextra->elt = yyextra->curr_elt;

   /* create the new element */
   yyextra->curr_elt =  (doc_elt *) org_heading_create_empty (&org_heading_ops);
   yyextra->curr_type = T_ORG_HEADING;
   org_heading_initversion ((org_heading *)yyextra->curr_elt, yyextra->src);

   /* copy in the data in  */
   char *c = malloc (sizeof (char)*(yyleng));
   strncpy (c, yytext, yyleng);
   org_heading_set_entire_text ((org_heading *)yyextra->curr_elt, c, yyleng, yyextra->src, yyextra->ctxt);

   /* scan the line for the internal values */
   BEGIN (INITIAL);

   /* return the previous element, if there was one */
   if (yyextra->elt != NULL && temp != T_NOTHING)
     {
       debug_msg (LEXER, 3, "element return\n");
       return temp;
     }
}

 /*
  * Text
  *
  * Any paragraph of text, also a catch all for anything without
  * specific rules
  */
 /* start of a plain text segment */
^. {
  BEGIN(text);
  yymore ();
  debug_msg (LEXER, 5, "text start line\n");
}

 /* finish a line */
<text>.*"\n"? {
  debug_msg (LEXER, 5, "text finish line\n");

  TOKEN temp = T_NOTHING;

  /* append this line of text */
  if (yyextra->curr_type != T_ORG_TEXT)
    {
      /* Create a temporary data store */
      temp = yyextra->curr_type;
      yyextra->elt = yyextra->curr_elt;

      debug_msg (LEXER, 5, "text create new\n");
      /* create a new element */
      yyextra->curr_type = T_ORG_TEXT;
      yyextra->curr_elt = (doc_elt *) org_text_create_empty (&org_text_ops);
      org_text_initversion ( (org_text *) yyextra->curr_elt, yyextra->src);
    }

  /* add data to the element */
  size_t size = org_text_get_length ((org_text *)yyextra->curr_elt, yyextra->src);
  char * string = org_text_get_text ((org_text *) yyextra->curr_elt, yyextra->src);
  char * new_string = malloc (sizeof (char) * (size + yyleng));
  strncpy (new_string, string, size);
  strncpy ((new_string + size), yytext, yyleng);
  org_text_set_text((org_text *) yyextra->curr_elt, new_string, size + yyleng, yyextra->src);

  BEGIN(INITIAL);

  /* return the previous element, if there was one */
  if (temp != T_NOTHING && yyextra->elt != NULL)
    {
      debug_msg (LEXER, 3, "element return\n");
      return temp;
    }

  /* Can still match more text for this element */
}

 /* a newline apart of the paragraph */
^"\n" {
  debug_msg (LEXER, 5, "text add newline\n");

  TOKEN temp = T_NOTHING;

  /* append this line of text */
  if (yyextra->curr_type != T_ORG_TEXT)
    {
      /* Create a temporary data store */
      temp = yyextra->curr_type;
      yyextra->elt = yyextra->curr_elt;

      debug_msg (LEXER, 5, "text create new\n");
      /* create a new element */
      yyextra->curr_type = T_ORG_TEXT;
      yyextra->curr_elt = (doc_elt *) org_text_create_empty (&org_text_ops);
      org_text_initversion ( (org_text *) yyextra->curr_elt, yyextra->src);
    }

  /* add data to the element */
  size_t size = org_text_get_length ((org_text *)yyextra->curr_elt, yyextra->src);
  char * string = org_text_get_text ((org_text *) yyextra->curr_elt, yyextra->src);
  char * new_string = malloc (sizeof (char) * (size + yyleng));
  strncpy (new_string, string, size);
  strncpy ((new_string + size), yytext, yyleng);
  org_text_set_text((org_text *) yyextra->curr_elt, new_string, size + yyleng, yyextra->src);

  BEGIN(INITIAL);

  /* return the previous element, if there was one */
  if (temp != T_NOTHING && yyextra->elt != NULL)
    {
      debug_msg (LEXER, 3, "element return\n");
      return temp;
    }
 /* Can still match more text for this element */
}

 /* Properties
  * "  :ID:  1201324054621536421035  "
  *
  * Org mode properties are (key, value) pairs that can apear
  * anywhere.  They will split elements that are currently being
  * defined.  They are recognized as any element that has only
  * whitespace between it and a semicolon surounded key.  Spaces are
  * allewed as apart of the key.
  */
 /*start of a property line, with the tag */
<property_drawer>^" "*":"[^:]*":" {
   debug_msg (LEXER, 3, "property start\n");
   /* Create a temporary data store */
   TOKEN temp = yyextra->curr_type;
   yyextra->elt = yyextra->curr_elt;

   /* create the new element */
   yyextra->curr_elt =  (doc_elt *) org_property_create_empty (&org_property_ops);
   yyextra->curr_type = T_ORG_PROPERTY;
   org_property_initversion ((org_property *)yyextra->curr_elt, yyextra->src);

   org_property_set_key_length ((org_property *)yyextra->curr_elt, yyextra->src, yyleng - 1);
   BEGIN(property_skipwhitespace);
   yymore();

   /* return the previous element, if there was one */
   if (yyextra->elt != NULL && temp != T_NOTHING)
     {
       debug_msg (LEXER, 3, "property element return\n");
       return temp;
     }
}

 /* skip white space */
<property_skipwhitespace>[ \t]* {
  /* store the offset to the start of the value */
  org_property_set_value_length ((org_property *)yyextra->curr_elt, yyextra->src,
				 yyleng);
  yymore();
  BEGIN(property_finish);
}

 /* Finish the property line */
<property_finish>.*[\n]? {
  /* Set the property text.
   * At this point, the values of the property look like this:
   * "   :key:     value text    "
   *        ^      ^            ^
   *        \------|------------|-> key length
   *               \------------|-> value length
   *                            \-> yylen
   */
  //debug_msg ("Properties");

  /* create the new string */
  char * new_text = malloc (sizeof (char) * (yyleng));
  strncpy (new_text, yytext, yyleng);

  size_t key_length = org_property_get_key_length ((org_property *)yyextra->curr_elt,
						   yyextra->src);

  size_t value_length = org_property_get_value_length ((org_property *)yyextra->curr_elt,
						     yyextra->src);

  org_property_set_text((org_property *) yyextra->curr_elt, yyextra->src,
		        new_text, yyleng);

  org_property_set_value_string ((org_property *)yyextra->curr_elt, yyextra->src,
				  new_text + value_length);

  /* do a backward seach to find the end of the string */
  size_t pos = yyleng-1;
  while (pos > 0)
    {
      if (new_text[pos] != ' ' && new_text[pos] != '\t')
	break;
      pos--;
    }
  value_length = pos - value_length;
  assert (value_length >= 0);
  org_property_set_value_length ((org_property *)yyextra->curr_elt,
				 yyextra->src, value_length);

   /* do a backword search to find the start of the string.
    * set the key substring, do not include the markup ':'
    */
  pos = key_length;
   while (pos > 0)
     {
       if (new_text[pos - 1] == ':')
	 break;

       pos--;
     }
  org_property_set_key_string ((org_property *)yyextra->curr_elt, yyextra->src,
			       new_text + pos);

  org_property_set_key_length ((org_property *)yyextra->curr_elt, yyextra->src, key_length - pos);

  if (LEXER_PRINTLEVEL == 5)
    {

      fwrite ( org_property_get_key_string ((org_property *)yyextra->curr_elt, yyextra->src),
               sizeof (char) , org_property_get_key_length ((org_property *)yyextra->curr_elt,
                                                            yyextra->src),
               stderr);

      fwrite ( org_property_get_value_string ((org_property *)yyextra->curr_elt, yyextra->src),
               sizeof (char) , org_property_get_value_length ((org_property *)yyextra->curr_elt,
                                                              yyextra->src),
               stderr);
    }

  /* return the property */
  debug_msg (LEXER, 3, "Property Return\n");
  BEGIN(property_drawer);

  /* set the last element to nothing */
  yyextra->curr_type = T_NOTHING;
  yyextra->elt = yyextra->curr_elt;
  yyextra->curr_elt = NULL;

  return T_ORG_PROPERTY;
}

 /* Drawer Parser
  * ":BEGIN:"
  * ":END:"
  *
  * A fully recursive element.  They can start on any line.  Since the
  * syntax is recursive, seperate tokens are needed for both the start
  * and end of a drawer.
  *
  * Current drawer support is just to create a property with no key.
  */
 /* Begin a drawer */
^[ ]*":PROPERTIES:"[ ]*[\n]? {
   debug_msg (LEXER, 3, "PROPERTIES drawer start\n");
   /* Create a temporary data store */
   TOKEN temp = yyextra->curr_type;
   yyextra->elt = yyextra->curr_elt;

   /* create the new element */
   yyextra->curr_elt =  (doc_elt *) org_property_create_empty (&org_property_ops);
   yyextra->curr_type = T_ORG_PROPERTY;
   org_property_initversion ((org_property *)yyextra->curr_elt, yyextra->src);

   /* set the line text */
   char * new_text = malloc (sizeof (char) * (yyleng));
   strncpy (new_text, yytext, yyleng);

   org_property_set_text((org_property *) yyextra->curr_elt, yyextra->src,
			 new_text, yyleng);

   /* do a backword search to find the start of the string.
    * set the key substring, do not include the markup ':'
    */
  int pos = yyleng - 1;
   while (pos >= 0)
     {
       if (new_text[pos] == ':')
	 break;

       pos--;
     }

   /* set the key to the value of the line */
   org_property_set_key ((org_property *)yyextra->curr_elt, yyextra->src, new_text+pos-10, 10);

   /* set the value to 0 */
   org_property_set_value ((org_property *)yyextra->curr_elt, yyextra->src, NULL, 0);

   /* mark that we are currently in a property drawer */
   BEGIN(property_drawer);

   /* return the previous element, if there was one */
   if (yyextra->elt != NULL && temp != T_NOTHING)
     {
       debug_msg (LEXER, 3, "drawer element return\n");
       return temp;
     }
}

 /* Finish A drawer. */
<property_drawer>^[ ]*":END:"[ ]*"\n"? {
   debug_msg (LEXER, 3, "END Drawer\n");

   /* Create a temporary data store */
   TOKEN temp = yyextra->curr_type;
   yyextra->elt = yyextra->curr_elt;

   /* create the new element */
   yyextra->curr_elt =  (doc_elt *) org_property_create_empty (&org_property_ops);
   yyextra->curr_type = T_ORG_PROPERTY;
   org_property_initversion ((org_property *)yyextra->curr_elt, yyextra->src);

   /* set the line text */
   char * new_text = malloc (sizeof (char) * (yyleng));
   strncpy (new_text, yytext, yyleng);

   org_property_set_text((org_property *) yyextra->curr_elt, yyextra->src,
			 new_text, yyleng);

   /* do a backword search to find the start of the string.
    * set the key substring, do not include the markup ':'
    */
   int pos = yyleng - 1;
   while (pos >= 0)
     {
       if (new_text[pos] == ':')
	 break;

       pos--;
     }

   /* set the key to the value of the line */
   org_property_set_key ((org_property *)yyextra->curr_elt, yyextra->src, new_text+pos-3, 3);

   /* set the value to 0 */
   org_property_set_value ((org_property *)yyextra->curr_elt, yyextra->src, NULL, 0);

   /* mark that we are currently in a property drawer */

   BEGIN(INITIAL);

   /* return the previous element, if there was one */
   if (yyextra->elt != NULL && temp != T_NOTHING)
     {
       debug_msg (LEXER, 3, "drawer element return\n");
       return temp;
     }
}

 /*
  * End Of File Wrap up
  *
  * Close the Lexer and wrap up the last element
  */
<<EOF>> {
  debug_msg (LEXER, 5, "EOF\n");
  if (yyextra->curr_elt != NULL)
    {
      /* If there is an element beintg defined, return it */
      yyextra->elt = yyextra->curr_elt;
      yyextra->curr_elt = NULL;
      debug_msg (LEXER, 5, "EOF return element\n");
      return yyextra->curr_type;
    }
  else
    {
      debug_msg (LEXER, 4, "EOF terminate lexer\n");
      yyterminate();
    }
}

%%

int
yywrap (yyscan_t scanner)
{
  /* Tell lex to stop processing at the end of a file */
  return 1;
}

bool
is_todo_state (substr *s)
{
  return false;
}

/**
 * @brief Parse a titile line, setting all the propper substrings
 */
static void
parse_title_line (org_heading * h, char * line, size_t len)
{
  int i = 0;

  size_t last_len = 0;
  substr next_substr;

  /* set all the substrings to len 0 */

  /* skip all starting blank space*/
  while ( i < len)
    {
      if (line[i] != ' ')
        break;
    }

  /* get the next word */
  next_substr.string = (line + i);
  last_len = i;
  while ( i < len)
    {
      if (line[i] == ' ')
        break;
    }
  next_substr.length = i - last_len;

  /* check what the last word was */
  if (is_todo_state (&next_substr))
    {
      // implement this
      //h->todo = s;
      /* get the next word */
      next_substr.string = (line + i);
      last_len = i;
      while ( i < len)
        {
          if (line[i] == ' ')
            break;
        }
      next_substr.length = i - last_len;
    }

  /* assume that the next substr is either text or :tags: */
  bool exit = false;
  while ( i < len)
    {
      if (next_substr.string[0] == ':')
	{
	  /* grab all characters untill there is no tag */
	}
      else
	{
	  /* grab all the characters, assuming its heading text */
	}

      /* get the next word */
      next_substr.string = (line + len);
      last_len = len;
      while ( i < len)
	{
	  if (line[i] != ' ')
	    break;
	}

      next_substr.length = len - last_len;
    }
}
