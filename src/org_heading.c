/**
 * @file org_heading.c
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


#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#include "debug.h"

#include "config.h"
#include "gl_array_list.h"
#include "gl_list.h"

#include "print.h"

#include "doc_elt.h"
#include "doc_elt_ops.h"
#include "doc_elt_util.h"
#include "doc_ref.h"
#include "org_heading.h"
#include "org_text.h"


/* Forward Declarations */
/* org_heading_data */
typedef struct org_heading_data org_heading_data;
static void org_heading_data_free (org_heading_data *self);
static org_heading_data *org_heading_data_create_empty ();
static bool org_heading_content_isupdated (org_heading *heading, size_t data_index);

static bool org_heading_subelts_isupdated (org_heading *heading);

static bool compare_body_text (org_heading_data *a_data,
			       org_heading_data *b_data, merge_ctxt *ctxt);

static size_t merge_tags (substr anc_str, substr loc_str, substr rem_sub,
			  size_t curr_col, bool gen_ws, print_ctxt *ctxt,
			  doc_stream *out);

static void print_LU_RU (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_LU_RD (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_LD_RU (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_LD_RD (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_LI_RI (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_LI_RX (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_LX_RI (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_LX_RX (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);

static void print_LR (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_L (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static void print_R (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);

static void print (org_heading *h, size_t index, print_ctxt *ctxt, doc_stream *out);
static int print_stars (org_heading *h, size_t index, print_ctxt *ctxt, doc_stream *out);
static void print_subelts (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);

/* merging helpers */
static void org_movement_merge_print (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);

/* property */
typedef struct property property;

/* Declaration of org_element operations table */
static doc_elt_ops_print     org_heading_print_op;
static doc_elt_ops_isrelated org_heading_isrelated_op;
static doc_elt_ops_compare   org_heading_compare_op;
static doc_elt_ops_merge     org_heading_merge_op;
static doc_elt_ops_isupdated org_heading_isupdated_op;
static doc_elt_ops_note_delete org_heading_note_delete;
static doc_elt_ops_note_insert org_heading_note_insert;
static doc_elt_ops_get_key     org_heading_get_key;

doc_elt_ops org_heading_ops = {
  /* printing */
  .print         = &org_heading_print_op,

  /* comparing */
  .isrelated     = &org_heading_isrelated_op,
  .compare       = &org_heading_compare_op,

  /* merging */
  .merge         = &org_heading_merge_op,
  .isupdated     = &org_heading_isupdated_op,
  .note_delete   = &org_heading_note_delete,
  .note_insert   = &org_heading_note_insert,

  /* Global mapping */
  .get_key       = &org_heading_get_key
};

/* Core org_heading struct */
typedef struct org_heading_data
{
  int       level;        /*< The heading level, number of stars. */
  int       rel_level;    /*< The relative heading level */
  substr    entire_text;  /*< The complete heading text. No stars. */
  substr    lead_ws;      /*< Whitespace between stars and content. */
  substr    todo;         /*< The todo state substring */
  substr    body_text;    /*< The basic heading text */
  substr    body_ws;      /*< Whitespace between the body and any tags.  */
  substr    tags_str;     /*< The tags, as a substring rather than a list. */
  substr    post_text;    /*< Any text after tags. */
  substr    linebreak;    /*< Any linebreaks. */

  bool global_search_merge;
  bool local_list_merge;

  property *uid;
} org_heading_data;

/* merged org_heading struct */
typedef struct org_heading
{
  doc_elt           elt;          /*< The element interface. */
  org_heading_data* data[3];      /*< The data for each elt version. */
  bool              isupdated[3]; /*< Indicates if a corresponding data entry is updated. */
  gl_list_t         subtext;      /*< A list of children text elements. */
  gl_list_t         subheadings;  /*< A list of children heading elements. */
  doc_key           key;
  doc_ref          *ref;
} org_heading;

/**
 * Property
 */
typedef struct property
{
  substr string; /*< A string representation of the entire line. */
  substr key;    /*< The property key, a substring. */
  substr value;  /*< The property value, a substring. */
} property;

/* Constructor, Destructor */
org_heading *
org_heading_create_empty (doc_elt_ops *elt_ops)
{
  org_heading *h = calloc (1, sizeof (org_heading));
  doc_elt_set_type ((doc_elt *)h, ORG_HEADING);
  doc_elt_set_ops ((doc_elt *)h, elt_ops);
  h->subheadings = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, NULL, NULL, true);
  h->subtext     = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, NULL, NULL, true);
  return h;
}

void
org_heading_free (org_heading *self)
{
  /**
   * @todo Implement org_heading_free.
   */
  free (self);
}

void
org_heading_initversion (org_heading *heading, doc_src src)
{
  heading->data[srctoindex(src)] = org_heading_data_create_empty();
  return;
}

bool
org_heading_containsversion (org_heading *heading, doc_src src)
{
  return (heading->data[srctoindex(src)] != NULL);
}

static org_heading_data *
org_heading_data_create_empty ()
{
  org_heading_data *data = calloc (1, sizeof (org_heading_data));
  return data;
}

static void
org_heading_data_free (org_heading_data *self)
{
  free (self);
}

/* Adding sub elements */
void
org_heading_add_subtext_last (org_heading *heading, doc_src src, doc_elt *text)
{
  /* wrap the element in a doc_ref, and add it to the list */
  doc_ref *ref = doc_ref_create_empty ();
  doc_ref_set_src (ref, src);
  doc_ref_set_elt (ref, (doc_elt *) text);
  assert (heading->ref != NULL);
  doc_ref_set_parent (ref, heading->ref);
  /**
   * @TODO make text elements honour movement
   */
  gl_list_nx_add_last (heading->subtext, ref);
  return;
}

void
org_heading_add_subheading_last (org_heading *heading, doc_src src, doc_elt *subheading)
{
  /* wrap the element in a doc_ref, and add it to the list */
  doc_ref *ref = doc_ref_create_empty ();
  doc_ref_add_src (ref, src);
  doc_ref_set_elt (ref,  subheading);
  assert (heading->ref != NULL);
  doc_ref_set_parent (ref, heading->ref);
  org_heading_set_doc_ref ((org_heading *)subheading, ref);
  gl_list_nx_add_last (heading->subheadings, ref);
  return;
}

doc_ref*
org_heading_get_doc_ref (org_heading *heading)
{
  return heading->ref;
}

void org_heading_set_doc_ref (org_heading *heading, doc_ref *ref)
{
  heading->ref = ref;
  return;
}

/**
 * This function is called when an org_heading is parseded, and placed
 * into a document tree.  This is called after org_heading_
 */
void
org_heading_set_parse_ctxt (org_heading *heading, doc_src src, parse_ctxt *ctxt)
{
  /* Set the relative level of the heading.  Use the final context of
   * this heading, and it's parsed absolute heading level, to
   * determine
   */
  size_t index = srctoindex (src);
  heading->data[index]->rel_level = (heading->data[index]->level
                                     - ctxt->current_level);

  return;
 }

/**
 * This function is called by the parser.  Set entire text is a subparser
 */
void
org_heading_set_entire_text (org_heading *heading, char *string, int length,
			     doc_src src, parse_ctxt *ctxt)
{

  /* Set the entire line of a heading.
   * The heading will parse the line, setting up substrings and extracting tags.
   *
   * Heading String Format
   * ***    TODO   [#A]   Heading Body Text [%] [/] <>        :TAG1:TAG2: etc etc etc\n
   * |  |   |   |  |                                  |       |          |           |
   * 0  1   2   3  4                                  5       6          7           8
   *
   * 0. Stars
   * 1. pre_ws
   * 2. todo
   * 3,4. body_text
   * 5. body_ws
   * 6. tags
   * 7. post_text
   * 7. linebreak
   */

  size_t index = srctoindex(src);

  heading->data[index]->entire_text.string = string;
  heading->data[index]->entire_text.length = length;

  size_t i = 0;
  size_t count = 0;       /* Used to count the length of a token. */
  size_t lbound = 0;      /* Lower bound, inclusive */
  size_t ubound = length; /* Upper bound, exclusive */

  /* Parse stars:
   * Count the lead stars.
   * Store the stars as an integer.
   */
  for (count = 0; (lbound + count) < ubound; count++)
    {
      if (string[lbound + count] != '*')
	{
	  break;
	}
    }
  heading->data[index]->level = (count);
  heading->data[index]->rel_level = (count - ctxt->current_level);

  lbound = lbound + count;

  debug_msg (ORG_HEADING, 3, "Parse ABS LVL=%d, REL LVL=%d\n",
             heading->data[index]->level,
             heading->data[index]->rel_level);

  /* Parse lead_whitespace:
   * This is the whitespace between the stars and heading.
   * Store it as a substring.
   */
  for (count = 0; count < ubound - lbound; count++)
    {
      if (!iswhitespace (string[lbound + count]))
	{
	  break;
	}
    }
  heading->data[index]->lead_ws.string = string + lbound;
  heading->data[index]->lead_ws.length = count;
  lbound = lbound + count;

  /* Parse TODO State:
   * Read in the first word of the heading.
   * If it is a TODO keyword:
   *   Set the TODO field of data,
   *   Increment lbound by the length of the todo.
   * Otherwise do nothing.
   */
  for (count = 0; (lbound + count) < ubound; count++)
    {
      if (iswhitespace (string[lbound + count]))
	{
	  break;
	}
    }
  if (istodo (string + lbound, count, ctxt))
    {
      heading->data[index]->todo.string = string + lbound;
      heading->data[index]->todo.length = count;
      lbound = lbound + count;
    }
  else
    {
      heading->data[index]->todo.string = NULL;
      heading->data[index]->todo.length = 0;
    }


  /* Scan trailing linebreaks
   * Scan right to left.
   */
  for (count = 0; count < (ubound - lbound); count++)
    {
      if (!islinebreak (string[ubound - count - 1]))
	{
	  break;
	}
    }
  heading->data[index]->linebreak.string = string + ubound - count;
  heading->data[index]->linebreak.length = count;
  ubound = ubound - count;

  /* Parse Tags:
   * Scan right to left.
   * Skip trailing newline characters,
   *   These are placed in the post-text string.
   * Scan for the first tag.
   *   Any text to the right of the tags is placed in the post_text.
   * Only the leftmost tags list is considered
   *   Any text to the left  of the tags is placed in the body_text.
   * The spacing between tags and body_text is not stored.
   *   It is calculated if any
   */
  size_t tags_ubound = ubound;  /* The upper bound of all tags.     */
  size_t tags_lbound = ubound;  /* The lower bound of all tags.     */

  bool foundtags = false;
  bool done = false;

  for (i = 0; i < (ubound - lbound); i++)
    {
      if (string [ubound - i - 1] == ':')
	{
	  debug_msg (DOC_ELT, 5, "Found first colon, at %d\n", ubound - i - 1);

	  if (foundtags = false)
	    {
	      tags_ubound = ubound - i;
	      debug_msg (DOC_ELT, 5, "Setting  tags_ubound =%d\n", tags_ubound);
	    }
	  int j;
	  for (j = 2; j < (tags_ubound - lbound); j++)
	    {
	      if (iswhitespace (string[tags_ubound - j]))
		{
		  debug_msg (DOC_ELT, 5, "Found whitespace at %d, tagsfound=%d\n",
			     tags_ubound - j - 1, foundtags);

                  if (!foundtags)
                    i += (j+1);

		  break;
		}
	      else if (string[tags_ubound - j] == ':')
		{

                  debug_msg (DOC_ELT, 5, "Found tag\n");
                  foundtags = true;
                  tags_lbound = tags_ubound - j;
                  debug_msg (DOC_ELT, 5,
                             "tags_lbound = %d; tags_ubound = %d\n",
                             tags_lbound, tags_ubound);
		}
              else
                {
                  debug_msg (DOC_ELT, 5,
                             "not all tags found\n",
                             tags_lbound, tags_ubound);
                  foundtags = false;
                }
	    }
	  if (foundtags)
	    {
	      break;
	    }
	}
    }

 if (foundtags)
   {
     heading->data[index]->tags_str.string = string + tags_lbound;
     heading->data[index]->tags_str.length = tags_ubound - tags_lbound;
   }
 else /* reset the ubound and lbound if no tags were found */
   {
     tags_ubound = ubound;
     tags_lbound = ubound;
   }

  /*
   * The post_text is all text between the linebreak and tags.
   */

  heading->data[index]->post_text.string = string + tags_ubound;
  heading->data[index]->post_text.length = ubound - tags_ubound;

  ubound = tags_lbound;

  /* Store the whitespace between body_text and tags as body_ws */
  int l = lbound;
  int u = lbound;

  for (i = lbound; i < tags_lbound; i++)
    {
      if (iswhitespace (string[i]))
	{
	  int j;
	  bool foundwhitespace = true;
	  for (j = i; j < tags_lbound; j++)
	    {
	      if (!iswhitespace (string[j]))
		{
		  i = j;
		  foundwhitespace = false;
		  break;
		}
	    }
	  if (foundwhitespace)
	    {
	      break;
	    }
	}
    }

  /* The trailing body_text whitespace will be through the
   * range [i .. tags_lbound).
   */
  heading->data[index]->body_text.string = string + lbound;
  heading->data[index]->body_text.length = i - lbound;
  heading->data[index]->body_ws.string = string + i;
  heading->data[index]->body_ws.length = tags_lbound - i;
  return;
}


int
org_heading_get_level (org_heading *heading, doc_src src)
{
  int index = srctoindex (src);
  return heading->data[index]->level;
}

/*
 * doc_elt interface
 */

/**
 * Test if two headings have the same title.  Compare the body_text of
 * both headings, ignoring cookies and whitespace.
 *
 * Essentially, if two headings have the same words, then they
 * related, regardless of spaces, cookies, tags, & todo state.
 */
static bool
org_heading_isrelated_op (doc_ref *a_ref, doc_ref *b_ref, merge_ctxt *ctxt)
{
  /* isrelated is used by various matching algorithms to see if the
   * elements stored at two refs are related.  Two elements are
   * related if they represent different versions of the same
   * elements.
   *
   * Two headings are the same if they share a key.  If neither has a
   * key, the body text of the heading is used.
   */

  doc_elt *elt_a = doc_ref_get_elt (a_ref);
  doc_elt *elt_b = doc_ref_get_elt (b_ref);

  bool isrelated = false;

  /* Before we can compare the elements as headings, we must make sure
   * that both are, in fact, actually headings.  For this function to
   * be called, one element is expected to be a heading, the other may
   * or may not be.  This isrelated operation needs both elements to
   * be headings, and will return false if they are not.
   */
  if ((doc_elt_get_type (elt_a) == ORG_HEADING) &&
      (doc_elt_get_type (elt_b) == ORG_HEADING))
    {

      /* Each doc_ref may store multiple versions of the same element.
       * Use only a single version to check if both headings are
       * equal, prioritizing using the ancestor.
       */

      org_heading *a_heading = (org_heading *) doc_ref_get_elt (a_ref);
      doc_src a_src;
      if (doc_ref_contains (a_ref, ANC_SRC))
        a_src = ANC_SRC;
      else if (doc_ref_contains (a_ref, LOC_SRC))
        a_src = LOC_SRC;
      else if (doc_ref_contains (a_ref, REM_SRC))
        a_src = REM_SRC;

      size_t a_index = srctoindex (a_src);
      org_heading_data *a_data = a_heading->data[a_index];

      org_heading *b_heading = (org_heading *) doc_ref_get_elt (b_ref);
      doc_src b_src;
      if (doc_ref_contains (b_ref, ANC_SRC))
        b_src = ANC_SRC;
      else if (doc_ref_contains (b_ref, LOC_SRC))
        b_src = LOC_SRC;
      else if (doc_ref_contains (b_ref, REM_SRC))
        b_src = REM_SRC;

      size_t b_index = srctoindex (b_src);
      org_heading_data *b_data = b_heading->data[b_index];

      assert (b_data && a_data);

      /* check if this element is already mapped,  IF it is, make sure
         it is only related to its other */
      if ((a_heading->data[b_index] != NULL)
          || (b_heading->data[a_index] != NULL))
        {
          isrelated = (a_heading == b_heading);
        }
      else
        {
          /* compare the key if it exists, use the heading body
             otherwise */
          if (a_heading->key.length > 0)
            {
              if (b_heading->key.length > 0)
                {
                  isrelated = doc_key_eql (&(a_heading->key), &(b_heading->key));
                }
              else
                {
                  isrelated = false;
                }
            }
          else
            {
              if (b_heading->key.length > 0)
                {
                  isrelated = false;
                }
              else
                {
                  isrelated = compare_body_text (a_data, b_data, ctxt);
                } /* end not key, so compare the lines */
            }/* end missing 1 key */
        } /* end same types of element */
    }
  return isrelated;
}

/*
 * Test if two headings have the same title.  Compare the body_text of
 * both headings, ignoring cookies and whitespace.
 *
 * Essentially, if two headings have the same words, then they
 * related, regardless of spaces, cookies, tags, & todo state.
 */
static bool
compare_body_text (org_heading_data *a_heading_data,
		   org_heading_data *b_heading_data, merge_ctxt *ctxt)
{
  bool isrelated = true;
  size_t a_i = 0;
  size_t b_i = 0;
  bool a_is_cookie = false, b_is_cookie = false;
  bool a_whitespace = true, b_whitespace = true; /*skip all leading
                                                   whitespace */
  size_t a_lookahead, b_lookahead;

  /* set an upperbound and lower bound to strip out all leading antd
     ending whitespace */
  substr a_body = a_heading_data->body_text;
  substr b_body = b_heading_data->body_text;
  int i;

  while ((a_i < a_body.length) ||
         (b_i < b_body.length))
    {
      a_is_cookie = false;
      b_is_cookie = false;
      /* compress all whitespace into a single space */

      /* Eat whitespace. Compress all white space into a single space */
      if ((a_i < a_body.length) &&
          (iswhitespace (a_body.string[a_i])))
        {

          while((a_i < a_body.length) &&
                (iswhitespace (a_body.string[a_i])))
            {
              a_i++;
            }

          a_whitespace = true;
        }

      if ((b_i < b_body.length) &&
          (iswhitespace (b_body.string[b_i])))
        {
          while((b_i < b_body.length) &&
                (iswhitespace (b_body.string[b_i])))
            {
              b_i++;
            }

          b_whitespace = true;
        }

      /* check for cookies.
       * priority cookie: "[#ABC]"
       * statistics:      "[535/5353]"
       *               or "[902%]"
       */
      if ( (a_i < a_body.length) &&
           (a_body.string[a_i] == '[') )
        {
          /* look a head to see if it is a cookie */
          bool quit = false;
          a_lookahead = a_i + 1;

          /* The state of the cookie parser:
           *  0: try to find what kind of cookie it is
           *  1: statistics cookie
           *  2: priority cookie
           *  3: wrap up cookie, ignoring numbers
           *  4: wrap up cookie
           */
          size_t state = 0;

          while ( (a_lookahead < a_body.length) &&
                  (!quit) )
            {
              switch (state)
                {
                case 0:  /* no idea what kind of cookie this is */
                  /* check for a priority */
                  if (a_body.string[a_lookahead] == '#')
                    {
                      state = 2;;
                    }
                  else if (isnumber(a_body.string[a_lookahead]))
                    {
                      state = 1; /* scan a statistics cookie */
                    }
                  else if (a_body.string[a_lookahead] == '/')
                    {
                      state = 4; /* ignore numbers and wrap up */
                    }
                  else if (a_body.string[a_lookahead] == '%')
                    {
                      state = 3; /* wrap up cookie */
                    }
                  else  /* is not a cookie */
                    {
                      quit = true;
                    }

                  /* advance to the next character */
                  a_lookahead ++;
                  break;

                case 1: /* check for a statistics cookie */
                  if (isnumber(a_body.string[a_lookahead]))
                    {
                      state = 1; /* scan a statistics cookie */
                    }
                  else if (a_body.string[a_lookahead] == '/')
                    {
                      state = 4; /* ignore numbers and wrap up */
                    }
                  else if (a_body.string[a_lookahead] == '%')
                    {
                      state = 3; /* wrap up cookie */
                    }
                  else /* is not a cookie */
                    {
                      quit = true; /* cookie finished too soon */
                    }

                  /* advance to the next character */
                  a_lookahead ++;
                  break;

                case 2: /* scanning for a priority cookie */
                  if ((a_lookahead < a_body.length) &&
                      (ispriority (a_body.string[a_lookahead], ctxt)))
                    {
                      state = 4;
                      a_lookahead++;
                    }
                  else /* not a cookie */
                    quit = true;

                  break;

                case 3: /* skip numbers and wrap up cookie */
                  while (isnumber(a_body.string[a_lookahead]))
                    {
                      a_lookahead++;
                    }

                case 4:  /* scan for propper wrapup */
                  /* note the fallthrough from above */
                  if (a_body.string[a_lookahead] = ']')
                    {
                      a_is_cookie = true;
                    }
                  a_lookahead++;
                  /* exit no matter what the next text is */
                  quit = true;

                  break;
                }
            } /* end while */
        } /* end if */

          /* eat cookies in b */
      if ( (b_i < b_body.length) &&
           (b_body.string[b_i] == '[') )
        {
          bool quit = false;
          size_t state = 0;
          b_lookahead = b_i + 1;

          while ( (b_lookahead < b_body.length) &&
                  (!quit) )
            {
              switch (state)
                {
                case 0:  /* no idea what kind of cookie this is */
                  /* check for a priority */
                  if (b_body.string[b_lookahead] == '#')
                    {
                      state = 2;;
                    }
                  else if (isnumber(b_body.string[b_lookahead]))
                    {
                      state = 1; /* scan a statistics cookie */
                    }
                  else if (b_body.string[b_lookahead] == '/')
                    {
                      state = 4; /* ignore numbers and wrap up */
                    }
                  else if (b_body.string[b_lookahead] == '%')
                    {
                      state = 3; /* wrap up cookie */
                    }
                  else  /* is not a cookie */
                    {
                      quit = true;
                    }

                  /* advance to the next character */
                  b_lookahead ++;
                  break;

                case 1: /* check for a statistics cookie */
                  if (isnumber(b_body.string[b_lookahead]))
                    {
                      state = 1; /* scan a statistics cookie */
                    }
                  else if (b_body.string[b_lookahead] == '/')
                    {
                      state = 4; /* ignore numbers and wrap up */
                    }
                  else if (b_body.string[b_lookahead] == '%')
                    {
                      state = 3; /* wrap up cookie */
                    }
                  else /* is not a cookie */
                    {
                      quit = true; /* cookie finished too soon */
                    }

                  /* advance to the next character */
                  b_lookahead ++;
                  break;

                case 2: /* scanning for a priority cookie */
                  if ((b_lookahead < b_body.length) &&
                      (ispriority (b_body.string[b_lookahead], ctxt)))
                    {
                      state = 4;
                      b_lookahead++;
                    }
                  else /* not a cookie */
                    quit = true;

                  break;

                case 3: /* skip numbers and wrap up cookie */
                  while (isnumber(b_body.string[b_lookahead]))
                    {
                      b_lookahead++;
                    }

                case 4:  /* scan for propper wrapup */
                  /* note the fallthrough from above */
                  if (b_body.string[b_lookahead] = ']')
                    {
                      b_is_cookie = true;
                      b_lookahead++;
                    }

                  /* exit no matter what the next text is */
                  quit = true;

                  break;
                }
            }
        } /* finish eating cookies */

      /* compare the next character */
      {
        if (a_is_cookie)
          {
            /* skip the cookie */
            a_i = a_lookahead;
          }

        if (b_is_cookie)
          {
            /* skip the cookie */
            b_i = b_lookahead;
          }

        if ((!b_is_cookie) && (!a_is_cookie))
          {
            if ((a_i < a_body.length) &&
                (b_i < b_body.length))
              {
                /* compare the next character */
                if ( !(a_whitespace == b_whitespace
                    && b_body.string[b_i] == a_body.string[a_i]) )
                  {
                    /* break from the loop */
                    isrelated = false;
                    b_i = -1;
                    a_i = -1;
                  }
                else
                  {
                    a_i ++;
                    b_i ++;
                    a_whitespace = false;
                    b_whitespace = false;
                  }
              }
            else
              {
                /* break from the loop */
                isrelated = false;
                b_i = -1;
                a_i = -1;
              }
          }
      }
    } /* end while: compare the lines */
  return isrelated;
}

static int
org_heading_compare_op (doc_elt *a, doc_src a_src, doc_elt *b, doc_src b_src)
{
  /**
   * @todo Implement org_heading compare operator.
   */
  return 0;
}

static void
org_heading_merge_op (doc_ref *a_ref, doc_ref *b_ref, merge_ctxt *ctxt)
{

  /* Merge both headings, copying in all data from b_ref to a_ref.
   * Overwrite an org_heading data if one already exists.
   */

  debug_msg (ORG_HEADING, 3, "Merging org_heading\n");

  org_heading *a_heading = (org_heading *) doc_ref_get_elt (a_ref);
  org_heading *b_heading = (org_heading *) doc_ref_get_elt (b_ref);

  assert (a_heading != NULL);
  assert (b_heading != NULL);

  /* check if the elements have already been merged */

  /* merge the data of the elements.  Ignore the doc_src sources, and
   * check if the data exists in the heading to copy over */
  if (b_heading->data[ANC_INDEX] != NULL)
    a_heading->data[ANC_INDEX] = b_heading->data[ANC_INDEX];

  if (b_heading->data[LOC_INDEX] != NULL)
    a_heading->data[LOC_INDEX] = b_heading->data[LOC_INDEX];

  if (b_heading->data[REM_INDEX] != NULL)
    a_heading->data[REM_INDEX] = b_heading->data[REM_INDEX];

  /* merge the doc_src of the elements */

  /* Deal with match strategy specific behaviour */
  if (ctxt->strategy == GLOBAL_SEARCH_MERGE)
    {
      if (b_heading->data[ANC_INDEX] != NULL)
	a_heading->data[ANC_INDEX]->global_search_merge = true;
      if (b_heading->data[LOC_INDEX] != NULL)
	a_heading->data[LOC_INDEX]->global_search_merge = true;
      if (b_heading->data[REM_INDEX] != NULL)
	a_heading->data[REM_INDEX]->global_search_merge = true;
    }
  else if (ctxt->strategy == LOCAL_LIST_MERGE)
    {
      if (b_heading->data[ANC_INDEX] != NULL)
	a_heading->data[ANC_INDEX]->local_list_merge = true;
      if (b_heading->data[LOC_INDEX] != NULL)
	a_heading->data[LOC_INDEX]->local_list_merge = true;
      if (b_heading->data[REM_INDEX] != NULL)
	a_heading->data[REM_INDEX]->local_list_merge = true;
    }

  /* Merge the children elements */
  debug_msg (DOC_ELT, 5, "Merging heading subtext\n");
  doc_reflist_merge (b_ref, a_heading->subtext, b_heading->subtext, ctxt);

  debug_msg (DOC_ELT, 3, "Merging heading subheadings\n");
  doc_reflist_merge (b_ref, a_heading->subheadings, b_heading->subheadings, ctxt);

  /* the doc_refs are updated externally */

  return;
}

/*
 * Isupdated_op will return true if any version located at the passed
 * ref is updated from the ancestor in a way that might conflict with
 * a parent update.
 *
 * This function is primarily used to test for conflicts with delete
 * operations.  If the parent was deleted, a child update will
 * conflict with the delete at the parent's level. This function
 * counts inserted elements as updates, but does not count deletions.
 */
static bool
org_heading_isupdated_op (doc_ref *ref)
{
  doc_elt *elt = doc_ref_get_elt (ref);
  org_heading *heading = (org_heading *)elt;
  org_heading_data *anc_data;
  org_heading_data *loc_data;
  org_heading_data *rem_data;

  anc_data = heading->data[ANC_INDEX];
  loc_data = heading->data[LOC_INDEX];
  rem_data = heading->data[REM_INDEX];

  bool isupdated = false;

  /* Check each version located at ref for updates.  If a version's
     data is nonexistant, then do not count that as an update.*/
  if ((loc_data != NULL) && doc_ref_contains (ref, LOC_SRC))
    {
      isupdated = isupdated || org_heading_content_isupdated(heading, LOC_INDEX);
    }

  if ((rem_data != NULL) && doc_ref_contains (ref, REM_SRC))
    {
      isupdated = isupdated || org_heading_content_isupdated(heading, REM_INDEX);
    }

  isupdated = isupdated || org_heading_subelts_isupdated (heading);
  return isupdated;
}

/**
 * Compare the data in slot data_index with the ancestor data.  Try to
 * detect if the content has been updated.
 */
static bool
org_heading_content_isupdated (org_heading *heading, size_t data_index)
{
  org_heading_data *anc_data = heading->data[ANC_INDEX];
  org_heading_data *new_data = heading->data[data_index];

  /**
   * @todo Check for add and delete operations.  These operations
   * count as updates according to this function.
   */

  /* return true if:
   * - moved
   * - children updated
   * - level changed
   * - body text changed
   * - todo text changed
   * - tags changed
   * Don't return true if:
   * - deleted
   */

  bool isupdated = false;

  if (anc_data != NULL)
    {
      if (new_data != NULL)
	{
	  isupdated = (substreql (anc_data->entire_text, new_data->entire_text) == 0);
	}
      else
	{
	}
    }
  else
    {
      if (new_data != NULL)
	{
	  isupdated = true;
	}
      else
	{

	}
    }

  /**
   * @todo Cache the calculated update.  This may require a
   * force_isupdated function.
   */

  return isupdated;
}

static bool
org_heading_subelts_isupdated (org_heading *heading)
{
  /**
   * @todo Cache the calculated isupdated status.
   */

  return  (doc_reflist_isupdated (heading->subheadings) ||
	   doc_reflist_isupdated (heading->subtext));
}

/*
 * Printing and Merging.
 */

void
org_heading_print_op (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{

  /* Letter | Meaning
   *      U | Updated: An updated element exists in this version.
   *      D | Deleted: The element was deleted in this version.
   *      I | Inserted: The element is new, and has no ancestor.
   *      X | Does not exist: The element is unassociated with the version.
   */
  org_heading *heading = (org_heading *)doc_ref_get_elt (ref);

  if ( heading->data[ANC_INDEX] != NULL)
    {
      if (heading->data[LOC_INDEX] != NULL)
        {
          if (heading->data[REM_INDEX] != NULL)
            {
              print_LU_RU (ref, ctxt, out);
            }
          else
            {
              print_LU_RD (ref, ctxt, out);
            }
        }
      else
        {
          if (heading->data[REM_INDEX] != NULL)
            {
              print_LD_RU (ref, ctxt, out);
            }
          else
            {
              print_LD_RD (ref, ctxt, out);
            }
        }
    }
  else
    {
      if (heading->data[LOC_INDEX] != NULL)
        {
          if (heading->data[REM_INDEX] != NULL)
            {
              print_LI_RI (ref, ctxt, out);
            }
          else
            {
              print_LI_RX (ref, ctxt, out);
            }
        }
      else
        {
          if (heading->data[REM_INDEX] != NULL)
            {
              print_LX_RI (ref, ctxt, out);
            }
          else
            {
              print_LX_RX (ref, ctxt, out);
            }
        }
    }
  return;
}

static inline void
print_LU_RU (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  org_heading *h = (org_heading *)doc_ref_get_elt (ref);
  bool loc_moved = (h->data[LOC_INDEX]->global_search_merge
		    && !h->data[LOC_INDEX]->local_list_merge);
  bool rem_moved =( h->data[REM_INDEX]->global_search_merge
		    && !h->data[REM_INDEX]->local_list_merge);

  bool loc_ishere = doc_ref_contains (ref, LOC_SRC);
  bool rem_ishere = doc_ref_contains (ref, REM_SRC);

  debug_msg (ORG_HEADING, 4,
             "LOC: local_list_merge =%d, global_search_merge =%d\n",
             h->data[LOC_INDEX]->local_list_merge,
             h->data[LOC_INDEX]->global_search_merge);


  debug_msg (ORG_HEADING, 4,
             "REM: local_list_merge =%d, global_search_merge =%d\n",
             h->data[REM_INDEX]->local_list_merge,
             h->data[REM_INDEX]->global_search_merge);

  if (loc_moved)
    {
      if (rem_moved)
        {
          if (loc_ishere)
            {
              if (rem_ishere)
                {
                  print_LR (ref, ctxt, out);
                }
              else
                {
                  enter_movement_conflict (ctxt, local_side, "Moved\n", out);
                  print_LR (ref, ctxt, out);
                  print_subelts (ref, ctxt, out);
                  enter_movement_conflict (ctxt, remote_side, NULL, out);
                  enter_movement_conflict (ctxt, no_conflict, "Moved\n", out);
                }
            }
          else
            {
              if (rem_ishere)
                {
                  enter_movement_conflict (ctxt, local_side, "Moved\n", out);
                  enter_movement_conflict (ctxt, remote_side, NULL, out);
                  print_LR (ref, ctxt, out);
                  print_subelts (ref, ctxt, out);
                  enter_movement_conflict (ctxt, no_conflict, "Moved\n", out);
                }
              else
                {
                  /* Print Nothing */
                }
            }
        }
      else
        {
          if (loc_ishere)
            {
              print_LR (ref, ctxt, out);
              print_subelts (ref, ctxt, out);
            }
          else
            {
            }
        }
    }
  else
    {
      if (rem_moved)
        {
          if (rem_ishere)
            {
              print_LR (ref, ctxt, out);
              print_subelts (ref, ctxt, out);
            }
          else
            {
            }
        }
      else
        {
          if (loc_ishere && rem_ishere)
            {
              print_LR (ref, ctxt, out);
              print_subelts (ref, ctxt, out);
            }
          else
            {
            }
        }
    }
  return;
}

static inline void
print_LU_RD (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  doc_elt *elt = doc_ref_get_elt (ref);
  org_heading *heading = (org_heading *)elt;
  bool local_ishere = doc_ref_contains (ref, LOC_SRC);

  if (local_ishere)
    {
      if (org_heading_content_isupdated (heading, LOC_INDEX) ||
	  org_heading_subelts_isupdated (heading))
        {
          enter_structural_conflict (ctxt, local_side, "Updated\n", out);
          print_L (ref, ctxt, out);
	  print_subelts (ref, ctxt, out);
          //enter_structural_conflict (ctxt, remote_side, NULL, out);
          enter_structural_conflict (ctxt, no_conflict, "Deleted\n", out);
        }
    }
  return;
}

static inline void
print_LD_RU (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  doc_elt *elt = doc_ref_get_elt (ref);
  org_heading *heading = (org_heading *)elt;
  bool remote_ishere = doc_ref_contains (ref, REM_SRC);

  debug_msg (DOC_ELT, 5, "remote_ishere = %d\n", remote_ishere);
  debug_msg (DOC_ELT, 5, "doc_ref = %d\n", doc_ref_get_src (ref));
  if (remote_ishere)
    {
      if (org_heading_content_isupdated (heading, REM_INDEX) ||
	  org_heading_subelts_isupdated (heading))
        {
          //enter_structural_conflict (ctxt, local_side, "Deleted\n", out);
          enter_structural_conflict (ctxt, remote_side, NULL, out);
          print_R (ref, ctxt, out);
	  print_subelts (ref, ctxt, out);
          enter_structural_conflict (ctxt, no_conflict, "Updated\n", out);
        }
    }
  return;
}

static inline void
print_LD_RD (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  return;
}

static inline void
print_LI_RI (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  bool loc_ishere = doc_ref_contains (ref, LOC_SRC);
  bool rem_ishere = doc_ref_contains (ref, REM_SRC);

  if (loc_ishere && rem_ishere)
    {
      print_LR (ref, ctxt, out);
      print_subelts (ref, ctxt, out);
    }
  return;
}

static inline void
print_LI_RX (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  bool loc_ishere = doc_ref_contains (ref, LOC_SRC);
  if (loc_ishere)
    {
      print_L (ref, ctxt, out);
      print_subelts (ref, ctxt, out);
    }
  return;
}

/**
 * The remote version of the heading is inserted.  There is no
 * corresponding local version.  Print the remote version if it is
 * located at the current doc ref.  It should always be located at the
 * doc_ref, because there is no corresponding ancestor.
 */
static inline void
print_LX_RI (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  bool rem_ishere = doc_ref_contains (ref, REM_SRC);
  if (rem_ishere)
    {
      print_R (ref, ctxt, out);
      print_subelts (ref, ctxt, out);
    }
  return;
}

/**
 * Print the heading where local never existed, and remote never
 * existed.  Should never be called.
 */
static inline void
print_LX_RX (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  return;
}

/**
 * Print the local and remote versions of the heading merged.  Will
 * cause a content conflict if the updates cannot be consolidated.
 */
static void
print_LR (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  org_heading *h = (org_heading *)doc_ref_get_elt (ref);
  org_heading_data *anc_data = h->data[ANC_INDEX];
  org_heading_data *loc_data = h->data[LOC_INDEX];
  org_heading_data *rem_data = h->data[REM_INDEX];

  /* Scan each field for an update.
     If it has updated, make a note.
     If both versions have updated, note a conflict.
  */
  if (anc_data == NULL)
    {
      if (substreql (loc_data->entire_text, rem_data->entire_text))
	{
	  substrprint (loc_data->entire_text, out);
	}
      else
	{
	  enter_content_conflict (ctxt, local_side, "Updated\n", out);
	  print (h, LOC_INDEX, ctxt, out);
	  enter_content_conflict (ctxt, remote_side, NULL, out);
	  print (h, REM_INDEX, ctxt, out);
	  enter_content_conflict (ctxt, no_conflict, "Updated\n", out);
	}
    }
  else
    {
      bool conflict = false;

      /* Level */
      bool loc_level_update = (loc_data->rel_level != anc_data->rel_level);
      bool rem_level_update = (rem_data->rel_level != anc_data->rel_level);
      if (loc_data->level != rem_data->level)
        {
          conflict = conflict || (loc_level_update && rem_level_update);
        }

      /* lead_ws */
      bool loc_lead_ws_update = !substreql (loc_data->lead_ws, anc_data->lead_ws);
      bool rem_lead_ws_update = !substreql (rem_data->lead_ws, anc_data->lead_ws);
      //if (!substreql (loc_data->lead_ws, rem_data->lead_ws))
        {
          //conflict = conflict || (loc_lead_ws_update && rem_lead_ws_update);
        }

      /* todo */
      bool loc_todo_update = !substreql (loc_data->todo, anc_data->todo);
      bool rem_todo_update = !substreql (rem_data->todo, anc_data->todo);
      if (!substreql (loc_data->todo, rem_data->todo))
        {
          conflict = conflict || ( loc_todo_update && rem_todo_update);
        }

      /* body text
       * strip the whitespace off the ends of the body text, so that
       * it is ignored when trying to see if there is a conflict or
       * not */
      bool loc_body_text_update = !substreql (loc_data->body_text, anc_data->body_text);
      bool rem_body_text_update = !substreql (rem_data->body_text, anc_data->body_text);

      /* set an upperbound and lower bound to strip out all leading antd
         ending whitespace */
      substr loc_body = loc_data->body_text;
      substr rem_body = rem_data->body_text;
      int i;

      for(i = 0; i < loc_body.length; i++)
        {
          if (!iswhitespace (loc_body.string[i]))
            break;
        }
      loc_body.length -= i;
      loc_body.string += i;

      for(i = 0; i < rem_body.length; i++)
        {
          if (!iswhitespace (rem_body.string[i]))
            break;
        }
      rem_body.length -= i;
      rem_body.string += i;

      for(i = 0; i < loc_body.length; i++)
        {
          if (!iswhitespace (loc_body.string[loc_body.length-i]))
            break;
        }
      loc_body.length -= (i -1);

      for(i = 0; i < rem_body.length; i++)
        {
          if (!iswhitespace (rem_body.string[rem_body.length-i]))
            break;
        }
      rem_body.length -= (i -1);

      if (!substreql (loc_body, rem_body))
        {
          conflict = conflict || (loc_body_text_update && rem_body_text_update);
        }

      /* tags_str */
      bool loc_tags_str_update = !substreql (loc_data->tags_str, anc_data->tags_str);
      bool rem_tags_str_update = !substreql (rem_data->tags_str, anc_data->tags_str);
      /* Tags cannot cause a conflict */

      /* Post text */
      bool loc_post_text_update = !substreql (loc_data->post_text, anc_data->post_text);
      bool rem_post_text_update = !substreql (rem_data->post_text, anc_data->post_text);
      if (!substreql (loc_data->post_text, rem_data->post_text))
        {
          conflict = conflict || (loc_post_text_update && rem_post_text_update);
        }

      /* linebreak */
      bool loc_linebreak_update = !substreql (loc_data->linebreak, anc_data->linebreak);
      bool rem_linebreak_update = !substreql (rem_data->linebreak, anc_data->linebreak);
      //conflict = conflict || (loc_post_text_update && rem_post_text_update);

      if (conflict)
	{
	  /* Print both version unmerged */
	  enter_content_conflict (ctxt, local_side, "Updated\n", out);
	  print (h, LOC_INDEX, ctxt, out);
	  enter_content_conflict (ctxt, remote_side, NULL, out);
	  print (h, REM_INDEX, ctxt, out);
	  enter_content_conflict (ctxt, no_conflict, "Updated\n", out);

	  ctxt->current_level += (h->data[REM_INDEX]->rel_level > h->data[LOC_INDEX]->rel_level) ?
	    h->data[REM_INDEX]->rel_level : h->data[LOC_INDEX]->rel_level;
	}
      else
	{
	  int col = 0;


	  /* Print Stars */
	  int i = 0;
	  int level = 0;
	  size_t index;

	  if (loc_level_update)
            index = LOC_INDEX;
	  else
	    index = REM_INDEX;

          debug_msg (ORG_HEADING, 5, "cur=%d, rel=%d \n", ctxt->current_level, level);
	  col += print_stars (h, index, ctxt, out);

	  /* Update the context */
	  ctxt->current_level += h->data[index]->rel_level;

	  /* Lead Witespace */
	  if (loc_lead_ws_update)
	      col += substrprint (loc_data->lead_ws, out);
	  else if (rem_lead_ws_update)
	      col += substrprint (rem_data->lead_ws, out);
	  else
	      col += substrprint (anc_data->lead_ws, out);

	  /* Todo State */
	  if (loc_todo_update)
	    col += substrprint (loc_data->todo, out);
	  else if (rem_todo_update)
	    col += substrprint (rem_data->todo, out);
	  else
	    col += substrprint (anc_data->todo, out);

	  /* body_text */
	  bool generate_body_ws = true;

	  if (loc_body_text_update)
	    {
	      col += substrprint (loc_data->body_text, out);
	      if (!generate_body_ws)
		{
		  col += substrprint (loc_data->body_ws, out);
		}
            }
          else if (rem_body_text_update)
            {
              col += substrprint (rem_data->body_text, out);
              if (!generate_body_ws)
                {
                  col += substrprint (rem_data->body_ws, out);
                }
            }
          else
            {
              col += substrprint (anc_data->body_text, out);
              if (!generate_body_ws)
                {
                  col += substrprint (anc_data->body_ws, out);
                }
            }

          /* print the tags, possibly generate whitespace */
          col += merge_tags(anc_data->tags_str,
                            loc_data->tags_str,
                            rem_data->tags_str,
                            col, generate_body_ws, ctxt, out);

          /* Post text */
          if (loc_post_text_update)
            col += substrprint (loc_data->post_text, out);
          else if (rem_post_text_update)
            col += substrprint (rem_data->post_text, out);
          else
            col += substrprint (anc_data->post_text, out);

          /* Line break */
          if (loc_linebreak_update)
            col += substrprint (loc_data->linebreak, out);
          else if (rem_linebreak_update)
            col += substrprint (rem_data->linebreak, out);
          else
            col += substrprint (anc_data->linebreak, out);

        }
    }
  return;
}

/**
 * Print the local version of the heading.  Update the context
 * accordingly.  Subelts will use the updated context when printing.
 */
static inline void
print_L (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  org_heading *h  = (org_heading *)doc_ref_get_elt (ref);
  print (h, LOC_INDEX, ctxt, out);

  ctxt->current_level += h->data[LOC_INDEX]->rel_level;
  return;
}

/**
 * Print the remote version of the heading.
 */
static inline void
print_R (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  org_heading *h  = (org_heading *)doc_ref_get_elt (ref);
  print (h, REM_INDEX, ctxt, out);

  ctxt->current_level += h->data[REM_INDEX]->rel_level;
  return;
}

/**
 * Print a single, unmerged version of the heading H. Print the
 * version of the heading corresponding to the index.
 */
static void
print (org_heading *h, size_t index, print_ctxt *ctxt, doc_stream *out)
{
  print_stars (h, index, ctxt, out);
  substrprint (h->data[index]->lead_ws, out);
  substrprint (h->data[index]->todo, out);
  substrprint (h->data[index]->body_text, out);
  substrprint (h->data[index]->body_ws, out);
  substrprint (h->data[index]->tags_str, out);
  substrprint (h->data[index]->post_text, out);
  substrprint (h->data[index]->linebreak, out);
  return;
}

/**
 * Print the lead stars of a heading.  Print the stars of the version
 * corresponding to index.  Use the print ctxt's current_level and the
 * heading's relative level to print the correct number of stars.
 * Returns the number of characters written to OUT.
 */
static int
print_stars (org_heading *h, size_t index, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (ORG_HEADING, 5, "level: %d", h->data[index]->rel_level, out);
  int num = h->data[index]->rel_level + ctxt->current_level;
  int i = 0;
  for (i = 0; i < num; i++)
    {
      doc_stream_putc ('*', out);
    }
  return num;
}

/**
 * Print all sub-elements of the heading stored at ref, giving them
 * the passed print_ctxt.  If the print ctxt should be changed, it
 * must be done before this function is called.
 */
static void
print_subelts (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  org_heading *h = (org_heading *)doc_ref_get_elt (ref);
  doc_reflist_print (h->subtext, ctxt, out);
  doc_reflist_print (h->subheadings, ctxt, out);
  return;
}

static void
org_heading_note_delete (doc_ref *ref, merge_ctxt *ctxt)
{
  org_heading * heading = (org_heading *)doc_ref_get_elt(ref);
  debug_msg (ORG_HEADING, 5, "key ='");
  if (ORG_HEADING_PRINTLEVEL >= 5)
    {
      fwrite (heading->key.string, 1, heading->key.length, stderr);
      fprintf (stderr, "'\n");
    }

  if ((heading->key.length > 0) &&
      (doc_ref_contains (ref, ANC_SRC)))
    {
      debug_msg (ORG_HEADING, 5, "registering\n");
      /* org_text does not have global matching, do nothing */
      smerger_register_delete (ctxt->global_smerger, ref, ctxt);
    }
  else
    {
      /* do nothing */
    }
  doc_reflist_note_delete (heading->subheadings, ctxt);
  return;
}

static void
org_heading_note_insert (doc_ref *ref, merge_ctxt *ctxt)
{
  /*
   * Note a movement for all vesions that doc_ref represents.
   */
  org_heading *heading = (org_heading *)doc_ref_get_elt (ref);
  debug_msg (ORG_HEADING, 5, "key = '");
  if (ORG_HEADING_PRINTLEVEL >= 5)
    {
      fwrite (heading->key.string, 1, heading->key.length, stderr);
      fprintf (stderr, "'\n");
    }

  if (heading->key.length > 0)
    {
      /* org_text does not have global matching, do nothing */
      smerger_register_insert (ctxt->global_smerger, ref, ctxt);
    }
  else
    {
      /* Do nothing */
    }
  doc_reflist_note_insert (heading->subheadings, ctxt);
  return;
}

void
org_heading_set_key (org_heading *h, char *string, size_t length)
{
  h->key.string = string;
  h->key.length = length;
  return;
}

static doc_key *
org_heading_get_key (doc_elt * elt)
{
  return &((org_heading *) elt )->key;//  &org_heading_key;
}

static size_t
parse_tags (gl_list_t tags, substr s)
{
  int ubound = 1;
  int lbound = 1;
  substr *tag;

  for (ubound=1; ubound< s.length; ubound++)
    {
      if (s.string[ubound] == ':')
        {
          /* create a new tag element */
          tag = malloc (sizeof (substr));
          tag->length = (ubound -lbound);
          tag->string = (s.string + lbound);

          /* add it to the list */
          gl_list_nx_add_last (tags, tag);

          /* try to find the next element */
          lbound = ubound+1;
        }
    }
  return;
}

static size_t
merge_tags (substr anc_str, substr loc_str, substr rem_str, size_t curr_col,
	    bool gen_ws, print_ctxt *ctxt, doc_stream *out)
{
  /**
   * @TODO try to maintain some semblance of the ordering
   */

  size_t char_count = 0;
  /* assume that the two strings are both correctly setup as the
     length of tags.  list diff the two tags, and print them assuming
     they will start at the correct location */

  /* scan the substrings and add them to a list */
  gl_list_t anc_list = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, NULL,
                                                NULL, true);
  gl_list_t loc_list = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, NULL,
                                                NULL, true);
  gl_list_t rem_list = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, NULL,
                                                NULL, true);

  parse_tags (anc_list, anc_str);
  parse_tags (loc_list, loc_str);
  parse_tags (rem_list, rem_str);

  char_count = anc_str.length + loc_str.length + rem_str.length + 1;
  if (gl_list_size (anc_list))
      char_count--;
  if (gl_list_size (loc_list))
      char_count--;
  if (gl_list_size (rem_list))
      char_count--;

  /* combine the tags into one list */
  /* if a tag is not in one of local or remote, mark the substr as 0
     length in the ancestor.  If the element is in local or remote,
     and anestor, mark local and remote substr as length 0

     this strategy will not maintain the order when merging
  */
  gl_list_iterator_t anc_i, loc_i, rem_i;

  anc_i = gl_list_iterator (anc_list);

  substr *anc_tag, *loc_tag, *rem_tag;
  bool loc_found = false;
  bool rem_found = false;

  /* filter out the nodes that match the ancestor */
  while (gl_list_iterator_next (&anc_i, (const void **) &anc_tag, NULL))
    {
      loc_found = false;
      rem_found = false;

      loc_i = gl_list_iterator (loc_list);
      rem_i = gl_list_iterator (rem_list);

      while (gl_list_iterator_next (&loc_i, (const void **) &loc_tag, NULL))
        {
          if (substreql (*anc_tag, *loc_tag))
            {
              debug_msg (DOC, 5, "loc anc match\n");
              /* found a match, remove from loc */
              char_count -= (loc_tag->length + 1);
              loc_tag->length = 0;
              loc_found = true;
              break;
            }
        }

      while (gl_list_iterator_next (&rem_i, (const void **) &rem_tag, NULL))
        {
          if (substreql (*anc_tag, *rem_tag))
            {
              debug_msg (DOC, 5, "rem anc match\n");
              /* found a match, remove from rem */
              char_count -= (rem_tag->length + 1);
              rem_tag->length = 0;
              rem_found = true;
              break;
            }
        }

      if (!rem_found || !loc_found)
        {
          /* no match found, remove anc */
          debug_msg (DOC, 5, "no anc match\n");
          char_count -= (anc_tag->length + 1);
          anc_tag->length = 0;
        }
    }

  rem_i = gl_list_iterator (rem_list);
  while (gl_list_iterator_next (&rem_i, (const void **) &rem_tag, NULL))
    {
      loc_found = false;
      loc_i = gl_list_iterator (loc_list);
      while (gl_list_iterator_next (&loc_i, (const void **) &loc_tag, NULL))
        {
          if (loc_tag->length > 0 && substreql (*rem_tag, *loc_tag))
            {
              /* found a match, remove from loc and print it */
              debug_msg (DOC, 5, "rem loc match\n");
              char_count -= (loc_tag->length + 1);
              loc_tag->length = 0;
              loc_found = true;
              break;
            }
        }
    }

  /* print every element with a length of more than 0 */
  bool close_mark = (char_count > 3);
  if (close_mark && gen_ws)
    {
      debug_msg (DOC_ELT, 5, "Generating %d long body_ws\n",
		 (ctxt->rmargin - 1 - char_count - curr_col));
      int i;
      doc_stream_putc(' ', out);
      //curr_col += 1;
      for (i=0; i < (ctxt->rmargin - 1 - char_count - curr_col); i++)
        {
          doc_stream_putc(' ', out);
        }
    }

  anc_i = gl_list_iterator (anc_list);
  while (gl_list_iterator_next (&anc_i, (const void **) &anc_tag, NULL))
    {
      if (anc_tag->length > 0)
        {
          close_mark = true;
          doc_stream_putc (':', out);
          substrprint (*anc_tag, out);
        }
    }

  rem_i = gl_list_iterator (rem_list);
  while (gl_list_iterator_next (&rem_i, (const void **) &rem_tag, NULL))
    {
      if (rem_tag->length > 0)
        {
          /* found a match, remove from loc and print it */
          doc_stream_putc (':', out);
          substrprint (*rem_tag, out);
          close_mark = true;
        }
    }

  loc_i = gl_list_iterator (loc_list);
  while (gl_list_iterator_next (&loc_i, (const void **) &loc_tag, NULL))
    {
      if (loc_tag->length > 0)
        {
          /* found a match, remove from loc and print it */
          doc_stream_putc (':', out);
          substrprint (*loc_tag, out);
          close_mark = true;
        }
    }

  if (close_mark)
    doc_stream_putc (':', out);

  return char_count;
}


/* For every element, check to see if some element is below it. Ignor
 * NULLs.  Return a value indicating if the element was found below */
bool
org_heading_check_for_target (org_heading *this, org_heading* target)
{
  /* first check to see if the target exist anywhere below */
  gl_list_iterator_t i;
  i = gl_list_iterator (this->subheadings);
  doc_ref *ref = NULL;
  bool found =  false;
  org_heading *heading;

  debug_msg (ORG_HEADING, 3, "checking subheadings for target...\n");

  while (!found
	 && gl_list_iterator_next (&i, (const void **) &ref, NULL))
    {
      heading = (org_heading *)doc_ref_get_elt (ref);
      if (heading == target)
        {
          debug_msg (ORG_HEADING,  1, "found loop!!\n");
          found = true;
        }
      else
        {
          found = org_heading_check_for_target(heading, target);
        }
    }
  debug_msg (ORG_HEADING, 3, "found = %d\n", found);
  gl_list_iterator_free (&i);
  return found;
}

/* will call thes function on its children after it searches for
   itself */
bool
org_heading_check_for_loop (org_heading *this)
{
  /* first check to see if the target exist anywhere below */
  gl_list_iterator_t i;
  i = gl_list_iterator (this->subheadings);
  doc_ref *ref = NULL;
  bool found =  false;
  org_heading *heading;

  debug_msg (ORG_HEADING, 3, "checking for loops\n");

  if (org_heading_check_for_target (this, this))
    {
      debug_msg (ORG_HEADING,  1, "found loop!!\n");
      found = true;
    }

  debug_msg (ORG_HEADING, 3, "checking subheadings for loops\n");

  while (gl_list_iterator_next (&i, (const void **) &ref, NULL))
    {
      heading = (org_heading *)doc_ref_get_elt (ref);

      org_heading_check_for_loop (heading);
    }

  gl_list_iterator_free (&i);
  return found;
}
