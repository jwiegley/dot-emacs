/**
 * @file org_text.c
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
#include <assert.h>
#include <stdio.h>

#include "print.h"
#include "doc_elt.h"
#include "doc_elt_ops.h"
#include "doc_elt_util.h"
#include "org_text.h"

/* Forward Declarations */
struct org_text_data;
typedef struct org_text_data org_text_data;

static doc_elt_ops_print     org_text_print_op;
static doc_elt_ops_isrelated org_text_isrelated_op;
static doc_elt_ops_compare   org_text_compare_op;
static doc_elt_ops_merge     org_text_merge_op;
static doc_elt_ops_isupdated org_text_isupdated_op;
static doc_elt_ops_note_delete org_text_note_delete;
static doc_elt_ops_note_insert org_text_note_insert;
static doc_elt_ops_get_key     org_text_get_key;


/* Declaration of org_element operations table */
doc_elt_ops org_text_ops = {
  /* printing */
  .print         = &org_text_print_op,
  /* comparing */
  .isrelated     = &org_text_isrelated_op,
  .compare       = &org_text_compare_op,
  /* merging */
  .merge         = &org_text_merge_op,
  .isupdated     = &org_text_isupdated_op,
  .note_delete   = &org_text_note_delete,
  .note_insert   = &org_text_note_insert,
  /* Global mapping */
  .get_key       = &org_text_get_key
};

typedef struct org_text
{
  doc_elt elt;
  org_text_data * data[3];
} org_text;

typedef struct org_text_data
{
  substr text;
} org_text_data;

/*
 * Constructor, Destructor
 */
org_text *
org_text_create_empty (doc_elt_ops *ops)
{
  org_text *txt   = calloc (1, sizeof (org_text));
  doc_elt_set_ops (&(txt->elt), ops);
  doc_elt_set_type ((doc_elt *) txt, ORG_TEXT);
  return txt;
}

void
org_text_initversion (org_text *text, doc_src src)
{
  size_t index = srctoindex(src);
  if (text->data[index] == NULL)
    {
      text->data[index] = calloc (1, sizeof (org_text_data));
    }
  return;
}

void
org_text_free (org_text *self)
{
  int i = 0;
  for (i = 0; i < 3; i++)
    {
      free(self->data[i]);
    }
  free (self);
  return;
}

bool
org_text_containsversion (org_text *text, doc_src src)
{
  size_t index = srctoindex(src);
  return text->data[index] != NULL;
}


/*
 * Modifier functions
 */
void
org_text_set_text (org_text *text, char *string, size_t length, doc_src src)
{
  assert (text != NULL);
  org_text_data *d = text->data[srctoindex(src)];
  assert (d != NULL);
  if (d != NULL)
    {
      d->text.length = length;
      d->text.string = string;
    }
  return;
}

char *
org_text_get_text (org_text *text, doc_src src)
{
  assert (text != NULL);
  char * str = NULL;
  org_text_data *d = text->data[srctoindex(src)];
  assert (d != NULL);
  if (d != NULL)
    {
      str = d->text.string;
    }
  return str;
}

size_t
org_text_get_length (org_text *text, doc_src src)
{
  assert (text != NULL);
  int length = 0;
  org_text_data *data = text->data[srctoindex(src)];
  assert (data != NULL);
  if (data != NULL)
    {
      length = data->text.length;
    }
  return length;
}

/*
 * Document Element Operations
 */

static void
org_text_print_op (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  /* text objects do not move.  They are either deleted, added, or
     updated. */

  debug_msg (DOC, 5, "Begin Printing\n");
  doc_elt *elt = doc_ref_get_elt(ref);
  org_text *text = (org_text *)elt;

  org_text_data *anc_data = text->data[ANC_INDEX];
  org_text_data *loc_data = text->data[LOC_INDEX];
  org_text_data *rem_data = text->data[REM_INDEX];

  /* This is the merge logic */
  if (anc_data != NULL)
    {
      debug_msg (DOC, 4, "Ancestor exists\n");
      if (loc_data != NULL)
	{
	  debug_msg (DOC, 4, "Local exists\n");
	  if (rem_data != NULL)
	    {
	      debug_msg (DOC, 4, "Remote exists\n");
	      if (substreql (loc_data->text, anc_data->text))
		{
		  if (substreql (rem_data->text, anc_data->text))
		    {
		      /* Nothing has updated, print ancestor */
		      substrprint (anc_data->text, out);
		    }
		  else
		    {
		      /* Remote has updated. Print remote */
		      substrprint (rem_data->text, out);
		    }
		}
	      else
		{
		  if (substreql (anc_data->text, rem_data->text))
		    {
		      /* Local has updated. Print local. */
		      substrprint (loc_data->text, out);
		    }
		  else
		    {
		      debug_msg(DOC, 3, "Update Conflict\n");
		      /* Both Have Updated, Conflict ! */
		      line_diff3 (anc_data->text.string, anc_data->text.length,
				  loc_data->text.string, loc_data->text.length,
				  rem_data->text.string, rem_data->text.length,
				  ctxt, out);
		    }
		}
	    }
	  else
	    {
	      if (substreql (loc_data->text, anc_data->text))
		{
		  /* Deleted in remote. Print nothing.  */
		}
	      else
		{
		  /* Updated in local, deleted in remote. Conflict ! */
		  enter_structural_conflict (ctxt, local_side, "Updated\n", out);
		  substrprint (loc_data->text, out);
		  enter_structural_conflict (ctxt, remote_side, NULL, out);
		  enter_structural_conflict (ctxt, no_conflict, "Deleted\n", out);
		}
	    }
	}
      else
	{
	  if (rem_data != NULL)
	    {
	      if (substreql (rem_data->text, anc_data->text))
		{
		  /* Deleted in local. Print nothing. */
		}
	      else
		{
		  /* Updated in remote, deleted in local */
		  enter_structural_conflict (ctxt, local_side, "Deleted\n", out);
		  enter_structural_conflict (ctxt, remote_side, NULL, out);
		  substrprint (rem_data->text, out);
		  enter_structural_conflict (ctxt, no_conflict, "Updated\n", out);
		}
	    }
	  else
	    {
	      /* Deleted in both. Print nothing. */
	    }
	}
    }
  else
    {
      if (loc_data != NULL)
	{
	  if (rem_data != NULL)
	    {
	      if (substreql (loc_data->text, rem_data->text))
		{
		  /* Both have inserted the same text. Print whichever, normally. */
		  substrprint (loc_data->text, out);
		}
	      else
		{
		  debug_msg(DOC, 3, "Conflict: Local: Inserted, Remote: Inserted\n");
		  /* Both have inserted different text. Conflict. */
		  enter_content_conflict (ctxt, local_side, "Inserted\n", out);
		  substrprint (loc_data->text, out);
		  enter_content_conflict (ctxt, remote_side, NULL, out);
		  substrprint (rem_data->text, out);
		  enter_content_conflict (ctxt, no_conflict, "Inserted\n", out);
		}
	    }
	  else
	    {
	      /* Local insert */
	      substrprint (loc_data->text, out);
	    }
	}
      else
	{
	  if (rem_data != NULL)
	    {
	      /* Remote insert */
	      substrprint (rem_data->text, out);
	    }
	  else
	    {
	      /* Never existed. */
	    }
	}
    }

  debug_msg (DOC, 5, "Done Printing\n");
  return;
}

static bool
org_text_isrelated_op (doc_ref *a_ref, doc_ref *b_ref, merge_ctxt  *ctxt)
{
  /* Two text elements are related if they represent different
   * versions of the same element.  Text objects are always related to
   * each other.
   */

  bool isrelated = false;

  doc_elt *elt_a = doc_ref_get_elt (a_ref);
  doc_elt *elt_b = doc_ref_get_elt (b_ref);

  if ((doc_elt_get_type (elt_a) == ORG_TEXT) &&
      (doc_elt_get_type (elt_b) == ORG_TEXT))
    {
      isrelated = true;
    }

  return isrelated;
}

static int
org_text_compare_op (doc_elt *a, doc_src a_src, doc_elt *b, doc_src b_src)
{
  /**
   * @todo Implement org_text_compare_op.
   */

  return 0;
}

static void
org_text_merge_op (doc_ref *a_ref, doc_ref *b_ref, merge_ctxt *ctxt)
{

  /**
   * @todo Ensure both elt's are org_text when merging.
   */

  debug_msg (DOC_ELT, 5, "Merging org_text\n");

  org_text *a_text = (org_text *) doc_ref_get_elt (a_ref);
  org_text *b_text = (org_text *) doc_ref_get_elt (b_ref);

  assert (a_text != NULL);
  assert (b_text != NULL);

  /* Merge data from b into a */
  int i = 0;
  for (i = 0; i < 3; i++)
    {
      if (a_text->data[i] == NULL)
	a_text->data[i] = b_text->data[i];
    }

  /* There is no other data to merge, so return; */
  return;
}

static bool
org_text_isupdated_op (doc_ref *ref)
{
  /* Return true if either local or remote texts have changed from the
     ancestor. Do not return true if the ancestor was deleted. */

  doc_elt *elt = doc_ref_get_elt(ref);
  org_text *text = (org_text *)elt;
  org_text_data *anc_data = text->data[ANC_INDEX];
  org_text_data *loc_data = text->data[LOC_INDEX];
  org_text_data *rem_data = text->data[REM_INDEX];

  bool isupdated = false;
  bool loc_isupdated = false;
  bool rem_isupdated = false;

  if (anc_data != NULL)
    {
      if (loc_data != NULL)
	{
	  loc_isupdated = !substreql(anc_data->text, loc_data->text);
	}
      if (rem_data != NULL)
	{
	  rem_isupdated = !substreql(anc_data->text, rem_data->text);
	}
      isupdated = (loc_isupdated || rem_isupdated);
    }
  else
    {
      /* if the node was inserted, ie. one new node */
      if ((loc_data != NULL) || (rem_data != NULL))
	{
	  isupdated = true;
	}
    }
  return isupdated;
}


static void
org_text_note_delete (doc_ref *ref, merge_ctxt *ctxt)
{
  /* org_text does not perform any fallback matching technique.
     Do nothing. */
  return;
}

static void
org_text_note_insert (doc_ref *ref, merge_ctxt *ctxt)
{
  /* org_text does not have global matching, do nothing */
  return;
}

static doc_key *
org_text_get_key (doc_elt * elt)
{
  /* org_text does not have global matching, do nothing */
  /* this function should never be called? */
  abort ();
  return NULL;
}
