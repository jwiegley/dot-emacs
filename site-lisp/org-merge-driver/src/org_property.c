/**
 * @file org_property.c
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

#include "debug.h"
#include "print.h"
#include "doc_elt_util.h"
#include "doc_elt.h"
#include "org_property.h"

static void org_property_print (doc_ref *ref, print_ctxt *ctxt, doc_stream *out);
static bool org_property_isrelated (doc_ref *ref1, doc_ref *ref2, merge_ctxt *ctxt);
static int org_property_compare (doc_elt *elt1, doc_src src1, doc_elt *elt2, doc_src src2);
static void org_property_merge (doc_ref *ref1, doc_ref *ref2, merge_ctxt *ctxt);
static bool org_property_isupdated (doc_ref *ref);
static void org_property_note_insert (doc_ref *ref, merge_ctxt *ctxt);
static void org_property_note_delete (doc_ref *ref, merge_ctxt *ctxt);
static doc_key * org_property_get_key (doc_elt *);

static bool org_property_content_isupdated (org_property *p, size_t index);

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
static void print (org_property *p, size_t index, print_ctxt *ctxt, doc_stream *out);

typedef struct org_property_data org_property_data;

typedef struct org_property
{
  doc_elt elt;
  org_property_data *data[3];
  bool *moved[2];
} org_property;

typedef struct org_property_data
{
  substr text;  /*< The entire text of the property. */
  substr key;   /*< A substring of text, the property's key. */
  substr value; /*< A substring of text, the property's value. */
} org_property_data;

doc_elt_ops org_property_ops = {
  .print       = org_property_print,
  .compare     = org_property_compare,
  .isrelated   = org_property_isrelated,
  .merge       = org_property_merge,
  .isupdated   = org_property_isupdated,
  .note_delete = org_property_note_delete,
  .note_insert = org_property_note_insert,
  .get_key     = org_property_get_key
};

org_property *
org_property_create_empty(doc_elt_ops *ops)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  org_property *p = calloc (1, sizeof (org_property));
  doc_elt_set_type (&(p->elt), ORG_PROPERTY);
  doc_elt_set_ops (&(p->elt), ops);
  debug_msg (DOC_ELT, 5, "Return = %d\n", p);
  return p;
}

void
org_property_free (org_property *p)
{
  int i = 0;
  for (i = 0; i < 3; i++)
    {
      free (p->data[i]);
    }
  free (p);
  return;
}

static org_property_data *
org_property_data_create ()
{
  return calloc (1, sizeof (org_property_data));
}

void
org_property_initversion (org_property *p, doc_src src)
{
  size_t index = srctoindex (src);
  if (p->data[index] == NULL)
    {
      p->data[index] = org_property_data_create ();
    }
  return;
}

bool
org_property_containsversion (org_property *p, doc_src src)
{
  bool containsversion = false;
  containsversion = (p->data[srctoindex (src)] != NULL);
  return containsversion;
}

void
org_property_set_text (org_property *p,  doc_src src, char *string, size_t length)
{
  size_t index = srctoindex(src);
  assert (p != NULL);
  assert (p->data[index] != NULL);
  if (p->data[index] != NULL)
    {
      p->data[index]->text.string = string;
      p->data[index]->text.length = length;
    }
  return;
}

char *
org_property_get_text_string (org_property *p, doc_src src)
{
  size_t index = srctoindex (src);
  char *string = NULL;

  assert (p != NULL);
  assert (p->data[index] != NULL);

  if (p->data[index] != NULL)
    {
      string =  p->data[srctoindex (src)]->text.string;
    }
  return string;
}

void
org_property_set_text_string (org_property *p, doc_src src, char *string)
{
  size_t index = srctoindex (src);
  assert (p != NULL);
  assert (p->data[index] != NULL);

  p->data[srctoindex (src)]->text.string = string;
  return;
}


size_t
org_property_get_text_length (org_property *p, doc_src src)
{
  size_t index = srctoindex (src);
  assert (p != NULL);
  assert (p->data[index] != NULL);

  return p->data[srctoindex (src)]->text.length;
}

void
org_property_set_text_length (org_property *p, doc_src src, size_t length)
{
  size_t index = srctoindex (src);
  assert (p != NULL);
  assert (p->data[index] != NULL);

  p->data[srctoindex (src)]->text.length = length;
  return;
}

char *
org_property_get_key_string (org_property *p, doc_src src)
{
  return p->data[srctoindex (src)]->key.string;
}

void
org_property_set_key (org_property *p, doc_src src, char *string, size_t length)
{
  assert (p != NULL);
  size_t index = srctoindex (src);
  assert (p->data[index] != NULL);
  org_property_set_key_string (p, src, string);
  org_property_set_key_length (p, src, length);
  return;
}

void
org_property_set_key_string (org_property *p, doc_src src, char *string)
{
  p->data[srctoindex (src)]->key.string = string;
  return;
}

size_t
org_property_get_key_length (org_property *p, doc_src src)
{
  return p->data[srctoindex (src)]->key.length;
}

void
org_property_set_key_length (org_property *p, doc_src src, size_t length)
{
  p->data[srctoindex (src)]->key.length = length;
  return;
}

void
org_property_set_value (org_property *p, doc_src src, char *string, size_t length)
{
  assert (p != NULL);
  size_t index = srctoindex (src);
  assert (p->data[index] != NULL);
  org_property_set_value_string (p, src, string);
  org_property_set_value_length (p, src, length);
  return;
}

char *
org_property_get_value_string (org_property *p, doc_src src)
{
  assert (p!= NULL);
  int index = srctoindex (src);
  assert (p->data[index] != NULL);
  return p->data[index]->value.string;
}

void
org_property_set_value_string (org_property *p, doc_src src, char *string)
{
  p->data[srctoindex (src)]->value.string = string;
  return;
}

size_t
org_property_get_value_length (org_property *p, doc_src src)
{
  int index = srctoindex (src);
  assert (p != NULL);
  assert (p->data[index] != NULL);
  return p->data[index]->value.length;
}

void
org_property_set_value_length (org_property *p, doc_src src, size_t length)
{
  p->data[srctoindex (src)]->value.length = length;
  return;
}

static void
org_property_print (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  doc_elt *elt = doc_ref_get_elt (ref);

  /* Letter | Meaning
   *      U | Updated: An updated element exists in this vesion.
   *      D | Deleted: The element was deleted in this version.
   *      I | Inserted: The element is new, and has no ancestor.
   *      X | Does not exist: The element is unassociated with the version.
   */
  org_property *p = (org_property *)doc_ref_get_elt (ref);

  if (p->data[ANC_INDEX] != NULL)
    {
      if (p->data[LOC_INDEX] != NULL)
        {
          if (p->data[REM_INDEX] != NULL)
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
          if (p->data[REM_INDEX] != NULL)
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
      if (p->data[LOC_INDEX] != NULL)
        {
          if (p->data[REM_INDEX] != NULL)
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
          if (p->data[REM_INDEX] != NULL)
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

static bool
org_property_isrelated (doc_ref *ref1, doc_ref *ref2, merge_ctxt *ctxt)
{
  bool isrelated = false;
  doc_elt *elt1 = doc_ref_get_elt (ref1);
  doc_elt *elt2 = doc_ref_get_elt (ref2);

  if (doc_elt_get_type (elt1) == ORG_PROPERTY)
    {
      if (doc_elt_get_type (elt2) == ORG_PROPERTY)
	{
	  org_property *p1 = (org_property *)(elt1);
	  org_property *p2 = (org_property *)(elt2);
	  org_property_data *data1;
	  org_property_data *data2;

	  if (doc_ref_contains (ref1, ANC_SRC))
	    {
	      data1 = p1->data[ANC_INDEX];
	    }
	  else if (doc_ref_contains (ref1, LOC_SRC))
	    {
	      data1 = p1->data[LOC_INDEX];
	    }
	  else if (doc_ref_contains (ref1, REM_SRC))
	    {
	      data1 = p1->data[REM_INDEX];
	    }

	  if (doc_ref_contains (ref2, ANC_SRC))
	    {
	      data2 = p2->data[ANC_INDEX];
	    }
	  else if (doc_ref_contains (ref2, LOC_SRC))
	    {
	      data2 = p2->data[LOC_INDEX];
	    }
	  else if (doc_ref_contains (ref2, REM_SRC))
	    {
	      data2 = p2->data[REM_INDEX];
	    }
	  isrelated = substreql (data1->key, data2->key);
	}
    }
  return isrelated;
}

static int org_property_compare (doc_elt *elt1, doc_src src1, doc_elt *elt2, doc_src src2)
{
  /**
   * @todo Implement org_property_compare.
   */
  return 0;
}

static void
org_property_merge (doc_ref *ref1, doc_ref *ref2, merge_ctxt *ctxt)
{
  org_property *p1 = (org_property *) doc_ref_get_elt (ref1);
  org_property *p2 = (org_property *) doc_ref_get_elt (ref2);

  if (doc_ref_contains (ref2, ANC_SRC))
    {
      p1->data[ANC_INDEX] = p2->data[ANC_INDEX];
    }
  else if (doc_ref_contains (ref2, LOC_SRC))
    {
      p1->data[LOC_INDEX] = p2->data[LOC_INDEX];
    }
  else if (doc_ref_contains (ref2, REM_SRC))
    {
      p1->data[REM_INDEX] = p2->data[REM_INDEX];
    }
  return;
}

static bool
org_property_isupdated (doc_ref *ref)
{
  /* isupdated is used to conflict deletes and other things that might
   * affect this element.  Currently, any change to the entire
   * property, will conflict.  Eventually, this may change to match
   * value updates only, and ignore indentation.
   */

  bool isupdated = false;
  org_property *p = (org_property *)doc_ref_get_elt (ref);

  if (doc_ref_contains (ref, ANC_SRC))
    {
      bool loc_isupdated = false;
      bool rem_isupdated = false;
      if (doc_ref_contains (ref, LOC_SRC)
	  && org_property_content_isupdated(p, LOC_INDEX))
	{
	  isupdated = true;
	}
	else if (doc_ref_contains (ref, REM_SRC)
		 && org_property_content_isupdated (p, REM_SRC))
	{
	  isupdated = true;
	}
    }
  else if (doc_ref_contains (ref, LOC_SRC)
	   || doc_ref_contains (ref, REM_SRC))
    {
      isupdated = true;
    }

  return isupdated;
}

static bool
org_property_content_isupdated (org_property *p, size_t index)
{
  bool isupdated = false;
  org_property_data *anc_data;
  anc_data = p->data[ANC_INDEX];

  /* Check each version located at ref for updates.  If a version's
     data is nonexistant, then do not count that as an update.*/
  if (anc_data != NULL)
    {
      if (p->data[index] != NULL)
        {
          isupdated = !substreql (p->data[index]->value, anc_data->value);
        }
    }
  else if (p->data[index] != NULL)
    isupdated = true;

  return isupdated;
}

static void
org_property_note_insert (doc_ref *ref, merge_ctxt *ctxt)
{
  /**
   * @todo Implement org_property_insert.
   */

  /* org_properties implement local search matching. */
}

static void
org_property_note_delete (doc_ref *ref, merge_ctxt *ctxt)
{
  /**
   * @todo Implement org_property_delete.
   */
}

static void
print_LU_RU (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  org_property *p = (org_property *) doc_ref_get_elt (ref);
  bool loc_moved = p->moved[LOC_INDEX];
  bool rem_moved = p->moved[REM_INDEX];
  bool loc_ishere = doc_ref_contains (ref, LOC_SRC);
  bool rem_ishere = doc_ref_contains (ref, REM_SRC);

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
                  enter_structural_conflict (ctxt, local_side, "Moved\n", out);
                  print_LR (ref, ctxt, out);
                  enter_structural_conflict (ctxt, remote_side, NULL, out);
                  enter_structural_conflict (ctxt, no_conflict, "Moved\n", out);
                }
            }
          else
            {
              if (rem_ishere)
                {
                  enter_structural_conflict (ctxt, local_side, "Moved\n", out);
                  enter_structural_conflict (ctxt, remote_side, NULL, out);
                  print_LR (ref, ctxt, out);
                  enter_structural_conflict (ctxt, no_conflict, "Moved\n", out);
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
            }
          else
            {
            }
        }
    }
  return;
}

static void
print_LU_RD (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  doc_elt *elt = doc_ref_get_elt (ref);
  org_property *p = (org_property *)elt;
  bool local_ishere = doc_ref_contains (ref, LOC_SRC);

  if (local_ishere)
    {
      if (org_property_content_isupdated (p, LOC_INDEX))
        {
          enter_structural_conflict (ctxt, local_side, NULL, out);
          print_L (ref, ctxt, out);
          enter_structural_conflict (ctxt, remote_side, NULL, out);
          enter_structural_conflict (ctxt, no_conflict, "Deleted\n", out);
        }
    }
  return;
}

static void
print_LD_RU (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  doc_elt *elt = doc_ref_get_elt (ref);
  org_property *p = (org_property *)elt;
  bool remote_ishere = doc_ref_contains (ref, REM_SRC);

  if (remote_ishere)
    {
      if (org_property_content_isupdated (p, REM_INDEX))
        {
          enter_structural_conflict (ctxt, local_side, "Deleted\n", out);
          enter_structural_conflict (ctxt, remote_side, NULL, out);
          print_R (ref, ctxt, out);
          enter_structural_conflict (ctxt, no_conflict, NULL, out);
        }
    }
  return;
}

static void
print_LD_RD (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  return;
}

static void
print_LI_RI (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  bool loc_ishere = doc_ref_contains (ref, LOC_SRC);
  bool rem_ishere = doc_ref_contains (ref, REM_SRC);

  if (loc_ishere && rem_ishere)
    {
      print_LR (ref, ctxt, out);
    }
  return;
}

static void
print_LI_RX (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  bool loc_ishere = doc_ref_contains (ref, LOC_SRC);
  if (loc_ishere)
    {
      print_L (ref, ctxt, out);
    }
  return;
}

static void
print_LX_RI (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  bool rem_ishere = doc_ref_contains (ref, REM_SRC);
  if (rem_ishere)
    {
      print_R (ref, ctxt, out);
    }
  return;
}

static void
print_LX_RX (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  return;
}

static void
print_LR (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");

  org_property *p = (org_property *)doc_ref_get_elt (ref);
  bool loc_isupdated = org_property_content_isupdated (p, LOC_INDEX);
  bool rem_isupdated = org_property_content_isupdated (p, REM_INDEX);

  if (loc_isupdated)
    {
      if (rem_isupdated)
        {
	  if (!substreql (p->data[LOC_INDEX]->text, p->data[REM_INDEX]->text))
	    {
	      enter_content_conflict (ctxt, local_side, "Updated\n", out);
	      print (p, LOC_INDEX, ctxt, out);
	      enter_content_conflict (ctxt, remote_side, NULL, out);
	      print (p, REM_INDEX, ctxt, out);
	      enter_content_conflict (ctxt, no_conflict, "Updated\n", out);
	    }
	  else
	    {
	      /* They are exactly the same, print whichever. */
	      print (p, LOC_INDEX, ctxt, out);
	    }
        }
      else
        {
          print (p, LOC_INDEX, ctxt, out);
        }
    }
  else
    {
      if (rem_isupdated)
        {
          print (p, REM_INDEX, ctxt, out);
        }
      else
        {
          print (p, ANC_INDEX, ctxt, out);
        }
    }

  debug_msg (DOC_ELT, 5, "Return\n");
  return;
}

static void
print_L (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  org_property *p = (org_property *)doc_ref_get_elt (ref);
  print (p, LOC_INDEX, ctxt, out);
  debug_msg (DOC_ELT, 5, "Return\n");
  return;
}

static void
print_R (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  org_property *p = (org_property *)doc_ref_get_elt (ref);
  print (p, REM_INDEX, ctxt, out);
  debug_msg (DOC_ELT, 5, "Return\n");
  return;
}

static void
print (org_property *p, size_t index,  print_ctxt *ctxt, doc_stream *out)
{
  /**
   * @todo Deal with indentation in a sane way.
   */
  debug_msg (DOC_ELT, 5, "Begin\n");
  substrprint (p->data[index]->text, out);
  debug_msg (DOC_ELT, 5, "Return\n");
  return;
}

static doc_key *
org_property_get_key (doc_elt *elt)
{
  return NULL;
}
