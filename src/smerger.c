/**
 * @flie smerger.c
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

#include <string.h>

#include "config.h"
#include "gl_rbtree_list.h"
#include "gl_list.h"
#include "doc_elt.h"
#include "doc_ref.h"
#include "smerger.h"

#include "org_heading.h"

static inline gl_list_t smerger_list_create ();
static inline doc_ref *smerger_match_remove (gl_list_t list, doc_ref *ref, merge_ctxt *ctxt);
static inline int smerger_remove_exactly (gl_list_t list, doc_ref *ref);
static inline int smerger_merge (doc_ref *ancestor, doc_ref *descendant, merge_ctxt *ctxt);
static inline int smerger_store (gl_list_t list, doc_ref *ref);

static int smerger_compare (const void *a, const void *b);
static bool smerger_equals (const void *obj_a, const void *obj_b);
static int doc_key_cmp (doc_key *a, doc_key *b);


typedef struct smerger
{
  gl_list_t insert_list;
  gl_list_t delete_list;
} smerger;


smerger *
smerger_create ()
{
  debug_msg (SMERGER, 5, "Begin\n");

  smerger *sm = malloc (sizeof (smerger));
  sm->insert_list = smerger_list_create();
  sm->delete_list = smerger_list_create();

  debug_msg (SMERGER, 5, "Return =%d\n", sm);
  return sm;
}

static inline gl_list_t
smerger_list_create ()
{
  debug_msg (SMERGER, 5, "Begin\n");
  gl_list_t list =  gl_list_nx_create_empty (GL_RBTREE_LIST, smerger_equals,
					     NULL, NULL, true);
  debug_msg (SMERGER, 5, "Return =%d\n", list);
  return list;
}

void
smerger_free (smerger *sm)
{
  debug_msg (SMERGER, 5, "Begin\n");

  gl_list_free (sm->insert_list);
  gl_list_free (sm->delete_list);
  free (sm);

  debug_msg (SMERGER, 5, "Return\n");
  return;
}

int
smerger_register_insert (smerger *sm, doc_ref *ref, merge_ctxt *ctxt)
{
  debug_msg (SMERGER, 5, "Begin\n");
  int status = 0;

  doc_ref *match = smerger_match_remove (sm->delete_list, ref, ctxt);
  if (match != NULL)
    {
      smerger_merge (match, ref, ctxt);
    }
  else
    {
      smerger_store (sm->insert_list, ref);
    }

  debug_msg (SMERGER, 5, "Return =%d\n", status);
  return status;
}

int
smerger_unregister_insert (smerger *sm, doc_ref *ref)
{
  debug_msg (SMERGER, 5, "Begin\n");
  int status = 0;

  status = smerger_remove_exactly (sm->insert_list, ref);

  debug_msg (SMERGER, 5, "Return =%d\n", status);
  return status;
}

int
smerger_register_delete (smerger *sm, doc_ref *ref, merge_ctxt *ctxt)
{
  debug_msg (SMERGER, 5, "Begin\n");
  int status = 0;

  doc_ref *match = smerger_match_remove (sm->insert_list, ref, ctxt);
  if (match != NULL)
    {
      smerger_merge (ref, match, ctxt);
    }
  else
    {
      smerger_store (sm->delete_list, ref);
    }

  debug_msg (SMERGER, 5, "Return =%d\n", status);
  return status;
}

int
smerger_unregister_delete(smerger *sm, doc_ref *ref)
{
  debug_msg (SMERGER, 5, "Begin\n");
  int status = 0;

  status = smerger_remove_exactly (sm->delete_list, ref);

  debug_msg (SMERGER, 5, "Return =%d\n", status);
  return status;
}

/**
 * Find a match for REF in LIST.
 */

static inline doc_ref *
smerger_match_remove (gl_list_t list, doc_ref *ref, merge_ctxt *ctxt)
{
  debug_msg (SMERGER, 5, "Begin\n");

  doc_ref        *match    = NULL;
  gl_list_node_t listnode  = NULL;
  int            last_pos  = 0;
  int            size      = gl_list_size (list);

  bool done_searching = false;
  while (!done_searching)
    {
      debug_msg(SMERGER, 5, "Searching from pos=%d\n", last_pos);
      last_pos = gl_sortedlist_indexof_from_to (list,
						smerger_compare,
                                                last_pos,
                                                size,
                                                (const void *) ref);
      debug_msg(SMERGER, 5, "Found possible match at pos=%d\n", last_pos);

      if (last_pos == -1)
        {
	  debug_msg (SMERGER, 3, "No Match Found\n");
	  match = NULL;
          done_searching = true;
        }
      else
	{
          match = (doc_ref *)gl_list_get_at (list, last_pos);
	  bool isrelated = false;
	  isrelated = doc_elt_isrelated (ref, match, ctxt);
	  debug_msg (SMERGER, 3, "Match isrelated =%d\n", isrelated);

	  if (isrelated == true)
	    {
	      debug_msg (SMERGER, 3, "Match Found\n");
	      gl_list_remove_at (list, last_pos);
	      done_searching = true;
	    }
	  else
	    {
	      last_pos++;
	    }
	}
    }

  debug_msg (SMERGER, 5, "Return =%d\n", match);
  return match;
}

static inline int
smerger_remove_exactly ( gl_list_t list, doc_ref *ref)
{
  debug_msg (SMERGER, 5, "Begin\n");
  int status = -1;

  /**
   * @todo Implement smerger_remove_exactly.
   */

  debug_msg (SMERGER, 5, "Return =%d\n", status);
  return status;
}

/**
 * Merge the element stored by DESCENDANT into the doc_elt stored by
 * ANCESTOR, and set DESCENDANT's elt to the newly merged ancestor
 * element.
 */
static inline int
smerger_merge (doc_ref *ancestor, doc_ref *descendant, merge_ctxt *old_ctxt)
{
  debug_msg (SMERGER, 5, "Begin\n");
  int status = 0;
  doc_elt *anc_elt = doc_ref_get_elt (ancestor);

  /* Clone the context */
  merge_ctxt new_ctxt = *old_ctxt;
  //memcpy (&new_ctxt, ctxt, sizeof (merge_ctxt));

  /* Modify the strategy to indicate */
  new_ctxt.strategy = GLOBAL_SEARCH_MERGE;

  doc_elt_merge (ancestor, descendant, &new_ctxt);
  doc_ref_set_elt (descendant, anc_elt);

  debug_msg (SMERGER, 5, "Return =%d\n", status);
  return status;
}

/**
 * Store REF in LIST.
 */
static inline int
smerger_store (gl_list_t list, doc_ref *ref)
{
  debug_msg (SMERGER, 5, "Begin\n");
  int status = 0;

  gl_sortedlist_nx_add (list, smerger_compare, (const void *)ref);

  debug_msg (SMERGER, 5, "Return =%d\n", status);
  return status;
}

static int
smerger_compare (const void *a, const void *b)
{
  debug_msg (SMERGER, 5, "Begin\n");

  int cmp = 0;

  doc_ref *a_ref = (doc_ref *)a;
  doc_ref *b_ref = (doc_ref *)b;
  doc_elt *a_elt = doc_ref_get_elt (a_ref);
  doc_elt *b_elt = doc_ref_get_elt (b_ref);
  doc_key *a_key = doc_elt_get_key (a_elt);
  doc_key *b_key = doc_elt_get_key (b_elt);

  cmp = doc_key_cmp (a_key, b_key);

  debug_msg (SMERGER, 5, "Return =%d\n", cmp);
  return cmp;
}

static bool
smerger_equals (const void *obj_a, const void *obj_b)
{
  debug_msg (DOC_ELT, 5, "Begin\n");
  /* smerger_equals is used by the underlying gl_list to test two
   * objects for true equality.  The gl_list stores doc_refs, which in
   * turn point to doc_elts.  Two objects are considered equal if
   * their doc_elt's are related.  Relatedness is tested for using
   * doc_elt_isrelated from the generic doc_elt interface.
   */
  return doc_elt_isrelated ((doc_ref *)obj_a, (doc_ref *)obj_b, NULL);
}

int
doc_key_cmp (doc_key *a, doc_key *b)
{
  debug_msg (SMERGER, 5, "Begin\n");

  int cmp = 0;
  int minlength = (a->length < b->length) ? a->length : b->length;

  if (SMERGER_PRINTLEVEL > 4)
    {
      debug_msg (SMERGER, 4, "A ='");
      fwrite ( a->string, sizeof (char), a->length, stderr);
      fprintf (stderr, "'\n");
      debug_msg (SMERGER, 4, "B ='");
      fwrite ( b->string, sizeof (char), b->length, stderr);
      fprintf (stderr, "'\n");
    }

  cmp = strncmp (a->string, b->string, minlength);

  if (cmp == 0)
    {
      if (a->length < b->length)
	{
	  cmp = -1;
	}
      else if (a->length > b->length)
	{
	  cmp = 1;
	}
    }

  debug_msg (SMERGER, 5, "Return = %d\n", cmp);
  return cmp;
}
