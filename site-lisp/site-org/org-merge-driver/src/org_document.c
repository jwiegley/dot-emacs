/**
 * @file org_document.c
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
#include "config.h"
#include "gl_array_list.h"
#include "gl_list.h"
#include "merge_ctxt.h"
#include "doc_elt.h"
#include "org_heading.h"
#include "org_text.h"

#include "org_document.h"

struct org_document
{
  doc_elt elt;
  gl_list_t subheadings;
  gl_list_t subtext;
};

typedef struct org_document org_document;

/* Forward Declarations */
static doc_elt_ops_print     org_print_op;
static doc_elt_ops_isrelated org_isrelated_op;
static doc_elt_ops_compare   org_compare_op;
static doc_elt_ops_merge     org_merge_op;
static doc_elt_ops_isupdated org_isupdated_op;

/* Declaration of org_element operations table */
doc_elt_ops org_document_ops = {
  /* printing */
  .print         = &org_print_op,
  /* comparing */
  .isrelated     = &org_isrelated_op,
  .compare       = &org_compare_op,
  /* merging */
  .merge         = &org_merge_op,
  .isupdated     = &org_isupdated_op
};

/* Constructor, Destructor */
org_document *
org_document_create_empty (doc_elt_ops *ops)
{
  org_document *d = malloc (sizeof (org_document));
  doc_elt_set_ops (&(d->elt), ops);
  doc_elt_set_type (&(d->elt), ORG_DOCUMENT);
  d->subheadings = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL,
					    NULL, NULL, true);
  d->subtext = gl_list_nx_create_empty (GL_ARRAY_LIST, NULL,
					NULL, NULL, true);
  return d;
}

void
org_document_free (org_document *self)
{
  free (self);
}

/* Adding sub elements */
void
org_document_add_text_last (org_document *document, doc_src src, org_text *text)
{
  /* wrap the element in a doc_ref, and add it to the list */
  doc_ref *ref = doc_ref_create_empty ();
  doc_ref_set_src (ref, src);
  doc_ref_set_elt (ref, (doc_elt *) text);
  /* tell the doc ref that the parent is immovable */
  doc_ref_set_parent (ref, NULL);
  gl_list_nx_add_last (document->subtext, ref);
  return;
}

void
org_document_add_heading_last (org_document *document, doc_src src, org_heading *heading)
{
  /* wrap the element in a doc_ref, and add it to the list */
  doc_ref *ref = doc_ref_create_empty ();
  doc_ref_set_src (ref, src);
  doc_ref_set_elt (ref, (doc_elt *) heading);
  /* tell the doc ref that the parent is immovable */
  doc_ref_set_parent (ref, NULL);
  org_heading_set_doc_ref (heading, ref);
  gl_list_nx_add_last (document->subheadings, ref);
  return;
}

void
org_document_print (org_document *doc, print_ctxt *ctxt, doc_stream *out)
{
  debug_msg (DOC_ELT, 3, "Print merging org_document\n");
  debug_msg (DOC_ELT, 5, "Printing text\n");
  doc_reflist_print (doc->subtext, ctxt, out);
  debug_msg (DOC_ELT, 3, "Printing headings\n");
  doc_reflist_print (doc->subheadings, ctxt, out);
  return;
}

void
org_document_merge (org_document *anc, org_document *desc, merge_ctxt *ctxt)
{
  debug_msg (DOC_ELT, 3, "Merging org_document\n");
  debug_msg (DOC_ELT, 5, "Merging text\n");
  doc_reflist_merge (NULL, anc->subtext, desc->subtext, ctxt);
  debug_msg (DOC_ELT, 3, "Merging headings\n");
  doc_reflist_merge (NULL, anc->subheadings, desc->subheadings, ctxt);
  return;
}

/* doc_elt interface */
static void
org_print_op (doc_ref *ref, print_ctxt *ctxt, doc_stream *out)
{
  /**
   * @todo make sure the doc merge print
   */
  org_document *doc = (org_document *) doc_ref_get_elt (ref);
  org_document_print (doc, ctxt, out);
  return;
}

static bool
org_isrelated_op (doc_ref *local, doc_ref *remote, merge_ctxt *ctxt)
{
  /* all org_documents are relatable */
  return true;
}

static int
org_compare_op (doc_elt *a, doc_src a_src, doc_elt *b, doc_src b_src)
{
  /* all org_documents are identical */
  return true;
}

static void
org_merge_op (doc_ref *a, doc_ref *b, merge_ctxt *ctxt)
{
  /**
   * @todo actually merge things
   */
  return;
}

static bool
org_isupdated_op (doc_ref *a)
{
  /**
   * @todo implement an actual function
   */
  /* check if the children are updated */
  /* check if this element is updated */
  return true;
}

/* will call thes function on its children after it searches for
   itself */
bool
org_document_check_for_loop (org_document *this)
{
  /* first check to see if the target exist anywhere below */
  gl_list_iterator_t i;
  i = gl_list_iterator (this->subheadings);
  doc_ref *ref = NULL;
  bool found =  false;
  org_heading *heading;

  debug_msg (DOC,3, "checking for loops");
  while (gl_list_iterator_next (&i, (const void **) &ref, NULL))
    {
      heading = (org_heading *)doc_ref_get_elt (ref);

      org_heading_check_for_loop (heading);
    }

  gl_list_iterator_free (&i);
  return found;
}
