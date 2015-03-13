/**
 * @file doc_ref.h
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

#ifndef DOC_REF_H
#define DOC_REF_H

#include <stdlib.h>
#include "gl_list.h"
#include "doc_stream.h"

struct doc_elt;
typedef struct doc_elt doc_elt;
typedef struct merge_ctxt merge_ctxt;
typedef struct doc_ref doc_ref;

/**
 * Indicates an input document (ancestor, local, or source). Used to
 * indicate the document from which a doc_* object originates.
 */
typedef enum doc_src
  {
    ANC_SRC = 1,
    REM_SRC = 2,
    LOC_SRC = 4
  } doc_src;

/**
 * A reference to a doc_elt.  It is used to keep track of what files a
 * merged document represents.
 */
typedef struct doc_ref
{
  doc_src src;
  doc_elt *elt;
  doc_ref *parent;
  bool circular_conflict;
} doc_ref;

/* Constructor and destructor */
static inline doc_ref *doc_ref_create_empty ();
static inline void doc_ref_free (doc_ref *ref);

/* Set the doc_elt reference */
static inline doc_elt * doc_ref_get_elt (doc_ref *ref);
static inline void doc_ref_set_elt (doc_ref *ref, doc_elt *elt);

/* Set the doc_src this file represents */
static inline doc_src doc_ref_get_src (doc_ref *ref);
static inline void doc_ref_set_src (doc_ref *ref, doc_src src);
static inline void doc_ref_add_src (doc_ref *ref, doc_src src);
static inline bool doc_ref_isexactly (doc_ref *ref, doc_src src);
static inline bool doc_ref_contains (doc_ref *ref, doc_src src);
static inline doc_ref *doc_ref_get_parent (doc_ref *ref);
static inline void doc_ref_set_parent (doc_ref *ref, doc_ref* parent);

void doc_reflist_note_insert (gl_list_t reflist, merge_ctxt *ctxt);
void doc_reflist_note_delete (gl_list_t reflist, merge_ctxt *ctxt);

/* circular conflict */
static inline bool doc_ref_is_circular_conflict (doc_ref *ref);
static inline void doc_ref_set_circular_conflict (doc_ref *ref, bool conflict);
/* check for a circulor conflic, and mark it in all doc_refs */
static inline bool dec_ref_check_for_circular_conflict (doc_ref *ref);

/*
 * doc_reflist
 */
/**
 * @brief Check to see if any of the elemets in a list of doc_refs are
 * updated.
 * This depends on the element's implementation of this.
 * This function will stop early if it finds a response.
 */
bool doc_reflist_isupdated (gl_list_t reflist);

/**
 * @brief Merge two doc_ref lists together.  This function changes ancestor.
 */
void doc_reflist_merge (doc_ref *parent, gl_list_t ancestor, gl_list_t descendant, merge_ctxt *ctxt);

/**
 * @brief print a list of ref_docs
 */
void doc_reflist_print (gl_list_t reflist, void *context, doc_stream *out);

/*
 * Implementation Details
 */

static inline doc_ref *
doc_ref_create_empty ()
{
  doc_ref *d = malloc (sizeof (doc_ref));
  d->elt = NULL;
  d->src = 0;
  d->parent = NULL;
  d->circular_conflict = false;
  return d;
}

static inline void
doc_ref_free (doc_ref *ref)
{
  free (ref);
}

static inline doc_elt *
doc_ref_get_elt (doc_ref *ref)
{
  return ref->elt;
}

static inline void
doc_ref_set_elt (doc_ref *ref, doc_elt *elt)
{
  ref->elt = elt;
  return;
}

static inline doc_src
doc_ref_get_src (doc_ref *ref)
{
  return ref->src;
}

static inline void
doc_ref_set_src (doc_ref *ref, doc_src src)
{
  ref->src = src;
  return;
}

static inline void
doc_ref_add_src (doc_ref *ref, doc_src src)
{
  ref->src = ref->src | src;
  return;
}

static inline bool
doc_ref_isexactly (doc_ref *ref, doc_src src)
{
  return (ref->src == src);
}

static inline bool
doc_ref_contains (doc_ref *ref, doc_src src)
{
  return (ref->src & src);
}


static inline doc_ref *doc_ref_get_parent (doc_ref *ref)
{
  return ref->parent;
}

static inline void doc_ref_set_parent (doc_ref *ref, doc_ref* parent)
{
  ref->parent = parent;
  return;
}

static inline bool doc_ref_is_circular_conflict (doc_ref *ref)
{
  return ref->circular_conflict;
}

static inline void doc_ref_set_circular_conflict (doc_ref *ref, bool conflict)
{
  ref->circular_conflict = conflict;
}

/* check for a circulor conflict, and mark it in all doc_refs */
static inline bool doc_ref_check_for_circular_conflict (doc_ref *ref)
{
  bool exit = false;
  bool conflict = false;

  doc_ref *parent = doc_ref_get_parent (ref);

  while ((parent != NULL)
          && (!conflict)
          && !(doc_ref_is_circular_conflict(parent)))
    {
      printf ("checking parent par=%d, ref=%d\n",
              doc_ref_get_elt (parent), doc_ref_get_elt (ref));

      if (doc_ref_get_elt (parent) == doc_ref_get_elt (ref))
        {
          printf ("CIRCULAR CONFLICT\n");
          conflict = true;
        }
      parent = doc_ref_get_parent ( parent );
    }

  /* set the doc_refs as having a conflict, if there was one */
  exit = false;
  if (conflict)
    {
      doc_ref * parent = doc_ref_get_parent (ref);
      while ( (parent != NULL) && (!exit))
        {
          if (doc_ref_get_elt (parent) == doc_ref_get_elt (ref))
            {
              exit = true;
            }
          doc_ref_set_circular_conflict (parent, true);
          parent = doc_ref_get_parent (parent);
        }
    }

  printf ("conflict = %d\n", conflict);
  return conflict;
}

#endif /* DOC_REF_H */
