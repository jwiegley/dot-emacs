/**
 * @file doc_elt_ops.h
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

#ifndef DOC_ELT_OPS
#define DOC_ELT_OPS

#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>

#include "doc_stream.h"
#include "doc_ref.h"

/* document element type, from doc_elt.h */
typedef struct doc_elt doc_elt;
/* printing context type, from print.h */
typedef struct print_ctxt print_ctxt;
/* sorting key type,  from doc_elt.h*/
typedef struct doc_key doc_key;
/* merge context type, from doc_elt.h */
typedef struct merge_ctxt merge_ctxt;

typedef struct doc_ref doc_ref;

/* function types for document operations */
/* Printing */
typedef void (doc_elt_ops_print) (doc_ref*, print_ctxt *, doc_stream *);

/* comparing */
typedef int (doc_elt_ops_compare) (doc_elt *, doc_src, doc_elt*, doc_src);
typedef bool (doc_elt_ops_isrelated) (doc_ref *, doc_ref *, merge_ctxt *);

/* merging */
typedef void (doc_elt_ops_merge) (doc_ref *, doc_ref *, merge_ctxt *);
typedef bool (doc_elt_ops_isupdated) (doc_ref *);

/* Global Mapping */
typedef void (doc_elt_ops_note_delete) (doc_ref *, merge_ctxt *);
typedef void (doc_elt_ops_note_insert) (doc_ref *, merge_ctxt *);
typedef doc_key *(doc_elt_ops_get_key) (doc_elt *);

/**
 * The operations for an implementation of a doc_elt
 */
typedef struct doc_elt_ops
{
  /* printing */
  doc_elt_ops_print        *print;         /*< print an element */
  /* comparing */
  doc_elt_ops_compare     *compare;       /*< see if element is updated */
  doc_elt_ops_isrelated   *isrelated;     /*< if elements can be mapped */
  /* merging */
  doc_elt_ops_merge       *merge;         /*< merge an element and all its children */
  doc_elt_ops_isupdated   *isupdated;     /*< check if an element (or children) is updated */
  doc_elt_ops_note_delete *note_delete;   /*< notify an element it was not matched */
  doc_elt_ops_note_insert *note_insert;
  /* Global mapping */
  doc_elt_ops_get_key     *get_key;       /*< get a sorting key from an element */

} doc_elt_ops;

/* constructor, destructor */
static inline doc_elt_ops * doc_elt_ops_create_empty ();
static inline void doc_elt_ops_free (doc_elt_ops *ops);

/* print operation */
static inline doc_elt_ops_print* doc_elt_ops_get_print (doc_elt_ops *ops);
static inline void doc_elt_ops_set_print (doc_elt_ops *ops, doc_elt_ops_print print);

/* compare operation */
static inline doc_elt_ops_compare* doc_elt_ops_get_compare (doc_elt_ops *ops);
static inline void doc_elt_ops_set_compare (doc_elt_ops *ops,
					    doc_elt_ops_compare compare);

/* isrelated operation */
static inline doc_elt_ops_isrelated* doc_elt_ops_get_isrelated (doc_elt_ops *ops);
static inline void doc_elt_ops_set_isrelated (doc_elt_ops *ops,
					      doc_elt_ops_isrelated isrelated);
/* merge operation */
static inline doc_elt_ops_merge* doc_elt_ops_get_merge (doc_elt_ops *ops);
static inline void doc_elt_ops_set_merge (doc_elt_ops *ops, doc_elt_ops_merge merge);

/* isupdated operation */
static inline doc_elt_ops_isupdated* doc_elt_ops_get_isupdated (doc_elt_ops *ops);
static inline void doc_elt_ops_set_isupdated (doc_elt_ops *ops,
					      doc_elt_ops_isupdated isupdated);

/* get_key operation */
static inline doc_elt_ops_get_key* doc_elt_ops_get_get_key (doc_elt_ops *ops);
static inline void doc_elt_ops_set_get_key (doc_elt_ops *ops,
					    doc_elt_ops_get_key get_key);

/* note_insert operation */
static inline doc_elt_ops_note_insert* doc_elt_ops_get_note_insert (doc_elt_ops *ops);
static inline void doc_elt_ops_set_note_insert (doc_elt_ops *ops,
						doc_elt_ops_note_insert insert);

/* note delete operation */
static inline doc_elt_ops_note_delete* doc_elt_ops_get_note_delete (doc_elt_ops *ops);
static inline void doc_elt_ops_set_note_delete (doc_elt_ops *ops,
						doc_elt_ops_note_delete delete);
/*
 * Implementation Details
 */

static inline doc_elt_ops *
doc_elt_ops_create_empty ()
{
  return malloc (sizeof (doc_elt_ops));
}

static inline void
doc_elt_ops_free (doc_elt_ops *ops)
{
  assert (ops != NULL);
  free (ops);
}

static inline doc_elt_ops_print*
doc_elt_ops_get_print (doc_elt_ops *ops)
{
  assert (ops != NULL);
  return ops->print;
}

static inline void
doc_elt_ops_set_print (doc_elt_ops *ops, doc_elt_ops_print print)
{
  assert (ops != NULL);
  ops->print = print;
}

static inline doc_elt_ops_compare*
doc_elt_ops_get_compare (doc_elt_ops *ops)
{
  assert (ops != NULL);
  return ops->compare;
}

static inline void
doc_elt_ops_set_compare (doc_elt_ops *ops, doc_elt_ops_compare compare)
{
  assert (ops != NULL);
  ops->compare = compare;
  return;
}

static inline doc_elt_ops_isrelated*
doc_elt_ops_get_isrelated (doc_elt_ops *ops)
{
  assert (ops != NULL);
  return ops->isrelated;
}

static inline void
doc_elt_ops_set_isrelated (doc_elt_ops *ops, doc_elt_ops_isrelated isrelated)
{
  assert (ops != NULL);
  ops->isrelated = isrelated;
  return;
}

static inline doc_elt_ops_merge*
doc_elt_ops_get_merge (doc_elt_ops *ops)
{
  assert (ops != NULL);
  return ops->merge;
}

static inline void
doc_elt_ops_set_merge (doc_elt_ops *ops, doc_elt_ops_merge merge)
{
  assert (ops != NULL);
  ops->merge = merge;
  return;
}

static inline doc_elt_ops_isupdated*
doc_elt_ops_get_isupdated (doc_elt_ops *ops)
{
  assert (ops != NULL);
  return ops->isupdated;
}

static inline void
doc_elt_ops_set_isupdated (doc_elt_ops *ops, doc_elt_ops_isupdated isupdated)
{
  assert (ops != NULL);
  ops->isupdated = isupdated;
  return;
}

static inline doc_elt_ops_note_insert* doc_elt_ops_get_note_insert (doc_elt_ops *ops)
{
  assert (ops != NULL);
  return ops->note_insert;
}

static inline void doc_elt_ops_set_note_insert (doc_elt_ops *ops,
						doc_elt_ops_note_insert insert)
{
  assert (ops != NULL);
  ops->note_insert = insert;
  return;
}


static inline doc_elt_ops_note_delete* doc_elt_ops_get_note_delete (doc_elt_ops *ops)
{
  assert (ops != NULL);
  return ops->note_delete;
}

static inline void doc_elt_ops_set_note_delete (doc_elt_ops *ops,
						doc_elt_ops_note_delete delete)
{
  assert (ops != NULL);
  ops->note_delete = delete;
  return;
}

static inline
doc_elt_ops_get_key* doc_elt_ops_get_get_key (doc_elt_ops *ops)
{
  assert (ops != NULL);
  return ops->get_key;
}

static inline
void doc_elt_ops_set_get_key (doc_elt_ops *ops,
			      doc_elt_ops_get_key get_key)
{
  assert (ops != NULL);
  ops->get_key = get_key;
  return;
}

#endif /* DOC_ELT_OPS_H */
