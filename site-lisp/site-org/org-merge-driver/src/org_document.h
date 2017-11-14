/**
 * @file org_document.h
 * @brief Defines the root document element
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


#ifndef ORG_DOCUMENT_H
#define ORG_DOCUMENT_H

#include "doc_stream.h"
#include "doc_ref.h"

/* type forward declaration */
struct org_document;
typedef struct org_document org_document;

typedef struct org_heading org_heading;
typedef struct org_text org_text;
typedef struct print_ctxt print_ctxt;

/* shov the ops */
typedef struct doc_elt_ops doc_elt_ops;
extern doc_elt_ops org_document_ops;

/* Constructor, Destructor */
org_document *org_document_create_empty (doc_elt_ops *org_doc_ops);
void org_document_free (org_document *self);

/* Adding sub elements */
void org_document_add_text_last (org_document *document, doc_src src, org_text *text);
void org_document_add_heading_last (org_document *document, doc_src src, org_heading *text);

void org_document_print (org_document *doc, print_ctxt *ctxt, doc_stream *out);
void org_document_merge (org_document *anc, org_document *desc, merge_ctxt *ctxt);


/* will call thes function on its children after it searches for
   itself */
bool
org_document_check_for_loop (org_document *this);

#endif /* ORG_DOCUMENT_H */
