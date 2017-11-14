/**
 * @file org_heading.h
 * @brief Defines an org mode heading
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


#ifndef ORG_HEADING_H
#define ORG_HEADING_H

#include "stddef.h"
#include "stdbool.h"

/* org_text forward declaration */
struct org_text;
typedef struct org_text org_text;

/* org_heading forward declaration */
struct org_heading;
typedef struct org_heading org_heading;

typedef struct doc_elt_ops doc_elt_ops;
extern doc_elt_ops org_heading_ops;


/* Constructor, Destructor */
/**
 * @brief Construct an empty org heading element.
 */
org_heading *org_heading_create_empty (doc_elt_ops *elt_ops);

/**
 * @brief Free an org heading.
 */
void org_heading_free (org_heading *self);

/* Getters and Setters */
int org_heading_get_level (org_heading *self, doc_src src);
void org_heading_set_level (org_heading *self, int level, doc_src src);

doc_ref* org_heading_get_doc_ref (org_heading *heading);
void org_heading_set_doc_ref (org_heading *heading, doc_ref *ref);

/**
 * @brief Set the entire text of a heading.
 *
 * This function expects a single line storing an entire heading,
 * including leading stars and any trailing line breaks.  The line
 * will be parsed, and any internal variables will be set. The string
 * is not null terminated.
 */
void org_heading_set_entire_text (org_heading *self, char *string, int length,
				  doc_src src, parse_ctxt *ctxt);

/**
 * @brief Set the key of a heading.
 * This key will be used to identify the heading globally.
 * Set the key to an empty key to disable global matching.
 * The key can be accessed through doc_elt_get_key.
 */
void org_heading_set_key (org_heading *self, char*key, size_t length);

/* Adding sub elements */
/**
 * @brief Add a doc_elt as the last item in the list of text
 * subelements.
 */
void org_heading_add_subtext_last (org_heading *heading, doc_src src, 
				   doc_elt *elt);

/**
 * @brief Add a doc_elt as the last item in the list of heading
 * subelements.
 */
void org_heading_add_subheading_last (org_heading *heading, doc_src src,
				      doc_elt *elt);

/**
 * @brief Set the values of a heading, using information stored in the
 * ctxt */
void org_heading_set_parse_ctxt (org_heading *heading, doc_src src, parse_ctxt *ctxt);

bool org_heading_check_for_target (org_heading *this, org_heading* target);

/* will call the function on its children after it searches for
   itself */
bool org_heading_check_for_loop (org_heading *this);

#endif
