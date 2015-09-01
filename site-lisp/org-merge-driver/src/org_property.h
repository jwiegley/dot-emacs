/**
 * @file org_property.h
 * @brief Defines a property element
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


#ifndef ORG_PROPERTY_H
#define ORG_PROPERTY_H

typedef struct org_property org_property;
extern  doc_elt_ops org_property_ops;

org_property *org_property_create_empty (doc_elt_ops *ops);
void org_property_free (org_property *p);
void org_property_initversion (org_property *p, doc_src src);
bool org_property_containsversion (org_property *p, doc_src src);

void org_property_set_text (org_property *p,  doc_src src, char *string, size_t length);
char * org_property_get_text_string (org_property *p, doc_src src);
size_t org_property_get_text_length (org_property *p, doc_src src);

void org_property_set_key (org_property *p, doc_src src, char *string, size_t length);
char * org_property_get_key_string (org_property *p, doc_src src);
size_t org_property_get_key_length (org_property *p, doc_src src);
void org_property_set_key_string (org_property *p, doc_src src, char *string);
void org_property_set_key_length (org_property *p, doc_src src, size_t length);

void org_property_set_value (org_property *p, doc_src src, char *string, size_t length);
char * org_property_get_value_string (org_property *p, doc_src src);
void org_property_set_value_string (org_property *p, doc_src src, char *string);
size_t org_property_get_value_length (org_property *p, doc_src src);
void org_property_set_value_length (org_property *p, doc_src src, size_t length);

#endif
