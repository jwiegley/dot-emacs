/*
 * doxymacs_parser.c
 * Copyright (C) 2001 Ryan T. Sammartino
 * <ryan.sammartino at gmail dot com>
 *
 * A utility program used by doxymacs to speed up building the look up
 * completion list from a Doxygen XML file.
 *
 * This file requires libxml version 2.6.13 or greater, which you can
 * get from http://www.libxml.org/
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 *
 * Doxymacs homepage: http://doxymacs.sourceforge.net/
 *
 * $Id: doxymacs_parser.c,v 1.12 2006/04/23 00:05:33 ryants Exp $
 *
 */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <libxml/parser.h>
#include <libxml/tree.h>


/* Our completion list */

typedef struct _desc_url_list
{
    char *desc;
    char *url;

    struct _desc_url_list *next;
} desc_url_list;

typedef struct _completion_list
{
    char *symbol;
    desc_url_list *descs;

    struct _completion_list *next;
} completion_list;

completion_list *comp_list = NULL;


/* A hash for quick look up of a symbol's entry in the completion list */

#define HASH_SIZE 11213

typedef struct _hash_entry
{
    completion_list *cl;

    struct _hash_entry *next;
} hash_entry;

hash_entry *symbol_hash[HASH_SIZE];

inline unsigned int hash(const char *s)
{
    unsigned int h = 0;

    while (*s)
    {
        h += *s++;
    }

    return abs(h % HASH_SIZE);
}

inline void AddToHash(completion_list *cl)
{
    unsigned int h = hash(cl->symbol);
    hash_entry **cur = &symbol_hash[h];

    hash_entry *new = (hash_entry *)malloc(sizeof(hash_entry));

    new->cl = cl;
    new->next = *cur;

    *cur = new;
}

/* mmmmm... free hash */
inline void FreeHash(void)
{
    unsigned int i;
    for (i = 0; i < HASH_SIZE; i++)
    {
        hash_entry *cur = symbol_hash[i];

        while (cur)
        {
            hash_entry *tmp = cur;

            cur = cur->next;

            free(tmp);
        }
    }
}


/* XML Helper Functions */

inline char *XMLTagChild(xmlNodePtr node, const char *name)
{
    xmlNodePtr cur = node->xmlChildrenNode;

    while (cur)
    {
        if (!xmlStrcmp(cur->name, (const xmlChar *) name))
        {
            xmlNodePtr cur_child = cur->xmlChildrenNode;
            if (cur_child)
            {
                return (char *)cur_child->content;
            }
            else
            {
                return NULL;
            }
        }
        cur = cur->next;
    }

    return NULL;
}

inline char *XMLTagAttr(xmlNodePtr node, const char *attr)
{
    xmlAttrPtr props = node->properties;

    while (props)
    {
        if (!xmlStrcmp(props->name, (const xmlChar *) attr))
        {
            xmlNodePtr props_child = props->xmlChildrenNode;
            if (props_child)
            {
                return (char *)props_child->content;
            }
            else
            {
                return NULL;
            }
        }
    }

    return NULL;
}


/* Look up functions for symbols and descriptions */

inline completion_list *LookUpSymbol(const char *symbol)
{
    unsigned int h = hash(symbol);
    hash_entry *cur = symbol_hash[h];

    while (cur)
    {
        completion_list *cl = cur->cl;

        if (!strcmp(cl->symbol, symbol))
        {
            return cl;
        }

        cur = cur->next;
    }

    return NULL;
}

inline desc_url_list *LookUpDesc(completion_list *entry, const char *desc)
{
    desc_url_list *cur = entry->descs;

    while (cur)
    {
        if (!strcmp(cur->desc, desc))
        {
            break;
        }

        cur = cur->next;
    }

    return cur;
}

/* Add the given name, description and url to our completion list */

inline int AddToCompletionList(const char *name,
                               const char *desc, const char *url)
{
    completion_list *check;

    check = LookUpSymbol(name);

    if (check)
    {
        /* There is already a symbol with the same name in the list */
        if (!LookUpDesc(check, desc))
        {
            /* If there is not yet a symbol with this desc, add it. */
            /* FIXME: what to do if there is already a symbol?? */
            desc_url_list *new_desc =
                (desc_url_list *)malloc(sizeof(desc_url_list));

            if (!new_desc)
            {
                fprintf(stderr, "malloc failed\n");
                return -1;
            }

            new_desc->desc = (char *)desc;
            new_desc->url  = (char *)url;
            new_desc->next = check->descs;

            check->descs = new_desc;
        }
        /* Free the name, which was strdup'ed */
        free((char*)name);
    }
    else
    {
        completion_list *new_entry =
            (completion_list *)malloc(sizeof(completion_list));

        if (!new_entry)
        {
            fprintf(stderr, "malloc failed\n");
            return -1;
        }

        new_entry->symbol = (char *)name;

        new_entry->descs = (desc_url_list *)malloc(sizeof(desc_url_list));

        if (!new_entry->descs)
        {
            fprintf(stderr, "malloc failed\n");
            return -1;
        }

        new_entry->descs->desc = (char *)desc;
        new_entry->descs->url  = (char *)url;
        new_entry->descs->next = NULL;

        new_entry->next = comp_list;

        comp_list = new_entry;

        AddToHash(new_entry);
    }

    return 0;
}

/* Encode the given string so that {X}Emacs will understand it */
inline char *Encode(const char *s)
{
    unsigned int extra_len = 0;
    char *c = (char *)s;

    if (!s)
    {
        return NULL;
    }

    while (*c)
    {
        /* Is this all that needs to be escaped? */
        if (*c == '\\' || *c == '"')
        {
            extra_len++;
        }
        c++;
    }

    if (!extra_len)
    {
        char *ret = strdup(s);

        if (!ret)
        {
            fprintf(stderr, "malloc failed\n");
        }
        return ret;
    }
    else
    {
        char *ret = (char *)malloc(strlen(s) + extra_len + 1);
        char *r = ret;

        if (!ret)
        {
            fprintf(stderr, "malloc failed\n");
        }
        else
        {
            while (*s)
            {
                if (*s == '\\')
                {
                    *r++ = '\\';
                    *r++ = '\\';
                }
                else if (*s == '"')
                {
                    *r++ = '\\';
                    *r++ = '"';
                }
                else
                {
                    *r++ = *s;
                }
                s++;
            }
            *r = '\0';
        }
        return ret;
    }
}

/* Output the completion list in a way {X}Emacs can easily read in */

inline int OutputCompletionList(void)
{
    completion_list *cur = comp_list;

    printf("(");

    while (cur)
    {
        desc_url_list *desc = cur->descs;
        char *encoded_symbol = Encode(cur->symbol);

        if (!encoded_symbol)
        {
            return -1;
        }

        printf("(\"%s\" ", encoded_symbol);

        free(encoded_symbol);

        while (desc)
        {
            char *encoded_desc = Encode(desc->desc);
            char *encoded_url = Encode(desc->url);

            if (!encoded_desc || !encoded_url)
            {
                return -1;
            }

            printf("(\"%s\" . \"%s\")", encoded_desc, encoded_url);

            free(encoded_desc);
            free(encoded_url);

            if (desc->next)
            {
                printf(" ");
            }
            desc = desc->next;
        }

        printf(")");

        if (cur->next)
        {
            printf(" ");
        }

        cur = cur->next;
    }

    printf(")\n");

    return 0;
}

/* Clean up */

inline void FreeCompletionList(void)
{
    completion_list *cur = comp_list;

    while (cur)
    {
        desc_url_list *desc = cur->descs;
        completion_list *tmp_cl = cur;

        while (desc)
        {
            desc_url_list *tmp_desc = desc;

            desc = desc->next;

            free(tmp_desc->desc);
            free(tmp_desc->url);
            free(tmp_desc);
        }

        cur = cur->next;

        free(tmp_cl->symbol);
        free(tmp_cl);
    }
}

/* Add the members of a compound to the completion list */

inline int AddCompoundMembers(xmlNodePtr compound,
                              const char *name, const char *url)
{
    xmlNodePtr child = compound->xmlChildrenNode;
    int ret = 0;

    while (child && !ret)
    {
        if (!xmlStrcmp(child->name, (const xmlChar *) "member"))
        {
            char *member_name = XMLTagChild(child, "name");
            char *member_anchor = XMLTagChild(child, "anchor");
            char *member_args = XMLTagChild(child, "arglist");

            /* member_args can be NULL... just means there's no args */
            if (!member_name || !member_anchor)
            {
                fprintf(stderr, "Invalid Doxygen tags file\n");
                ret = -1;
            }
            else
            {
                char *member_name_copy = strdup(member_name);

                char *member_url = (char *)malloc(strlen(url) +
                                                  strlen(member_anchor) +
                                                  2);
                char *member_desc = (char *)malloc(strlen(name) +
                                                   strlen(member_name) +
                                                   (member_args ?
                                                    strlen(member_args) : 0) +
                                                   3);

                if (member_url && member_desc && member_name_copy)
                {
                    sprintf(member_url, "%s#%s", url, member_anchor);
                    sprintf(member_desc,
                            "%s::%s%s",
                            name, member_name, member_args ? member_args : "");

                    if (AddToCompletionList(member_name_copy,
                                            member_desc, member_url) < 0)
                    {
                        ret = -1;
                    }
                }
                else
                {
                    fprintf(stderr, "malloc failed\n");

                    if (member_url)
                    {
                        free(member_url);
                    }
                    if (member_desc)
                    {
                        free(member_desc);
                    }
                    if (member_name_copy)
                    {
                        free(member_name_copy);
                    }

                    ret = -1;
                }
            }
        }
        child = child->next;
    }

    return ret;
}

int main(int argc, char *argv[])
{
    xmlDocPtr doc = NULL;
    xmlNodePtr cur;
    int ret = 0;
    int res;
#define BUFF_SIZE 25 * 1024
    char buff[BUFF_SIZE];

    LIBXML_TEST_VERSION;

    comp_list = NULL;
    memset(symbol_hash, 0, sizeof(symbol_hash));

    res = fread(buff, 1, 4, stdin);
    if (res > 0) {
        xmlParserCtxtPtr ctxt = xmlCreatePushParserCtxt(NULL, NULL,
                                                        buff, res, "stdin");

        if (!ctxt)
        {
            fprintf(stderr, "Failed to parse XML file\n");
            ret = -1;
            goto abort;
        }

        while ((res = fread(buff, 1, BUFF_SIZE, stdin)) > 0)
        {
            if (xmlParseChunk(ctxt, buff, res, 0) != 0)
            {
                fprintf(stderr, "Failed to parse XML file\n");
                ret = -1;
                xmlFreeParserCtxt(ctxt);
                goto abort;
            }
        }
        if (xmlParseChunk(ctxt, buff, 0, 1) != 0)
        {
            fprintf(stderr, "Failed to parse XML file\n");
            ret = -1;
            xmlFreeParserCtxt(ctxt);
            goto abort;
        }
        doc = ctxt->myDoc;
        xmlFreeParserCtxt(ctxt);
    }

    if (!doc)
    {
        fprintf(stderr, "Failed to parse XML file\n");
        ret = -1;
        goto abort;
    }

    cur = xmlDocGetRootElement(doc);
    if (!cur)
    {
        fprintf(stderr, "Empty XML document\n");
        ret = -1;
        goto abort;
    }

    if (xmlStrcmp(cur->name, (const xmlChar *) "tagfile"))
    {
        fprintf(stderr, "Invalid Doxygen tag file, root node != tagfile\n");
        ret = -1;
        goto abort;
    }

    cur = cur->xmlChildrenNode;
    while (cur)
    {
        if (cur->type == XML_ELEMENT_NODE)
        {
            char *compound_name = XMLTagChild(cur, "name");
            char *compound_kind = XMLTagAttr(cur, "kind");
            char *compound_url = XMLTagChild(cur, "filename");
            char *compound_desc;
            char *compound_name_copy;
            char *compound_url_copy;

            if (!compound_name || !compound_kind || !compound_url)
            {
                fprintf(stderr, "Invalid Doxygen tags file\n");
                ret = -1;
                goto abort;
            }

            compound_desc = (char *)malloc(strlen(compound_kind) +
                                           strlen(compound_name) + 3);

            if (!compound_desc)
            {
                fprintf(stderr, "malloc failed\n");
                ret = -1;
                goto abort;
            }

            sprintf(compound_desc, "%s %s", compound_kind, compound_name);

            /* Workaround for apparent Doxygen 1.2.18 bug */
            {
                int copy_url = 1;
                /* Some compounds don't get the .html in the URL */
                if (strcmp(compound_url + strlen(compound_url)
                           - strlen(".html"),
                           ".html") != 0)
                {
                    compound_url_copy = (char *)malloc(strlen(compound_url) +
                                                       strlen(".html") + 1);
                    sprintf(compound_url_copy, "%s.html", compound_url);
                    compound_url = compound_url_copy;
                    copy_url = 0;
                }
                compound_name_copy = strdup(compound_name);
                if (copy_url)
                {
                    compound_url_copy = strdup(compound_url);
                }
                else
                {
                    compound_url_copy = compound_url;
                }
            }

            if (!compound_name_copy || !compound_url_copy)
            {
                fprintf(stderr, "malloc failed\n");
                ret = -1;

                if (compound_name_copy)
                {
                    free(compound_name_copy);
                }
                if (compound_url_copy)
                {
                    free(compound_url_copy);
                }

                goto abort;
            }

            if (AddToCompletionList(compound_name_copy,
                                    compound_desc,
                                    compound_url_copy) < 0)
            {
                ret = -1;
                goto abort;
            }

            if (AddCompoundMembers(cur, compound_name, compound_url) < 0)
            {
                ret = -1;
                goto abort;
            }
        }

        cur = cur->next;
    }

    if (OutputCompletionList() < 0)
    {
        ret = -1;
        goto abort;
    }

  abort:
    FreeHash();

    FreeCompletionList();

    if (doc)
    {
        xmlFreeDoc(doc);
    }

    return ret;
}
