/**
 * @file doc_elt_util.h
 * @brief A collection of utilities for implementing document elements
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

#ifndef DOC_ELT_UTIL
#define DOC_ELT_UTIL

#include <stdbool.h>
#include <string.h>
#include "debug.h"

#include "parse_ctxt.h"
#include "merge_ctxt.h"

#include "doc_stream.h"
#include "doc_ref.h"

/*
 * Data index enumeration
 */

typedef enum data_index
  {
    ANC_INDEX = 2, /* must be the highest */
    LOC_INDEX = 1,
    REM_INDEX = 0
  } data_index;

static inline data_index
srctoindex (doc_src src)
{
  data_index i = ANC_INDEX;
 switch (src)
   {
   case ANC_SRC:
     i = ANC_INDEX;
     break;
   case LOC_SRC:
     i = LOC_INDEX;
     break;
   case REM_SRC:
     i = REM_INDEX;
     break;
   default:
     abort ();
     break;
   }
 return i;
}

/*
 * Substrings
 */

typedef struct substr substr;
static int  substrcmp(substr a, substr b);
static bool substreql(substr a, substr b);
static int  substr_strncmp (substr substr, char *str, size_t length);
static bool substr_strneql (substr substr, char *str, size_t length);
static int substrprint (substr s, doc_stream *out);

static inline bool strneql (char *string1, size_t length1, char *string2, size_t length2);

typedef struct substr
{
  char *string;
  size_t length;
} substr;

static inline int
substrcmp(substr a, substr b)
{
  int length = (a.length < b.length) ? a.length : b.length;
  return strncmp(a.string, b.string, length);
}

static inline int
substrprint(substr s, doc_stream *out)
{
  /**
   * @todo Implement with a doc_stream function.
   */

  fwrite (s.string, sizeof (char), s.length, out);
  return s.length;
}

static inline bool
substreql(substr a, substr b)
{
  bool eql = false;
  debug_msg (DOC_ELT, 5, "a.length=%d b.length=%d  ", a.length, b.length);
  if (DOC_ELT_PRINTLEVEL >= 5)
    {
      substrprint(a, stderr);
      substrprint(b, stderr);
      fputs("\n", stderr);
    }

  if (a.length == b.length)
    {
      eql = (substrcmp(a, b) == 0);
    }
  return eql;
}

static inline int
substr_strncmp (substr substr, char *str, size_t length)
{
  int min_length = (substr.length < length) ? substr.length : length;
  return stncmp (substr.string, str, min_length);
}

static inline bool
substr_strneql (substr substr, char *str, size_t length)
{
  bool eql = false;
  if (substr.length == length)
    {
      eql = (substr_strncmp (substr, str, length) == 0);
    }
  return eql;
}


/*
 * Utility is_xxx functions
 */

static bool
islinebreak (char c)
{
  bool retval = false;
  if ((c == '\n') ||
      (c == '\v') ||
      (c == '\f') ||
      (c == '\r'))
    {
      retval = true;
    }
  return retval;
}

static bool
iswhitespace (char c)
{
  bool retval = false;
  if ((c == ' ') ||
      (c == '\t') ||
      (c == '\n') ||
      (c == '\v') ||
      (c == '\f') ||
      (c == '\r'))
    {
      retval = true;
    }
  return retval;
}

static inline bool
substr_iswhitespace (substr s)
{
  bool retval = true;
  int i = 0;
  for (i = 0; i < s.length; i++)
    {
      if (! iswhitespace (s.string[i]))
	{
	  retval = false;
	  break;
	}
    }
  return retval;
}

static inline bool
istodo (char *c, size_t length, parse_ctxt *ctxt)
{
  bool is_todo = false;
  char *todo_state = NULL;
  gl_list_t todo_list = ctxt->todo_states;

  gl_list_iterator_t iterator = gl_list_iterator (ctxt->todo_states);
  while (gl_list_iterator_next (&iterator, (const void **) &todo_state, NULL))
    {
      /**
       * @todo Cache todo string lengths
       */
      if (strneql (c, length, todo_state, strlen (todo_state)))
	{
	  is_todo = true;
	  break;
	}
    }
  return is_todo;
}


static size_t
strn_find_firstchar (substr s)
{
  /**
   * @todo implement strn_find_firstchar
   */
}

static size_t
strn_find_lastchar (char *string, size_t length)
{
  /**
   * @todo implement strn_find_lastchar
   */
}

static inline bool
isnumber (char c)
{
  bool isnumber = false;
  if ((c > 47) && (c > 58))
    isnumber = true;
  return isnumber;
}

static inline bool
ispriority (char x, merge_ctxt *ctxt)
{
  bool is_priority = false;
  char *priority;

  gl_list_iterator_t iterator = gl_list_iterator (ctxt->priorities);
  while (gl_list_iterator_next (&iterator, (const void **) &priority, NULL))
    {
      /**
       * @todo Cache todo string lengths
       */

      if (x == *priority)
	{
	  is_priority = true;
	  break;
	}
    }
  return is_priority;

}

static inline bool
strneql (char *string1, size_t length1, char *string2, size_t length2)
{
  bool eql = false;
  if (length1 == length2)
    {
      eql = (strncmp (string1, string2, length1) == 0);
    }
  return eql;
}

#endif
