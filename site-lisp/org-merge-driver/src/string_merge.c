/**
 * @file string_merge.c
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

#include "string.h"
#include "assert.h"
#include "stddef.h"
#include <limits.h>
#include <stdbool.h>
#include "minmax.h"

#include "debug.h"
#include "doc_elt_util.h"
#include "doc_ref.h"
#include "doc_stream.h"
#include "print.h"

#include "string_merge.h"

#define OFFSET int

void
substr_print_merge (substr loc_text, substr rem_text, print_ctxt *ctxt, doc_stream *out)
{
  line_diff (loc_text.string, loc_text.length, rem_text.string, rem_text.length,
	     ctxt, out);
  return;
}

void
line_diff (char *loc_s, size_t loc_len, char *rem_s, size_t rem_len,
	   print_ctxt *print_ctxt, doc_stream *out)
{

  /*
   * Scan the amount of lines in each string, create a state for each
   * line, camopareseq the lines, print the merged lines
   */
  size_t loc_line_count, rem_line_count;
  loc_line_count = count_lines (loc_s, loc_len);
  rem_line_count = count_lines (rem_s, rem_len);

  debug_msg (DOC, 5, "START: loc: len=%d, lines=%d\n"
	     "       rem: len=%d, lines=%d\n",
	     loc_len, loc_line_count, rem_len, rem_line_count);

  /* create a index into the strings */
  size_t *loc_lines = malloc (sizeof (size_t) * (loc_line_count + 1));
  index_lines (loc_lines, loc_s, loc_len);

  size_t *rem_lines = malloc (sizeof (size_t) * (rem_line_count + 1));
  index_lines (rem_lines, rem_s, rem_len);

  /* store if a line has a match or not, initialized to false */
  bool *loc_state = calloc (loc_line_count, sizeof (bool));
  bool *rem_state = calloc (rem_line_count, sizeof (bool));

  /* calculate the mappings */
  string_index_compareseq (loc_s, loc_line_count, loc_lines, loc_state,
			   rem_s, rem_line_count, rem_lines, rem_state);

  /* print the diff'd lines */
  size_t loc_index = 0;
  size_t rem_index = 0;

  while ( loc_index < loc_line_count ||
	  rem_index < rem_line_count )
    {
      if ((loc_index < loc_line_count) &&
	  (loc_state[loc_index] == unmapped))
	{
	  debug_msg (DOC, 5, "note:\n");
	  size_t loc_length = loc_lines[loc_index+1] - loc_lines[loc_index];
	  enter_content_conflict (print_ctxt, local_side, "Updated\n", out);
	  doc_stream_fwrite (loc_s + loc_lines[loc_index], sizeof (char),
			     loc_length, out);
	  loc_index++;
	}
      else if ((rem_index < rem_line_count) &&
	       (rem_state[rem_index] == unmapped))
	{
	  debug_msg (DOC, 5, "note:\n");
	  size_t rem_length = rem_lines[rem_index+1] - rem_lines[rem_index];
	  enter_content_conflict (print_ctxt, remote_side, "\n", out);
	  doc_stream_fwrite (rem_s + rem_lines[rem_index], sizeof (char),
			     rem_length, out);
	  rem_index++;
	}
      else if (rem_state[rem_index] == mapped &&
	       loc_state[loc_index] == mapped)
	{
	  debug_msg (DOC, 5, "note:\n");
	  size_t loc_length = loc_lines[loc_index+1] - loc_lines[loc_index];
	  enter_content_conflict (print_ctxt, no_conflict, "Updated\n", out);
	  doc_stream_fwrite (loc_s + loc_lines[loc_index], sizeof (char),
			     loc_length, out);
	  rem_index++;
	  loc_index++;
	}
    }
  /* finish up any conflict markers if the loop left a conflicted state */
  enter_content_conflict (print_ctxt, no_conflict, "Updated\n", out);

  free (loc_lines);
  free (rem_lines);
  free (loc_state);
  free (rem_state);

  return;
}

void
line_diff_only_known_overlap3 (char *anc_s, size_t anc_len, char *loc_s, size_t loc_len,
	    char *rem_s, size_t rem_len, print_ctxt *print_ctxt, doc_stream *out)
{
  /*
   * Scan the amount of lines in each string, create a state for each
   * line, camopareseq the lines, print the merged lines
   */
  size_t anc_line_count, loc_line_count, rem_line_count;
  anc_line_count = count_lines (anc_s, anc_len);
  loc_line_count = count_lines (loc_s, loc_len);
  rem_line_count = count_lines (rem_s, rem_len);

  debug_msg (DOC, 5, "\nSTART: loc: len=%d, lines=%d\n"
	     "       rem: len=%d, lines=%d\n"
	     "       anc: len=%d, lines=%d\n",
	     loc_len, loc_line_count, rem_len, rem_line_count, anc_len, anc_line_count);

  /* create a index into the strings */
  size_t *anc_lines = malloc (sizeof (size_t) * (anc_line_count + 1));
  index_lines (anc_lines, anc_s, anc_len);

  size_t *loc_lines = malloc (sizeof (size_t) * (loc_line_count + 1));
  index_lines (loc_lines, loc_s, loc_len);

  size_t *rem_lines = malloc (sizeof (size_t) * (rem_line_count + 1));
  index_lines (rem_lines, rem_s, rem_len);

  /* store if a line has a match or not, initialized to false */
  bool *loc_anc_state = calloc (anc_line_count, sizeof (bool));
  bool *loc_state     = calloc (loc_line_count, sizeof (bool));
  bool *rem_anc_state = calloc (anc_line_count, sizeof (bool));
  bool *rem_state     = calloc (rem_line_count, sizeof (bool));

  /* calculate the mappings for ancestor and local */
  string_index_compareseq (anc_s, anc_line_count, anc_lines, loc_anc_state,
			   loc_s, loc_line_count, loc_lines, loc_state);

  /* calculate the mappings for ancestor and remote */
  string_index_compareseq (anc_s, anc_line_count, anc_lines, rem_anc_state,
			   rem_s, rem_line_count, rem_lines, rem_state);

  /* print merge the objects */
  size_t loc_index     = 0;
  size_t loc_anc_index = 0;
  size_t rem_index     = 0;
  size_t rem_anc_index = 0;

  while ( loc_index < loc_line_count ||
	  rem_index < rem_line_count )
    {
      if ((loc_index < loc_line_count) &&
	  (loc_state[loc_index] == unmapped))
	{
	  if ((rem_index < rem_line_count) &&
	      (rem_state[rem_index] == unmapped))
	    {
	      /* overlapping inserts, print all local inserts,
	       * followed by all remote inserts in conflict markers.
	       * Stop printing when the next element is not an
	       * insert */
	      enter_content_conflict (print_ctxt, local_side, "Updated\n", out);
	      while ((loc_index < loc_line_count) &&
		     (loc_state[loc_index] == unmapped))
		{
		  /* print all local unmapped */
		  size_t loc_length = loc_lines[loc_index+1] - loc_lines[loc_index];
		  doc_stream_fwrite (loc_s + loc_lines[loc_index], sizeof (char),
				     loc_length, out);
		  loc_index ++;
		}

	      enter_content_conflict (print_ctxt, remote_side, "\n", out);
	      while ((rem_index < rem_line_count) &&
		     (rem_state[rem_index] == unmapped))
		{
		  /* print all remote unmapped */
		  size_t rem_length = rem_lines[rem_index+1] - rem_lines[rem_index];
		  doc_stream_fwrite (rem_s + rem_lines[rem_index], sizeof (char),
				     rem_length, out);
		  rem_index ++;
		}

	      enter_content_conflict (print_ctxt, no_conflict, "Updated\n", out);
	    }
	  else
	    {
	      /* insert only in local */
	      while ((loc_index < loc_line_count) &&
		     (loc_state[loc_index] == unmapped))
		{
		  /* print all local unmapped */
		  enter_content_conflict (print_ctxt, no_conflict, "Updated\n", out);
		  size_t loc_length = loc_lines[loc_index+1] - loc_lines[loc_index];
		  doc_stream_fwrite (loc_s + loc_lines[loc_index], sizeof (char),
				     loc_length, out);
		  loc_index++;
		}
	    }
	}
      else if ((rem_index < rem_line_count) &&
	       (rem_state[rem_index] == unmapped))
	{
	  /* insert in remote only */
	  enter_content_conflict (print_ctxt, no_conflict, "Updated\n", out);
	  size_t rem_length = rem_lines[rem_index+1] - rem_lines[rem_index];
	  doc_stream_fwrite (rem_s + rem_lines[rem_index], sizeof (char),
			     rem_length, out);
	  rem_index++;
	}
      else if (rem_index < rem_line_count &&
	       loc_index < loc_line_count &&
	       rem_state[rem_index] == mapped &&
	       loc_state[loc_index] == mapped)
	{
	  /* two mapped lines, print one of them:
	   * advance the ancestor pointers untill they are both 'mapped'
	   * if the both the remote and local have the same ancestor, then print the line
	   * if one of them points to a previos ancestor, it was deleted in the other file
	   *
	   * If an element was deleted in one file, advance the other file
	   * If the element is in both files, advance all files forwards
	   */

	  /* advance the ancestors to the next mapped element */
	  while (rem_anc_state[rem_anc_index] == unmapped &&
		 rem_anc_index < anc_line_count)
	    rem_anc_index ++;
	  assert (rem_anc_state[rem_anc_index] == mapped);

	  while (loc_anc_state[loc_anc_index] == unmapped &&
		 loc_anc_index < anc_line_count)
	    loc_anc_index ++;
	  assert (loc_anc_state[loc_anc_index] == mapped);

	  /* check to see if both elements point to the same ancestor */
	  if (loc_anc_index == rem_anc_index)
	    {
	      /* same line in both files, print it */
	      enter_content_conflict (print_ctxt, no_conflict, "Updated\n", out);
	      size_t rem_length = rem_lines[rem_index+1] - rem_lines[rem_index];
	      doc_stream_fwrite (rem_s + rem_lines[rem_index], sizeof (char),
				 rem_length, out);
	      rem_index++;
	      loc_index++;
	      loc_anc_index++;
	      rem_anc_index++;
	    }
	  else if (loc_anc_index < rem_anc_index)
	    {
	      /* deleted line in remote */
	      loc_index++;
	      loc_anc_index++;
	    }
	  else /* loc_anc_index > rem_anc_index */
	    {
	      /* line deleted in local */
	      rem_index++;
	      rem_anc_index ++;
	    }
	}
    }

  free (anc_lines);
  free (loc_lines);
  free (rem_lines);
  free (loc_anc_state);
  free (loc_state);
  free (rem_anc_state);
  free (rem_state);

  return;
}

void
line_diff3 (char *anc_s, size_t anc_len, char *loc_s, size_t loc_len,
	    char *rem_s, size_t rem_len, print_ctxt *print_ctxt, doc_stream *out)
{
  /*
   * Scan the amount of lines in each string, create a state for each
   * line, camopareseq the lines, print the merged lines
   */
  size_t anc_line_count, loc_line_count, rem_line_count;
  anc_line_count = count_lines (anc_s, anc_len);
  loc_line_count = count_lines (loc_s, loc_len);
  rem_line_count = count_lines (rem_s, rem_len);

  debug_msg (DOC, 5, "\nSTART: loc: len=%d, lines=%d\n"
	     "       rem: len=%d, lines=%d\n"
	     "       anc: len=%d, lines=%d\n",
	     loc_len, loc_line_count, rem_len, rem_line_count, anc_len, anc_line_count);

  /* create a index into the strings */
  size_t *anc_lines = malloc (sizeof (size_t) * (anc_line_count + 1));
  index_lines (anc_lines, anc_s, anc_len);

  size_t *loc_lines = malloc (sizeof (size_t) * (loc_line_count + 1));
  index_lines (loc_lines, loc_s, loc_len);

  size_t *rem_lines = malloc (sizeof (size_t) * (rem_line_count + 1));
  index_lines (rem_lines, rem_s, rem_len);

  /* store if a line has a match or not, initialized to false */
  bool *loc_anc_state = calloc (anc_line_count, sizeof (bool));
  bool *loc_state     = calloc (loc_line_count, sizeof (bool));
  bool *rem_anc_state = calloc (anc_line_count, sizeof (bool));
  bool *rem_state     = calloc (rem_line_count, sizeof (bool));

  /* calculate the mappings for ancestor and local */
  string_index_compareseq (anc_s, anc_line_count, anc_lines, loc_anc_state,
			   loc_s, loc_line_count, loc_lines, loc_state);

  /* calculate the mappings for ancestor and remote */
  string_index_compareseq (anc_s, anc_line_count, anc_lines, rem_anc_state,
			   rem_s, rem_line_count, rem_lines, rem_state);

  /* print merge the objects */
  size_t loc_index     = 0;
  size_t loc_extent    = 0;
  size_t anc_index     = 0;
  size_t rem_index     = 0;
  size_t rem_extent    = 0;


  debug_msg (DOC, 5,"starting the merge\n");

  bool extent_found = false, loc_update = false, rem_update = false;
  int changes = 0;
  int rem_mapped_count = 0, loc_mapped_count = 0;

  while ( loc_index < loc_line_count ||
	  rem_index < rem_line_count )
    {
      /* calculate the range of the extent */
      extent_found = false;
      loc_update = false;
      rem_update = false;
      changes = 0;
      rem_mapped_count = 1;
      loc_mapped_count = 1;

      /* find mapped ancestor */
      while ((anc_index < anc_line_count) &&
	     ((rem_anc_state[anc_index] == unmapped) ||
	      (loc_anc_state[anc_index] == unmapped)))
	{
	  if (rem_anc_state[anc_index] == mapped)
	      rem_mapped_count ++;

	  if (loc_anc_state[anc_index] == mapped)
	      loc_mapped_count ++;

	  anc_index ++;
	}

      /* ancestor index now points to a mutualy mapped line.
       * mapped_count = mapped elements, including the element the extent points to
       */

      /* find the local extent */
      int mapped_count = 0;
      while (loc_extent < loc_line_count)
	{
	  if (loc_state[loc_extent] == mapped)
	    mapped_count ++;
	  else
	    loc_update = true;

	  /* if the element is at the correct spot, break eaply to
	     keep it from incrementing one last time */
	  if (mapped_count >= loc_mapped_count)
	    break;

	  loc_extent ++;
	}

      /* find the remote extent */
      mapped_count = 0;
      while (rem_extent < rem_line_count)
	{
	  if (rem_state[rem_extent] == mapped)
	    mapped_count ++;
	  else
	    rem_update = true;

	  if (mapped_count >= rem_mapped_count)
	    break;

	  rem_extent++;
	}

      /* the remote and local extents should be pointing at a ancestor
	 element in both files */

      /* set the extent to one before the matched element */
      debug_msg (DOC, 5, "anc_index=%d\n", anc_index);
      debug_msg (DOC, 5, "loc_index=%d  rem_index=%d\n", loc_index, rem_index);
      debug_msg (DOC, 5, "loc_update=%d  rem_update=%d\n", loc_update, rem_update);
      debug_msg (DOC, 5, "mapped in rem, count=%d\n", rem_mapped_count);
      debug_msg (DOC, 5, "mapped in loc, count=%d\n", loc_mapped_count);
      debug_msg (DOC, 5, "extents are loc=%d, rem=%d\n", loc_extent, rem_extent);

      if (loc_update)
	{
	  if (rem_update)
	    {
	      /* conflict both sides */
	      /* overlapping inserts, print all local inserts,
	       * followed by all remote inserts in conflict markers.
	       * Stop printing when the next element is not an
	       * insert */
	      enter_content_conflict (print_ctxt, local_side, "Updated\n", out);
	      while (loc_index < loc_extent)
		{
		  /* print all local unmapped */
		  size_t loc_length = loc_lines[loc_index+1] - loc_lines[loc_index];
		  doc_stream_fwrite (loc_s + loc_lines[loc_index], sizeof (char),
				     loc_length, out);
		  loc_index ++;
		}

	      enter_content_conflict (print_ctxt, remote_side, "\n", out);
	      while (rem_index < rem_extent)
		{
		  /* print all remote unmapped */
		  size_t rem_length = rem_lines[rem_index+1] - rem_lines[rem_index];
		  doc_stream_fwrite (rem_s + rem_lines[rem_index], sizeof (char),
				     rem_length, out);
		  rem_index ++;
		}

	      enter_content_conflict (print_ctxt, no_conflict, "Updated\n", out);
	    }
	  else /* !rem_update */
	    {
	      /* print local side */
	      while (loc_index < loc_extent)
		{
		  if (loc_state[loc_index] == unmapped)
		    {
		      /* print all local unmapped */
		      size_t loc_length = loc_lines[loc_index+1] - loc_lines[loc_index];
		      doc_stream_fwrite (loc_s + loc_lines[loc_index], sizeof (char),
					 loc_length, out);
		    }
		  loc_index ++;
		}
	    }
	}
      else if (rem_update)
	{
	  /* print remote side */
	  while ((rem_index < rem_extent) &&
		 (rem_state[rem_index] == unmapped))
	    {
	      if (rem_state[rem_index] == unmapped)
		{
		  /* print all remote unmapped */
		  size_t rem_length = rem_lines[rem_index+1] - rem_lines[rem_index];
		  doc_stream_fwrite (rem_s + rem_lines[rem_index], sizeof (char),
				     rem_length, out);
		}
	      rem_index ++;
	    }
	}

      /* print the element at the extent */
      if (rem_extent < rem_line_count)
	{
	  /* same line in both files, print it */
	  enter_content_conflict (print_ctxt, no_conflict, "Updated\n", out);
	  size_t rem_length = rem_lines[rem_index+1] - rem_lines[rem_index];
	  doc_stream_fwrite (rem_s + rem_lines[rem_index], sizeof (char),
			     rem_length, out);

	  loc_index = loc_extent+1;
	  rem_index = rem_extent+1;

	  loc_extent++;
	  rem_extent++;
	  anc_index++;
	}
      else
	break;
    }

  free (anc_lines);
  free (loc_lines);
  free (rem_lines);
  free (loc_anc_state);
  free (loc_state);
  free (rem_anc_state);
  free (rem_state);

  return;
}
size_t
count_lines (char *string, size_t length)
{
  /* if there are X '\n's, there are (X+1) lines */
  size_t count = 1;
  size_t pos;

  for (pos = 0; pos < length; pos++)
    {
      if (string[pos] == '\n')
	count++;
    }
  return count;
}

void
index_lines (size_t array[], char* string, size_t length)
{
  /* The array will be indexed, such that the start and the end of the
   * string are the first and last elements, and the newlines are
   * marked in between.
   */
  size_t count = 1;
  size_t pos;

  /* the start of the string */
  array[0] = 0;

  /* the newlines */
  debug_msg (DOC, 5, "length: %d\n", length);
  for (pos = 0; pos < length; pos++)
    {
      if (string[pos] == '\n')
	{
	  debug_msg (DOC, 5, "count: %d, pos=%d\n", count, pos);
	  array[count] =  pos+1;
	  count++;
	}
    }

  /* the end of the sring */
  array[count] = length;

  return;
}

struct context;

#undef USE_HEURISTIC
#undef ELEMENT
#undef EQUAL

/* compareseq functions */
static void note_delete (struct context *ctxt, OFFSET xoff);
static void note_insert (struct context *ctxt, OFFSET yoff);
static int  compare     (struct context *ctxt, OFFSET xoff, OFFSET yoff);

/* extra fields for the compareseq context */
#define EXTRA_CONTEXT_FIELDS			\
  bool   *loc_state;				\
  bool   *rem_state;				\
  size_t *loc_indices;				\
  size_t *rem_indices;				\
  char   *loc_string;				\
  char   *rem_string;

/* ised to note adds and deletes in subsequences */
#define NOTE_DELETE(ctxt, xoff) note_delete (ctxt, xoff)
#define NOTE_INSERT(ctxt, yoff) note_insert (ctxt, yoff)
#define XVECREF_YVECREF_EQUAL(ctxt, xoff, yoff) compare (ctxt, xoff, yoff)

#include "diffseq.h"
#define OFFSET int

void
string_index_compareseq (char *loc_string, size_t loc_count,
			 size_t *loc_indices, bool *loc_state,
			 char *rem_string, size_t rem_count,
			 size_t *rem_indices, bool *rem_state)
{

  /* prepare the compareseq context */
  struct context ctxt;

  /* Add the caller data */
  ctxt.loc_state   = loc_state;
  ctxt.loc_indices = loc_indices;
  ctxt.loc_string  = loc_string;

  ctxt.rem_state   = rem_state;
  ctxt.rem_indices = rem_indices;
  ctxt.rem_string  = rem_string;

  /* Allocate data for the algorithm to use*/
  size_t diags = loc_count + rem_count + 3;
  void *mem    = malloc (diags * (2 * sizeof (OFFSET)));
  ctxt.fdiag   = mem;
  ctxt.bdiag   = ctxt.fdiag + diags;
  ctxt.fdiag  += rem_count + 1;
  ctxt.bdiag   = ctxt.fdiag + diags;

  /* run a diffseq on the elements */
  compareseq (0,                     /* children index lower bound   */
	      loc_count,             /* children index upper bound   */
	      0,                     /* children index lower bound   */
	      rem_count,             /* children index upper bound   */
	      1,                     /* find optimal solution        */
	      &ctxt);                /* difseq context created above */

  free (mem);
}

static void
note_delete (struct context *ctxt, OFFSET xoff)
{
  debug_msg (DOC, 5, "delete: %d\n", xoff);
  ctxt->loc_state[xoff] = unmapped;
  return;
}

static void
note_insert (struct context *ctxt, OFFSET yoff)
{
  debug_msg (DOC, 5, "insert: %d\n", yoff);
  ctxt->rem_state[yoff] = unmapped;
  return;
}

static int
compare (struct context *ctxt, OFFSET xoff, OFFSET yoff)
{
  int result = 0;
  size_t loc_length = (ctxt->loc_indices[xoff + 1] - ctxt->loc_indices[xoff]);
  size_t rem_length = (ctxt->rem_indices[yoff + 1] - ctxt->rem_indices[yoff]);

  if (loc_length == rem_length)
    {
      debug_msg (DOC, 5, "length: %d & %d\n", loc_length, rem_length);
      if (strncmp(ctxt->loc_string + ctxt->loc_indices[xoff],
		  ctxt->rem_string + ctxt->rem_indices[yoff], loc_length) == 0)
	result = 1;
    }

  debug_msg (DOC, 5, "compare: %d & %d = %d\n", xoff, yoff, result);
  return result;
}
