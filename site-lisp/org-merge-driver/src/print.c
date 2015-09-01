/**
 * @file print.c
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

#include <stdlib.h>
#include "doc_stream.h"
#include "print_ctxt.h"
#include "print.h"

static const char *start_mark  = ">>>>>>> ";
static const char *middle_mark = "======= ";
static const char *end_mark    = "<<<<<<< ";

/*
 * Print the conflict markers
 */
static void
print_conflict_markers (conflict_state *current_state, conflict_state state,
                        char* msg, doc_stream *out);


void
enter_structural_conflict (print_ctxt *ctxt, conflict_state state,
			   char* msg, doc_stream *out)
{
  /* wrap up the conflicts, print a message on the last conflict
   * marker, if there is one */

  if ( ctxt->structure_conflict != state )
    {
      enter_movement_conflict (ctxt, no_conflict, NULL, out);
    }
  else
    return;

  if (state != no_conflict)
    ctxt->conflict_occurred = true;

  print_conflict_markers (&ctxt->structure_conflict, state, msg, out);

  return;
}

void
enter_movement_conflict (print_ctxt *ctxt, conflict_state state,
                         char* msg, doc_stream *out)
{
  /* wrap up the conflicts, print a message on the last conflict
   * marker, if there is one */
  if ( ctxt->movement_conflict != state )
    {
      enter_content_conflict (ctxt, no_conflict, NULL, out);
    }
  else
    return;

  if (state != no_conflict)
    ctxt->conflict_occurred = true;

  print_conflict_markers (&ctxt->movement_conflict, state, msg, out);

  return;
}

void
enter_content_conflict (print_ctxt *ctxt, conflict_state state,
			char* msg, doc_stream *out)
{
  if (ctxt->content_conflict == state)
    return;

  if (state != no_conflict)
    ctxt->conflict_occurred = true;

  print_conflict_markers (&ctxt->content_conflict, state, msg, out);

  return;
}

static void
print_conflict_markers (conflict_state *current_state, conflict_state state,
                        char* msg, doc_stream *out)
{

  while (*current_state != state )
    {
      /*conflict wrap up */
      switch (*current_state)
	{
	case no_conflict:
	  doc_stream_puts (start_mark, out);
	  break;
	case local_side:
	  doc_stream_puts (middle_mark, out);
	  break;
	case remote_side:
	  doc_stream_puts (end_mark, out);
	  break;
	}
      (*current_state) ++;

      if (*current_state == 3)
	*current_state = 0;

      if (*current_state != state)
	doc_stream_putc ('\n', out);
    }

  if (msg != NULL)
    {
      doc_stream_puts (msg, out);
    }
  else
    {
      doc_stream_putc ('\n', out);
    }
  return;
}
