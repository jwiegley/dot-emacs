/**
 * @flie print_ctxt.c
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

#include "config.h"
#include "debug.h"
#include "print.h"
#include "stdlib.h"
#include "print_ctxt.h"

/**
 * @brief Set all unset values in CTXT to defaults.
 */
void print_ctxt_set_defaults (print_ctxt *ctxt);

print_ctxt *
print_ctxt_create_empty (void)
{
  print_ctxt *ctxt = calloc (1, sizeof (print_ctxt));
  return ctxt;
}

void
print_ctxt_init (print_ctxt *ctxt)
{
  ctxt->depth = 0;
  ctxt->current_level = 0;
  ctxt->rmargin = 0;
  ctxt->tab_width = 0;
  ctxt->use_tabs = 0;
  ctxt->print_state = print_merged;
  ctxt->nested_conflicts = no_conflict;
  ctxt->structure_conflict = no_conflict;
  ctxt->content_conflict = no_conflict;
  ctxt->movement_conflict = no_conflict;
  ctxt->conflict_occurred = false;
  return;
}

void
print_ctxt_set_defaults (print_ctxt *ctxt)
{
  if (ctxt->rmargin == 0)
    {
      ctxt->rmargin = 77;
    }
  if (ctxt->tab_width == 0)
    {
      ctxt->tab_width = 8;
    }
  return;
}
