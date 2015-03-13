/**
 * @file main.c
 * @brief Main entry point
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
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <iconv.h>
#include <string.h>
#include <argp.h>

#include "debug.h"
#include "gl_list.h"
#include "gl_array_list.h"
#include "doc_stream.h"
#include "doc_ref.h"
#include "print.h"
#include "doc_elt.h"
#include "org_document.h"
#include "org_parser.h"

struct arguments;
typedef struct arguments arguments;

static error_t parse_opt (int key, char *arg, struct argp_state *state);
static void arguments_set_default (arguments *arguments);

const char *argp_program_version =
  "org-merge-driver 0.1\n\
Copywrite (C) 2012 Free Software Foundation, Inc\n\
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>\n\
This is free software: you are free to change and redistribute it.\n\
There is NO WARRANTY, to the extent permitted by law.";

const char *argp_program_bug_address =
  "<youngar17@gmail.com>";

static char doc [] =
  "org-merge-driver\n\
A tool for performing 3 way merges of org-mode formatted plain text documents.";

static char args_doc[] = "ANCESTOR LOCAL REMOTE [OUT]";

static struct argp_option options[] = {
  {"todo",      't',      "STATE",          0, "Specify an accepted todo state" },
  {"priority",  'p',   "PRIORITY",          0, "Specify an accepted prority"},
  {"tabwidth",  'W',      "WIDTH",          0, "The width of tabs in spaces"},
  {"notabs",    'N',            0,          0, "Use only spaces in the output"},
  {"usetabs",   'T',            0,          0, "Use tabs in the output"},
  {"rmargin",   'm',     "COLUMN",          0, "Set the right margin of headings"},
  { 0 }
};

struct arguments
{
  char      *paths[4];
  gl_list_t todo_states;
  gl_list_t priorities;
  bool      verbose;
  size_t    tab_width;
  bool      use_tabs;
  size_t    rmargin;
};

static struct argp argp = { options, parse_opt, args_doc, doc };

main (int argc, char *argv[])
{
  debug_msg (MAIN, 5, "Begin\n");
  error_t exit_status = EXIT_SUCCESS;


  /* Parse Arguments */
  struct arguments arguments;
  error_t error = argp_parse (&argp, argc, argv, 0, 0, &arguments);

  /* Configure the contexts using arguments */
  struct parse_ctxt parse_ctxt;
  parse_ctxt_init (&parse_ctxt);
  if (gl_list_size (arguments.todo_states) > 0)
    {
      parse_ctxt.todo_states = arguments.todo_states;
    }
  parse_ctxt_set_defaults (&parse_ctxt);

  struct merge_ctxt loc_merge_ctxt;
  merge_ctxt_init (&loc_merge_ctxt);
  struct merge_ctxt rem_merge_ctxt;
  merge_ctxt_init (&rem_merge_ctxt);
  if (gl_list_size (arguments.priorities) > 0)
    {
      loc_merge_ctxt.priorities = arguments.priorities;
      rem_merge_ctxt.priorities = arguments.priorities;
    }
  merge_ctxt_set_defaults (&loc_merge_ctxt);
  merge_ctxt_set_defaults (&rem_merge_ctxt);

  struct print_ctxt print_ctxt;
  print_ctxt_init (&print_ctxt);
  print_ctxt.tab_width = arguments.tab_width;
  print_ctxt.use_tabs  = arguments.use_tabs;
  print_ctxt.rmargin   = arguments.rmargin;
  print_ctxt_set_defaults (&print_ctxt);

  /* Parse input files */
  org_document *anc = NULL;
  org_document *loc = NULL;
  org_document *rem = NULL;

  FILE *anc_file = fopen ( arguments.paths[0], "r");

  if (anc_file != NULL)
    {
      debug_msg (MAIN, 4, "File 1 opened\n");
      FILE *loc_file = fopen (arguments.paths[1], "r");
      if (loc_file != NULL)
	{
	  debug_msg (MAIN, 4, "File 2 opened\n");
	  FILE *rem_file = fopen (arguments.paths[2], "r");
	  if (rem_file != NULL)
	    {
	      debug_msg (MAIN, 4, "File 3 opened\n");
	      debug_msg (MAIN, 4, "Parsing Files\n\n");
	      anc = org_parse_file_stream (anc_file, ANC_SRC, &parse_ctxt);
	      loc = org_parse_file_stream (loc_file, LOC_SRC, &parse_ctxt);
	      rem = org_parse_file_stream (rem_file, REM_SRC, &parse_ctxt);
	      fclose (rem_file);
	    }
	  else
	    {
	      fprintf (stderr, "Could not open REMOTE %s\n", arguments.paths[2]);
              exit_status = 2;
	    }
	  fclose (loc_file);
	}
      else
	{
	  fprintf (stderr, "Could not open LOCAL %s\n", arguments.paths[1]);
          exit_status = 2;
	}
      fclose(anc_file);
    }
  else
    {
      fprintf (stderr, "Could not open ANCESTOR %s\n", arguments.paths[0]);
      exit_status = 2;
    }

  if ((anc != NULL) && (loc != NULL) && (rem != NULL))
    {
      /* Merge files */
      debug_msg (MAIN, 4, "Merging Files\n\n");
      debug_msg (MAIN, 4, "Merging anc and loc\n");
      org_document_merge (anc, loc, &loc_merge_ctxt);
      debug_msg (MAIN, 4, "Merging anc and rem\n");
      org_document_merge (anc, rem, &rem_merge_ctxt);

      org_document_check_for_loop (anc);

      debug_msg (MAIN, 3, "Printing\n\n");


      /* Print output */
      /* Open output file */
      FILE * out = NULL;
      if (arguments.paths[3] != NULL)
        {
          out =  fopen ( arguments.paths[3], "w");
          if (out == NULL)
            {
              fprintf (stderr, "Could not open OUT %s\n", arguments.paths[3]);
              exit_status = 2;
            }
        }
      else
        {
          debug_msg (MAIN, 4, "Setting output to stdout\n");
          out = stdout;
        }

      if (out != NULL)
        {
          org_document_print (anc, &print_ctxt, out);
          exit_status = (print_ctxt.conflict_occurred ? 1 : exit_status);

          if (out != stdout)
            {
              fclose (out);
            }
        }
    }

  /* Exit */
  debug_msg (MAIN, 5, "Return =%d\n", exit_status);
  return exit_status;
}

void
arguments_set_default (arguments *arguments)
{
  debug_msg (MAIN, 5, "Begin\n");

  arguments->paths[0] = NULL;
  arguments->paths[1] = NULL;
  arguments->paths[2] = NULL;
  arguments->paths[3] = NULL;
  arguments->todo_states =
    gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, NULL, NULL, true);
  arguments->priorities  =
    gl_list_nx_create_empty (GL_ARRAY_LIST, NULL, NULL, NULL, true);
  arguments->verbose = 0;
  arguments->tab_width = 8;
  arguments->use_tabs = false;
  arguments->rmargin = 77;

  debug_msg (MAIN, 5, "Return\n");
  return;
}

static error_t
parse_opt (int key, char *arg, struct argp_state *state)
{
  struct arguments *arguments = state->input;
  error_t retvalue = 0;
  debug_msg (MAIN, 3, "opt key=%c, arg=%s\n", key, arg);

  switch (key)
    {
    case ARGP_KEY_INIT:
      /* Initialize defaults */
      arguments_set_default (arguments);
      break;

    case ARGP_KEY_NO_ARGS:
      argp_usage (state);
      break;

    case 'v':
      arguments->verbose = true;
      break;

    case 't':
      gl_list_nx_add_last (arguments->todo_states, arg);
      break;

    case 'p':
      gl_list_nx_add_last (arguments->priorities, arg);
      break;

    case 'W':
      {
	int tab_width = atoi (arg);
	if (tab_width > 0)
	  {
	    arguments->tab_width = tab_width;
	  }
	else
	  {
	    argp_error (state, "Specified tab width must be a positive integer.\n");
	  }
      }
      break;

    case 'N':
      arguments->use_tabs = false;
      break;

    case 'T':
      arguments->use_tabs =  true;
      break;

    case 'm':
      {
	int rmargin = atoi (arg);
	if (rmargin > 0)
	  {
	    arguments->rmargin = rmargin;
	  }
	else
	  {
	    argp_error (state, "Specified right margin column must be a positive interger.\n");
	  }
      }
      break;

    case ARGP_KEY_ARG:
      if (state->arg_num < 5)
	{
	  arguments->paths[state->arg_num] = arg;
	}
      else
	{
	  argp_error (state, "Too many arguments.\n");
        }
      break;

    case ARGP_KEY_END:
      if (state->arg_num < 2)
        {
          argp_error (state, "Too few arguments.\n");
        }
      break;

    default:
      retvalue = ARGP_ERR_UNKNOWN;
    }
  return retvalue;
}
