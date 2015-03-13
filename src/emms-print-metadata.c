/* emms-print-metadata.c --- Info function for libtag
   Copyright (C) 2005, 2006, 2007, 2008, 2009  Free Software Foundation, Inc.

Author: Trent Buck <trentbuck@gmail.com>

This file is part of EMMS.

EMMS is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

EMMS is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with EMMS; see the file COPYING.  If not, write to
the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
Boston, MA 02110-1301, USA.  */

#include <stdlib.h>
#include <stdio.h>
#include <tag_c.h>

int
main (int argc, char **argv)
{
  TagLib_File *file;
  TagLib_Tag *tag;

  if (argc != 2)
    {
      fprintf (stderr, "usage: emms-print-metadata file.{mp3,ogg,flac}\n");
      exit (1);
    }

  file = taglib_file_new (argv[1]);

  if (!file)
    {
      fprintf (stderr, "%s: File does not exist or is of an unknown type\n", argv[1]);
      exit (1);
    }

  tag = taglib_file_tag (file);

  /* Apparently, if the file is named foo.mp3 or similar, the library
     still can open it, for whatever reason.
  */
  if (!tag)
    {
      fprintf (stderr, "%s: File does not exist or is of an unknown type\n", argv[1]);
      exit (1);
    }

  printf ("info-artist=%s\n", taglib_tag_artist (tag));
  printf ("info-title=%s\n", taglib_tag_title (tag));
  printf ("info-album=%s\n", taglib_tag_album (tag));
  printf ("info-tracknumber=%d\n", taglib_tag_track (tag));
  printf ("info-year=%d\n", taglib_tag_year (tag));
  printf ("info-genre=%s\n", taglib_tag_genre (tag));
  printf ("info-note=%s\n", taglib_tag_comment (tag));
  printf ("info-playing-time=%d\n", taglib_audioproperties_length (taglib_file_audioproperties (file)));

  taglib_tag_free_strings ();
  taglib_file_free (file);

  return 0;
}

/* emms-print-metadata.c ends here. */
