/* emms-print-metadata.cpp --- Info function for TagLib
   Copyright (C) 2016  Free Software Foundation, Inc.

   Author: Petteri Hintsanen <petterih@iki.fi>

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

#include <taglib/fileref.h>
#include <taglib/tag.h>
#include <taglib/tpropertymap.h>
#include <iostream>

static const char* const tags_to_extract[] = {
  "album",
  "albumsort",
  "albumartist",
  "albumartistsort",
  "artist",
  "artistsort",
  "composer",
  "composersort",
  "performer",
  "year",
  "originalyear",
  "date",
  "originaldate",
  "genre",
  "label",
  "title",
  "titlesort",
  "tracknumber",
  "discnumber"
};

void print_tag (const TagLib::PropertyMap& tags, const std::string& tag);

int
main (int argc, char* argv[])
{
  if (argc != 2)
    {
      std::cerr << argv[0] << ": "
		<< "usage: emms-print-metadata FILENAME"
		<< std::endl
		<< "FILENAME must end to one of these extensions: "
		<< TagLib::FileRef::defaultFileExtensions ().toString ()
		<< std::endl;
      return 1;
    }

  TagLib::FileRef file (argv[1]);
  if (file.isNull ()) {
    std::cerr << argv[0] << ": "
	      << argv[1] << ": "
	      << "file does not exist or is of an unknown type"
	      << std::endl;
    return 1;
  }

  const TagLib::PropertyMap tags = file.file ()->properties ();
  if (tags.isEmpty ()) {
    std::cerr << argv[0] << ": "
	      << argv[1] << ": "
	      << "file does not have tags or is of an unknown type"
	      << std::endl;
    return 1;
  }

  for (unsigned int i = 0; i < sizeof (tags_to_extract) / sizeof (char*);
       i++)
    {
      print_tag (tags, tags_to_extract[i]);
    }

  int length = 0;
  if (file.audioProperties ())
    {
      const TagLib::AudioProperties* properties = file.audioProperties ();
      length = properties->length ();
    }
  std::cout << "info-playing-time=" << length << std::endl;

  return 0;
}

void
print_tag (const TagLib::PropertyMap& tags, const std::string& tag)
{
  TagLib::StringList values = tags[tag];
  if (!values.isEmpty ())
    {
      const TagLib::String& value = values.front ();
      std::cout << "info-" << tag << "=" << value.to8Bit (true) << std::endl;
    }
}

/* emms-print-taglib-metadata.cpp ends here. */
