#!/usr/bin/perl
#  emms-print-metadata.pl --- Info function for libtag
#    Copyright (C) 2012  Free Software Foundation, Inc.

# Author: Lucas Bonnet <lbonnet@rincevent.net>

# This file is part of EMMS.

# EMMS is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 3, or (at your option)
# any later version.

# EMMS is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with EMMS; see the file COPYING.  If not, write to
# the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
# Boston, MA 02110-1301, USA.

use strict;
use warnings;

use Audio::Scan;
use File::Basename;

# enable UTF-8 output
binmode(STDOUT, ":utf8");

my $file = $ARGV[0];

# Scan without reading (possibly large) artwork into memory.
# Instead of binary artwork data, the size of the artwork will be returned instead.
local $ENV{AUDIO_SCAN_NO_ARTWORK} = 1;
my $data = Audio::Scan->scan($file);

# determines the names of tags according to file type
my %ext_map = ("mp3" =>
         {'artist'    => 'TPE1',
          'title'     => 'TIT2',
          'album'     => 'TALB',
          'tracknumber' => 'TRCK',
          'composer'  => 'TCOM',
          'performer' => 'TPE2',
          'year'      => 'TDRC',
          'genre'     => 'TCON',
          'comment'   => 'COMM'},
         "flc" =>
         {'artist'    => 'ARTIST',
          'title'     => 'TITLE',
          'album'     => 'ALBUM',
          'tracknumber' => 'TRACKNUMBER',
          'composer'  => 'COMPOSER',
          'performer' => 'PERFORMER',
          'year'      => 'DATE',
          'genre'     => 'GENRE',
          'comment'   => 'COMMENT'},
         "ogg" =>
         {'artist'    => 'ARTIST',
          'title'     => 'TITLE',
          'album'     => 'ALBUM',
          'tracknumber' => 'TRACKNUMBER',
          'composer'  => 'COMPOSER',
          'performer' => 'PERFORMER',
          'year'      => 'DATE',
          'genre'     => 'GENRE',
          'comment'   => 'COMMENT'},
        );

# find out extension
my ($filename, $directories, $extension) = fileparse($file, qr/[^.]*/);
my $type = Audio::Scan->type_for(lc($extension));
my $tag_map = $ext_map{$type};

# print tag info
print "info-artist=";      safe_print('artist');
print "info-title=";       safe_print('title');
print "info-album=";       safe_print('album');
print "info-tracknumber="; safe_print('tracknumber');
print "info-composer=";    safe_print('composer');
print "info-performer=";   safe_print('performer');
print "info-year=";        safe_print('year');
print "info-genre=";       safe_print('genre');
print "info-note=" ;       safe_print('comment');

print "info-playing-time=",int($data->{'info'}->{'song_length_ms'} / 1000),"\n";

sub safe_print {
  my $k = shift;

  if (defined $data->{'tags'}->{ $tag_map->{$k} }) {
    print $data->{'tags'}->{ $tag_map->{$k} };
  } else {
    print "<no $k>";
  }
  print "\n";
}
