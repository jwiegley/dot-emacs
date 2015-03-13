#!/usr/bin/perl -w --

#
# $Id: getstamps.pl,v 1.3 2007-08-19 13:46:54 welle Exp $
#

# Author: Michael Welle

# This file is available under the terms of the GNU General Public
# License, Version 2.

# Modified by Michael Olson to add Author note. license text, and to
# fix a use of "muse" rather than $muse_file_extension.

#my $tsfile = "/tmp/blog/timestamps";
my $tsfile = "-";
my $muse_file_extension = "muse";

#
#
#
sub process_file {
  my ($file) = @_;


  open( F, "<$file" );

  while ( <F> ) {

    if ( /^#date\s+(.+)$/ ) {

      close ( F );
      my $d = $1;

      $file =~ s/\.${muse_file_extension}$/\.txt/;
      $file =~ s/^\.\///;

      if ( $d =~ /(\d\d\d\d)-(\d\d)-(\d\d)-(\d\d)-(\d\d)/ ) {

	printf TS "${file}=>$2/$3/$1 $4:$5\n";
	return;

      } # if

    } # if

  } # while

  close( F );

} # process_file



#
#
#
sub traverse_directory {
  my ($directory) = @_;
  local *DIR;
  my @files = ();
  my $pfad = "";


  opendir( DIR, $directory );
  @files = readdir( DIR );
  closedir( DIR );


  foreach my $file ( @files ) {

    next if ( !( $file =~ /^.*\.${muse_file_extension}$/ )
	      || ($file eq '.') || ($file eq '..'));


    $path = "$directory/$file";

    if( -d $path ) {

       traverse_directory( $path );

    } else {

      process_file( $path );

    } #if

  } #foreach

} # traverse_directory


#
# Here we go...
#

open( TS, ">${tsfile}" );

if ( @ARGV == 0 ) {

  traverse_directory( "." );

} else {

  traverse_directory( $ARGV[0] );

} #if

close( TS );

exit 0;
