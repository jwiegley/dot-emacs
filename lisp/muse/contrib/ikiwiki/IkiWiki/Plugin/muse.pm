#!/usr/bin/perl
# Ikiwiki plugin for Emacs Muse.
# Author: Michael Olson
# License: GPLv2 or later
#
# In your ikiwiki.setup file, set the muse_init option to the location
# of the init file for Muse.  Some examples provided in the
# examples/ikiwiki directory are muse-init-simple.el and
# muse-init-project.el.

package IkiWiki::Plugin::muse;

use warnings;
use strict;
use IkiWiki 3.00;

use Date::Format ();
use Encode ();
use File::Temp ();

sub import {
    hook(type => "getsetup", id => "muse", call => \&getsetup);
    hook(type => "scan", id => "muse", call => \&scan);
    hook(type => "filter", id => "muse", call => \&filter);
    hook(type => "htmlize", id => "muse", call => \&htmlize);
}

sub getsetup () {
    return (
        plugin => {
            safe => 1,
            rebuild => 1,         # format plugin
        },
        muse_emacs => {
            type => "string",
            example => "/usr/bin/emacs",
            description => "the location of Emacs",
            safe => 1,
            rebuild => 1,
        },
        muse_init => {
            type => "string",
            example => "~/ikiwiki/muse-init.el",
            description => "the location of your Muse init file",
            safe => 1,
            rebuild => 1,
        },
    );
}

# Handle Muse directives
sub scan (@) {
    my %params=@_;
    return unless pagetype($pagesources{$params{page}}) eq 'muse';
    my $canmeta = UNIVERSAL::can('IkiWiki::Plugin::meta', 'preprocess');
    my $cantag = UNIVERSAL::can('IkiWiki::Plugin::tag', 'preprocess_tag');
    return unless $canmeta || $cantag;
    my $fun;

    $_ = $params{content};
    pos = undef;
    while ( m/ \G \# ([a-zA-Z-]+) \s+ (.+?) \n+ /sgx ) {
        my ($key, $val) = ($1, $2);
        if ( $key =~ m/^(tags?|category)$/s ) {
            next unless $cantag;
            $fun = sub {
                IkiWiki::Plugin::tag::preprocess_tag(
                    (map { $_ => '' } (split /\s+/, $val)),
                    page     => $params{page},
                    destpage => $params{page},
                    preview  => 1,
                );
            };
        }
        else {
            next unless $canmeta;
            if ( $key eq 'date' ) {
                # Support pyblosxom-style dates (YYYY-MM-DD(-hh-mm)?)
                my $re = qr/ ^ ([0-9]{4}) - ([0-1][0-9]) - ([0-3][0-9])
                             (?: - ([0-2][0-9]) - ([0-5][0-9]) )? $ /sx;
                if ( $val =~ m/$re/ ) {
                    my @array = (0, $5 || 0, $4 || 0, $3, $2, $1 - 1900);
                    $val = Date::Format::strftime("%a, %e %b %Y %T", @array);
                }
            }
            $fun = sub {
                IkiWiki::Plugin::meta::preprocess(
                    $key, $val,
                    page     => $params{page},
                    destpage => $params{page},
                    preview  => 1,
                );
            };
        }
        if ( $params{muse_filter} ) {
            # Make "wantarray" work in the meta plugin
            my $ret = $fun->();
        }
        else {
            $fun->();
        }
    }
}

# Determine the emacs binary to use
sub locate_emacs {
    my $err = sub {
        die "Unable to find your emacs binary.\n",
          "  Set muse_emacs config to the right value.\n";
    };
    if ( $config{muse_emacs} ) {
        ( -x $config{muse_emacs} ) ? return $config{muse_emacs} : $err->();
    }
    else {
        my $emacs = `which emacs`;
        chomp $emacs;
        ( $emacs ) ? return $emacs : $err->();
    }
}

# Pass the content of the page to Muse for publishing
sub filter (@) {
    my %params=@_;
    return $params{content}
      unless pagetype($pagesources{$params{page}}) eq 'muse';

    # Force detection of the Muse #date directive
    scan(
        content     => $params{content},
        page        => $params{page},
        muse_filter => 1,
    );

    my $content = Encode::encode_utf8($params{content});
    my $qname = $params{page};
    $qname =~ s/"/\\"/g;

    my ($fh, $filename) = File::Temp::tempfile();
    print $fh $content;
    close $fh;
    my $qfile = $filename;
    $qfile =~ s/"/\\"/g;
    eval {
        system locate_emacs(),
          qw( -q --no-site-file -batch -l ), $config{muse_init},
          '--eval', qq{(muse-ikiwiki-publish-file "$qfile" "$qname")};
        {
            open my $ifh, '<', $filename;
            local $/; $content = <$ifh>;
            close $ifh;
        }
        unlink $filename;
    };
    if ($@) {
        my $ret = $@;
        unlink $filename;
        die $ret;
    }
    return Encode::decode_utf8($content);
}

# Fake handler to make publishing work
sub htmlize (@) {
    my %params=@_;
    return $params{content};
}

1
