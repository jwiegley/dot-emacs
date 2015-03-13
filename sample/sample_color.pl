#!/usr/bin/env perl
use strict;
use warnings;

use Term::ANSIColor qw(:constants);

print RED BOLD "This is RED and BOLD\n", RESET;
print GREEN UNDERSCORE "This is GREEN and UNDERSCORE\n", RESET;
print BOLD ON_BLUE "This is BACKGROUD COLOR\n", RESET;
