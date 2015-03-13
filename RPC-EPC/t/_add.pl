#!/usr/bin/perl

use RPC::EPC::Service;
use Data::Dumper;

sub add_test {
    my $methods = {
        'add' => sub {
            my $args_ref = shift;
            my ($a,$b) = @$args_ref;
            return $a + $b;
        }
    };
    my $server = RPC::EPC::Service->new(8888, $methods);
    $server->start;
}

add_test();
