#!/usr/bin/perl

use RPC::EPC::Service;
use Data::Dumper;

sub errors_test {
    my $methods = {
        'num_error' => sub {
            1/0;
        },
        'die_error' => sub {
            die "die!";
        },
    };
    my $server = RPC::EPC::Service->new(8888, $methods);
    $server->start;
}

errors_test();
