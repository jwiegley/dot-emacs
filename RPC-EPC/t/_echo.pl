#!/usr/bin/perl

use RPC::EPC::Service;
use Data::Dumper;

sub echo_test {
    my $methods = {
        'echo' => sub {
          my $args = shift;
          return $args;
        }
    };
    my $server = RPC::EPC::Service->new(8888, $methods);
    $server->start;
}

echo_test();
