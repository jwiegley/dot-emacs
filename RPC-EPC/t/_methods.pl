#!/usr/bin/perl

use RPC::EPC::Service;
use Data::Dumper;

sub methods_test {
    my $methods = {
        'method1' => {'sub' => sub {
          return 1;
        }, 'arg_spec' => "args"},
        'test2' => [sub {
          return 2;
        }, 'a b c','docstring here...']
    };
    my $server = RPC::EPC::Service->new(8888, $methods);
    $server->define_method("defined_method", sub {}, "A","B");
    $server->start;
}

methods_test();
