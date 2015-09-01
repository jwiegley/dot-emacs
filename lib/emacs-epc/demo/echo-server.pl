#!/usr/bin/perl

use RPC::EPC::Service;

sub echo_test {
    my $methods = {
        'echo' => [sub {
            my $args = shift;
            return $args;
        },"args","just echo back arguments."],
        'add' => sub {
            my $args_ref = shift;
            my ($a,$b) = @$args_ref;
            return $a + $b;
        }
    };
    my $server = RPC::EPC::Service->new(0, $methods);
    $server->start;
}

echo_test();

