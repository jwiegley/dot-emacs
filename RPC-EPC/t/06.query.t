use Test::More tests => 3;

use IPC::Open2;
use RPC::EPC::Service;

$pid = open2(*PROC_OUT, undef, $^X . " ./t/_methods.pl");
$port = <PROC_OUT>;

eval {
  $client = RPC::EPC::Service->new($port,{});
  $client->client_start;

  $ret = $client->query_methods();
  my $got = to_sexp($ret->recv);
  like $got, qr/\Q("defined_method" "A" "B")\E/;
  like $got, qr/\Q("method1" "args" nil)\E/;
  like $got, qr/\Q("test2" "a b c" "docstring here...")\E/;
};

kill 1, $pid;
