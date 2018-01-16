use Test::More tests => 3;

use IPC::Open2;
use RPC::EPC::Service;

$pid = open2(*PROC_OUT, undef, $^X . " ./t/_add.pl");
$port = <PROC_OUT>;

eval {
  $client = RPC::EPC::Service->new($port,{});
  $client->client_start;

  $ret = $client->call_method('add', [1,2]);
  is($ret->recv, 3);

  $ret = $client->call_method('add', [123,-122]);
  is($ret->recv, 1);

  # ignore additional arguments
  $ret = $client->call_method('add', [123,-122], 123);
  is($ret->recv, 1);
};

kill 1, $pid;
