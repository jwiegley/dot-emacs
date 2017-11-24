use Test::More tests => 8;

use IPC::Open2;
use RPC::EPC::Service;

$pid = open2(*PROC_OUT, undef, $^X . " ./t/_echo.pl");
$port = <PROC_OUT>;

eval {
  $client = RPC::EPC::Service->new($port,{});
  $client->client_start;

  $ret = $client->call_method('echo', "hello epc!");
  is($ret->recv, 'hello epc!');

  $ret = $client->call_method('echo', 123);
  is($ret->recv, 123);

  $ret = $client->call_method('echo', undef);
  is($ret->recv, undef);

  $ret = $client->call_method('echo', [1,2,3]);
  is(to_sexp($ret->recv), to_sexp(['1','2','3']));

  $ret = $client->call_method('echo', {a=>'b'});
  is(to_sexp($ret->recv), to_sexp({a=>'b'}));

  $ret = $client->call_method('echo', [10,20,[1,2,3]]);
  is(to_sexp($ret->recv), to_sexp(['10','20',['1','2','3']]));

  $ret = $client->call_method('echo', {a=>[1,2,3]});
  is(to_sexp($ret->recv), to_sexp([['a','1','2','3']]));

  $ret = $client->call_method('echo', "abcd\nefgh\nOK");
  is($ret->recv, "abcd\nefgh\nOK");

};

kill 1, $pid;
