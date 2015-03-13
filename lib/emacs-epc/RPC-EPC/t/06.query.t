use Test::More tests => 1;

use IPC::Open2;
use RPC::EPC::Service;

$pid = open2(*PROC_OUT, undef, "perl ./t/_methods.pl");
$port = <PROC_OUT>;

eval {
  $client = RPC::EPC::Service->new($port,{});
  $client->client_start;

  $ret = $client->query_methods();
  is(to_sexp($ret->recv), to_sexp([['defined_method',"A","B"],
                                   ['method1','args',undef],
                                   ['test2','a b c','docstring here...'],
                                   ]));
};

kill 1, $pid;
