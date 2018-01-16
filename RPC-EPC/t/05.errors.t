use Test::More tests => 6;

use IPC::Open2;
use RPC::EPC::Service;
use Data::Dumper;

$pid = open2(*PROC_OUT, undef, $^X . " ./t/_errors.pl");
$port = <PROC_OUT>;

eval {
  $client = RPC::EPC::Service->new($port,{});
  $client->client_start;

  eval {
    $ret = $client->call_method('num_error');
    $ret->recv;
  };
  # print STDERR Dumper $@;
  is('ERROR' => $@->[0]);
  like($@->[1],qr/Illegal division by zero/);

  eval {
    $ret = $client->call_method('die_error');
    $ret->recv;
  };
  # print STDERR Dumper $@;
  is('ERROR' => $@->[0]);
  like($@->[1],qr/die!/,);

  eval {
    $ret = $client->call_method('other_method');
    $ret->recv;
  };
  # print STDERR Dumper $@;
  is('EPC_ERROR' => $@->[0]);
  like($@->[1],qr/other_method/);
};

kill 1, $pid;
