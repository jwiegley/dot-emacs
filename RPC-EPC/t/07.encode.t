use Test::More tests => 3;

use IPC::Open2;
use Encode;
use RPC::EPC::Service;
use Data::Dumper;

$pid = open2(*PROC_OUT, undef, $^X . " ./t/_echo.pl");
$port = <PROC_OUT>;

eval {
  $client = RPC::EPC::Service->new($port,{});
  $client->client_start;

  foreach my $text ('abcd', '日本語', 'efgh') {
    my $ret = $client->call_method('echo', [Encode.decode_utf8($text)])->recv;
    is($ret->[0], Encode.decode_utf8($text));
  }

};

kill 1, $pid;
