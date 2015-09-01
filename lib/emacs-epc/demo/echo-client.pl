use RPC::EPC::Service;

$client = RPC::EPC::Service->new(8888,{});
$client->client_start;

$ret = $client->call_method('echo', 'hello epc!');

print $ret->recv . "\n";

$client->stop;

