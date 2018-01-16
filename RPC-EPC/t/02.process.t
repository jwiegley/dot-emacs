use Test::More tests => 1;

use IPC::Open2;
use RPC::EPC::Service;

# start server

$pid = open2(*PROC_OUT, undef, $^X . " ./t/_process.pl");
$val = <PROC_OUT>;

is("8888\n", $val);

close PROC_OUT;
kill 1, $pid;
sleep 0.5;

