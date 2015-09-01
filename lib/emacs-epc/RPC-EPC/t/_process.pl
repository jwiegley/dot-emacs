use RPC::EPC::Service;

my $s=RPC::EPC::Service->new(8888,{});
$s->{wait}->send;
$s->start;
sleep 1;
