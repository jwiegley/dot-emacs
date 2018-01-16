use strict;
use warnings;
use Module::Build;

my $builder = Module::Build->new(
    module_name         => 'RPC::EPC::Service',
    license             => 'perl',
    dist_author         => 'Masashi Sakurai <m.sakurai@kiwanami.net>',
    dist_version_from   => 'lib/RPC/EPC/Service.pm',
    requires => {
        'AnyEvent' => 6.1,
        'Data::SExpression' => 0.41,
        'Test::More' => 0,
        'version'    => 0,
    },
    add_to_cleanup      => [ 'RPC-EPC-*' ],
);

$builder->create_build_script();
