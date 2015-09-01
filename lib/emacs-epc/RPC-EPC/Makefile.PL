use lib qw(lib);
use Module::Build::Compat;

Module::Build::Compat->run_build_pl(args => \@ARGV);
Module::Build::Compat->write_makefile(build_class => 'Module::Build');
