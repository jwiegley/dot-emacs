use Test::More tests => 18;

use RPC::EPC::Service;

##################################################
# Service

$h2 = {};
$ss = RPC::EPC::Service->new(9876,$h2);
is($ss->{port},9876);
is($ss->{count},0);
ok($ss->{methods} => $h2);
ok($ss->{sessions} => {});
ok(ref $ss->{wait}, 'AnyEvent::CondVar');

##################################################
# to_sexp interface

is(to_sexp("abcd"),"\"abcd\"");
is(to_sexp("ab'cd"),"\"ab'cd\"");
is(to_sexp("a\nbcd"),"\"a\nbcd\"");
is(to_sexp(undef),"nil");
is(to_sexp(123), "123");

# array
my @a = (2,4,6);
is(to_sexp(\@a), "(2 4 6)");

is(to_sexp([1,2,3]), "(1 2 3)");
is(to_sexp([1,"2",3]), "(1 \"2\" 3)");

# hash
my %a = ('a'=>'b','c'=>'d');
is(to_sexp(\%a), "((\"c\" . \"d\") (\"a\" . \"b\"))");

is(to_sexp({'a'=>'b','c'=>'d'}), "((\"c\" . \"d\") (\"a\" . \"b\"))");
is(to_sexp({'a'=>1,'b'=>2}), "((\"a\" . 1) (\"b\" . 2))");

# complex
is(to_sexp([1,[2,3.3,45],10]), "(1 (2 3.3 45) 10)");
is(to_sexp({'a'=>[1,2,3],
            'c'=>{name => 'OK'}}),
   "((\"c\" . ((\"name\" . \"OK\"))) (\"a\" . (1 2 3)))");

