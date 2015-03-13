use strict;
use warnings;
use Test::More;

my $var = "quickrun";
is "quickrun", $var, "setting string 'quickrun'";

like $var, qr/quick/, "var looks like 'quick'";

ok undef, 'error test';

done_testing;

__END__

(progn
   (add-to-list 'quickrun-file-alist '("\\.t$" . "prove"))
   (quickrun-add-command "prove" '((:command . "prove") (:exec . "%c -v %s"))))
