Future work
============

Clean up state dir
--------------------

Currently the list of trusted expressions grows indefinitely, and we
keep gc roots to the latest build for every file we ever
`nix-buffer` into. This can be manually cleaned up by nuking the state
dir and clearing `nix-buffer--trusted-exprs`, but this should be
handled more automatically.

Handle remote files
--------------------

Right now `nix-buffer` will almost certainly fail for remote
files, unless `f.el` and `call-process` somehow conspire to do the
right thing here.
