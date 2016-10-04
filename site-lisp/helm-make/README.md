### Description

A call to `helm-make` will give you a `helm` selection of this directory
Makefile's targets. Selecting a target will call `compile` on it.
You can cancel as usual with `C-g`.

### Install

Just get it from [MELPA](http://melpa.org/).

The functions that this package provides are auto-loaded, so no
additional setup is required. Unless you want to bind the functions to
a key.

### Additional stuff

#### `helm-make-do-save`

If this is set to `t`, the currently visited files from Makefile's
directory will be saved.

#### `helm-make-projectile`

This is a `helm-make` called with `(projectile-project-root)` as base directory.

#### `helm-make-list-target-method`

What method should be used to parse the Makefile. The default value is
`default`, which is a pure elisp solution, but falls a bit short when the
Makefile includes other Makefile's. The second option is `qp`, it is much more
accurate, as it uses the database produced by make to extract the
targets. But could be a bit slower when the database produced by make is large.

#### `helm-make-build-dir`

An additional directory, relative to `projectile-project-root`, where
`helm-make-projectile` will search for a valid Makefile. A valid Makefile is
one that GNU make looks after, i.e. the name of the Makefile must be one of
Makefile, makefile or GNUmakefile to be valid.

#### `helm-make-sort-targets`

If this is set to `t`, sort the targets before calling the completion method.
By default it is set to nil, if you are setting it to `t`, and you encounter
longer delays before the targets are displayed, try to set this back to nil.
This, however, might only be the case, if the Makefile contains thousand of
targets.

#### `helm-make-cache-targets`

If this is set to `t`, cache the targets. Next time when you call
`helm-make(-projectile)` for the same Makefile, and the modification time of
the Makefile has not changed meanwhile, reuse the cached targets.
It is set to `nil` by default.

#### `helm-make-executable`

You can customize executable of make command by changing this variable. Helpful
for implementing remote compiling.

#### `helm-make-named-buffer`

When setting helm-make-named-buffer to `t` all make buffers will be named based
on their make target. e.g. \*Helm-Make all\* for `make all`. This is useful if
you want to run multiple make targets at the same time.

#### `helm-make-comint`

When setting helm-make-comint to `t` helm-make will use Comint mode instead of
Compilation mode. This is useful if you want to interact with the make buffer.
