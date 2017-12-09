# benchstat.el

[![MELPA](https://melpa.org/packages/benchstat-badge.svg)](https://melpa.org/#/benchstat)

[benchstat](https://godoc.org/golang.org/x/perf/cmd/benchstat) integration that enhances
builtin `benchmark` package with ability to analyze benchmarking results.

## Overview

When you do a performance analysis, or simple benchmarking,
you almost always **compare** two or more functionally equivallent versions of the code.
One of them is expected to be **faster** and/or produce less **allocations**.

Emacs provides useful [benchmarking](https://www.emacswiki.org/emacs/EmacsLispBenchmark) macros
that can be used to get basic profile: execution time and the number of GC runs for it's evaluation.

This package makes proper benchmark results analysis far easier by leveraging [benchstat](https://godoc.org/golang.org/x/perf/cmd/benchstat) utility. 

## Installation

### Installation: Emacs package

To install from [MELPA](https://github.com/melpa/melpa): `M-x package-install benchstat`.  
If this is not working, check your `package-archives` list.  

See [manual installation instruction](docs/manual-installation.md) if you do not
want to use package manager.

### Installation: benchstat program

Two options:

1. Download precompiled binary (only for **amd64/linux**).
2. Compile binary yourself (requires `go` installed).

Precompiled binary for **amd64/linux** is distributed with every [major release](https://github.com/Quasilyte/benchstat.el/releases/tag/v1.0.0).

Snippet below shows how to install `benchstat` for any platform.

```bash
mkdir build_benchstat 
cd build_benchstat
GOPATH=`pwd` go get golang.org/x/perf/cmd/benchstat
# ./bin/benchstat is the binary you need
```

Emacs will try to invoke `benchstat` utility by command which is
specified by `benchstat-program` variable (default value: `benchstat`).  
If you do not have `benchstat` under your PATH, 
you can set `benchstat-program` to absolute path.

### Installation: test

1. `(require 'benchstat)` should be evaluated without errors.
2. `(shell-command "benchstat")` should result into usage message.

## Quick start

**Case**: your library used `(list x y)` in the places where 2 return values were needed.  
You wounder, how performance may change with transition to `(cons x y)`.

We call `(list x y)` code **old**.  
We call `(cons x y)` code **new**.  
`:old` and `:new` are **profile keys** that specify profile data file to be used.

```elisp
(require 'benchstat)

;; Decide how much repetitions is needed.
;; This is the same as `benchmark-run-compiled` REPETITIONS argument.
(defconst repetitions 1000000)

;; Collect old code profile.
(benchstat-run :old repetitions (list 1 2))
;; Collect new code profile.
(benchstat-run :new repetitions (cons 1 2))

;; Display the results.
;; Can be run interactively by `M-x benchstat-compare'.
(benchstat-compare)
```

Evaluation of `benchstat-compare` form creates a temporary buffer which will contain
something like this:

```
name   old time/op    new time/op    delta
Emacs    44.2ms ± 6%    25.0ms ±15%  -43.38%  (p=0.000 n=10+10)

name   old allocs/op  new allocs/op  delta
Emacs      23.0 ± 0%      11.4 ± 5%  -50.43%  (p=0.000 n=10+10)
```

This shows use that:

* `cons` (new) version is almost 2 times faster.
* `cons` (new) version does 2 times less allocations.

> Tip: if you have hard times interpreting the output,
> read [benchstat documentation](https://github.com/golang/perf/tree/master/cmd/benchstat).

`benchstat-run` executes form 10 times by default.
this can be re-defined with `benchstat-run-count` variable:

```elisp
;; Use 5 runs instead of 10.
(let ((benchstat-run-count 5))
  (benchstat-run :new repetitions (cons 1 2)))

;; Additional runs can be performed by `benchstat-run-more',
;; which appends to profile data file.
(benchstat-run-more :new repetitions (cons 1 2)) ;; Additional 10 runs

;; Profile can be reset on demand.
(benchstat-reset :new) ;; `:new' file had 15 runs info
```

It is possible to define additional **profiles** to make comparison of multiple
implementations easier.  

```elisp
(benchstat-push-profile :vector
                        "/tmp/benchstat-vector")

(benchstat-run :vector repetitions (vector 1 2))

(benchstat-compare :old :vector)
```

When `benchstat-compare` is called with arguments different from default {`:old`, `:new`},  
single-line header is prepended to the output.

```
/* old=(:old "/tmp/benchstat-old") new=(:vector "/tmp/benchstat-vector") */

name   old time/op    new time/op    delta
Emacs    44.2ms ± 6%    54.7ms ± 9%  +23.91%  (p=0.000 n=10+10)

name   old allocs/op  new allocs/op  delta
Emacs      23.0 ± 0%      17.0 ± 0%  -26.09%  (p=0.000 n=9+8)
```

## More documentation

* [troubleshooting.md](docs/troubleshooting.md) outlines some problems that you may encounter,
  along with their possible solutions.
