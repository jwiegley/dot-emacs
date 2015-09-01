# Monky An Emacs mode for Hg

Monky provides an interactive interface for Hg.

## Installation

````cl
(add-to-list 'load-path "path/to/monky/dir")
(require 'monky)

;; By default monky spawns a seperate hg process for every command.
;; This will be slow if the repo contains lot of changes.
;; if `monky-process-type' is set to cmdserver then monky will spawn a single
;; cmdserver and communicate over pipe.
;; Available only on mercurial versions 1.9 or higher

(setq monky-process-type 'cmdserver)

````

## Usage

open any file in a hg repo and run `M-x monky-status` to see the
current status. Look at the [documentation][monky-documentation] for further details.

## Thanks

Heavily borrowed from [Magit][magit]. Thanks to Marius Vollmer.

[magit]: http://github.com/magit/magit
[monky-documentation]: http://ananthakumaran.github.com/monky/index.html

## Contributors
[ananthakumaran](https://github.com/ananthakumaran) (Anantha Kumaran)

[lyro](https://github.com/lyro) (Frank Fischer)

[tkf](https://github.com/tkf) (Takafumi Arakaki)

