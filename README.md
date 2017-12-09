**eval-in-repl: Consistent ESS-like eval interface for various REPLs**
--------------------

This package does what ESS does for R for various REPLs.

Emacs Speaks Statistics (ESS) package has a nice function called ess-eval-region-or-line-and-step, which is assigned to C-RET. This function sends a line or a selected region to the corresponding shell (R, Julia, Stata, etc) visibly. It also start up a shell if there is none.

This package implements similar work flow for various read-eval-print-loops (REPLs) shown below.

The languages currently supported are: **Emacs Lisp**, **Clojure**, **Common
Lisp**, **Racket**, **Scheme**, **Hy**, **Python**, **Ruby**, **Standard ML**,
**OCaml**, **Prolog**, **Javascript**, **shell script**, **Elixr**, **Erlang**,
**Elm** and **Scala**. **Prolog** and **Javascript** support was contributed by other authors (see special thanks).


**Usage: C-RET rules all**
--------------------

After installation and appropriate configuration (see below), you can use C-RET in a source file to start up an appropriate REPL (except cider, which needs manual M-x ```cider-jack-in```) and evaluate a line, selected region or the current expression depending on the context. The script will be shown in one window, and the REPL in another. The REPL shows both the code executed and the value the code evaluated to. The cursor steps to the next expression in the source file (only when invoked without a selected region). A more detailed explanation is available at Qiita (http://qiita.com/kaz-yos/items/bb8016ec79cfbbf328df ).

**Emacs Lisp via IELM (screencast)**

You can see C-RET in action.

![ielm](screencast_ielm.gif?raw=true "ielm example")

YouTube video: https://www.youtube.com/watch?v=gNBlF67e-0w&feature=youtu.be

**Clojure via cider.el**

![cider](screen_shot_cider.png?raw=true "cider example")

**Python via python.el**

![python](screen_shot_python.png?raw=true "python example")

**Shell script**

![shell](screen_shot_shell.png?raw=true "shell example")


**Installation**
--------------------

eval-in-repl.el is available on the MELPA repository. You can do the following, then choose and install eval-in-repl.

```
M-x list-packages
```

To configure the MELPA, see this: http://melpa.milkbox.net/#/getting-started


The following files are included in the package. There are respective dependencies for each language-specific file that are NOT automatically installed.

- eval-in-repl.el
 - Skeleton package required by all specialized packages below.

- eval-in-repl-ielm.el (depends on IELM; part of default emacs installation)
 - Support for Inferior Emacs Lisp Mode

- eval-in-repl-cider.el (depends on cider.el)
 - Support for Clojure via cider.el

- eval-in-repl-slime.el (depends on slime.el)
 - Support for Common Lisp via slime.el

- eval-in-repl-geiser.el (depends on geiser.el)
 - Support for Racket and Guile Scheme via geiser.el

- eval-in-repl-racket.el (depends on racket-mode.el)
 - Support for Racket via racket-mode.el (incompatible with geiser version)

- eval-in-repl-scheme.el
 - Support for Scheme via scheme.el (depends on scheme.el and cmuscheme.el; both part of default emacs installation) (incompatible with geiser version)

- eval-in-repl-hy.el (depends on hy-mode.el)
 - Support for Hy via hy-mode.el


- eval-in-repl-python.el
 - Support for Python via python.el (depends on python.el; part of default emacs installation)

- eval-in-repl-ruby.el (depends on ruby-mode.el, and inf-ruby.el)
 - Support for Ruby via ruby-mode.el

- eval-in-repl-sml.el (depends on sml-mode.el)
 - Support for Standard ML via sml-mode.el

- eval-in-repl-ocaml.el (depends on tuareg.el)
 - Support for OCaml via tuareg.el

- eval-in-repl-prolog.el (depends on prolog.el; part of default emacs installation)
 - Support for Prolog via prolog.el

- eval-in-repl-javascript.el (depends on js3-mode.el, js2-mode.el, and js-comint.el)
 - Support for Javascript via js-comint.el

- eval-in-repl-shell.el
 - Support for shell

- eval-in-repl-iex.el (depends on elixir-mode.el, and alchemist.el)
 - Support for Elixir via alchemist.el

- eval-in-repl-erlang.el (depends on erlang.el)
 - Support for Erlang via erlang.el

- eval-in-repl-elm.el (depends on elm-mode.el)
 - Support for Elm via elm-mode.el

- eval-in-repl-scala.el (depends on scala-mode.el, and ensime.el)
 - Support for Scala via ensime.el

**Configuration**
--------------------

The full configuration is the following. ```eval-in-repl.el``` is always necessary. Require other files as needed and configure the respective mode-specific key bindings.

The REPL startup behavior has change in version 0.9.0. Previously, a specific window configuration (REPL on left, script on right, nothing else) was strictly enforced. The newer versions try to be less invasive. If only one window exists, necessarily window splitting occurs. The splitting behavior can be controlled by the ```eir-repl-placement``` option (either one of quoted symbols 'left, 'right, 'above, or 'below). When there are multiple windows present, you can choose which window to replace via ```ace-window``` for some languages (currently, IELM, Python, Hy, and shell only). For others, window splitting and replacement are controlled by the respective major/minor mode packages, and may be erratic.

The ```eir-always-split-script-window``` option introduced in version 0.9.1, when true, splits the current script window at REPL start up, but does not replace any other windows. This may be useful if you do not like to replace one of the windows that are already open, and create a new window for the REPL.

To recover the old behavior of the two-window layout, both ```eir-delete-other-windows``` and ```eir-always-split-script-window``` should be set to ```t```.

```lisp
;; require the main file containing common functions
(require 'eval-in-repl)

;; Uncomment if no need to jump after evaluating current line
;; (setq eir-jump-after-eval nil)

;; Uncomment if you want to always split the script window into two.
;; This will just split the current script window into two without
;; disturbing other windows.
;; (setq eir-always-split-script-window t)

;; Uncomment if you always prefer the two-window layout.
;; (setq eir-delete-other-windows t)

;; Place REPL on the left of the script window when splitting.
(setq eir-repl-placement 'left)


;;; ielm support (for emacs lisp)
(require 'eval-in-repl-ielm)
;; Evaluate expression in the current buffer.
(setq eir-ielm-eval-in-current-buffer t)
;; for .el files
(define-key emacs-lisp-mode-map (kbd "<C-return>") 'eir-eval-in-ielm)
;; for *scratch*
(define-key lisp-interaction-mode-map (kbd "<C-return>") 'eir-eval-in-ielm)
;; for M-x info
(define-key Info-mode-map (kbd "<C-return>") 'eir-eval-in-ielm)

;;; cider support (for Clojure)
;; (require 'cider) ; if not done elsewhere
(require 'eval-in-repl-cider)
(define-key clojure-mode-map (kbd "<C-return>") 'eir-eval-in-cider)

;;; SLIME support (for Common Lisp)
;; (require 'slime) ; if not done elsewhere
(require 'eval-in-repl-slime)
(add-hook 'lisp-mode-hook
		  '(lambda ()
		     (local-set-key (kbd "<C-return>") 'eir-eval-in-slime)))

;;; Geiser support (for Racket and Guile Scheme)
;; When using this, turn off racket-mode and scheme supports
;; (require 'geiser) ; if not done elsewhere
(require 'eval-in-repl-geiser)
(add-hook 'geiser-mode-hook
		  '(lambda ()
		     (local-set-key (kbd "<C-return>") 'eir-eval-in-geiser)))

;;; racket-mode support (for Racket; if not using Geiser)
;; (require 'racket-mode) ; if not done elsewhere
;; (require 'eval-in-repl-racket)
;; (define-key racket-mode-map (kbd "<C-return>") 'eir-eval-in-racket)

;;; Scheme support (if not using Geiser))
;; (require 'scheme)    ; if not done elsewhere
;; (require 'cmuscheme) ; if not done elsewhere
;; (require 'eval-in-repl-scheme)
;; (add-hook 'scheme-mode-hook
;; 	  '(lambda ()
;; 	     (local-set-key (kbd "<C-return>") 'eir-eval-in-scheme)))

;;; Hy support
;; (require 'hy-mode) ; if not done elsewhere
(require 'eval-in-repl-hy)
(define-key hy-mode-map (kbd "<C-return>") 'eir-eval-in-hy)


;;; Python support
;; (require 'python) ; if not done elsewhere
(require 'eval-in-repl-python)
(add-hook 'python-mode-hook
          '(lambda ()
             (local-set-key (kbd "<C-return>") 'eir-eval-in-python)))

;;; Ruby support
;; (require 'ruby-mode) ; if not done elsewhere
;; (require 'inf-ruby)  ; if not done elsewhere
(require 'eval-in-repl-ruby)
(define-key ruby-mode-map (kbd "<C-return>") 'eir-eval-in-ruby)

;;; SML support
;; (require 'sml-mode) ; if not done elsewhere
(require 'eval-in-repl-sml)
(define-key sml-mode-map (kbd "<C-return>") 'eir-eval-in-sml)
(define-key sml-mode-map (kbd "C-;") 'eir-send-to-sml-semicolon)

;;; OCaml support
;; (require 'tuareg) ; if not done elsewhere
(require 'eval-in-repl-ocaml)
(define-key tuareg-mode-map (kbd "<C-return>") 'eir-eval-in-ocaml)
;; function to send a semicolon to OCaml REPL
(define-key tuareg-mode-map (kbd "C-;") 'eir-send-to-ocaml-semicolon)

;;; Prolog support (Contributed by m00nlight)
;; if not done elsewhere
;; (autoload 'run-prolog "prolog" "Start a Prolog sub-process." t)
;; (autoload 'prolog-mode "prolog" "Major mode for editing Prolog programs." t)
;; (autoload 'mercury-mode "prolog" "Major mode for editing Mercury programs." t)
;; (setq prolog-system 'swi)
;; (setq auto-mode-alist (append '(("\\.pl$" . prolog-mode)
;;                                 ("\\.m$" . mercury-mode))
;;                                auto-mode-alist))
(require 'eval-in-repl-prolog)
(add-hook 'prolog-mode-hook
          '(lambda ()
             (local-set-key (kbd "<C-return>") 'eir-eval-in-prolog)))

;;; Javascript support
;; (require 'js3-mode)  ; if not done elsewhere
;; (require 'js2-mode)  ; if not done elsewhere
;; (require 'js-comint) ; if not done elsewhere
(with-eval-after-load 'js3-mode
  (require 'eval-in-repl-javascript)
  (define-key js3-mode-map (kbd "<C-return>") 'eir-eval-in-javascript))
(with-eval-after-load 'js2-mode
  (require 'eval-in-repl-javascript)
  (define-key js2-mode-map (kbd "<C-return>") 'eir-eval-in-javascript))


;; Shell support
(require 'eval-in-repl-shell)
(add-hook 'sh-mode-hook
          '(lambda()
             (local-set-key (kbd "C-<return>") 'eir-eval-in-shell)))
;; Version with opposite behavior to eir-jump-after-eval configuration
(defun eir-eval-in-shell2 ()
  "eval-in-repl for shell script (opposite behavior)

This version has the opposite behavior to the eir-jump-after-eval
configuration when invoked to evaluate a line."
  (interactive)
  (let ((eir-jump-after-eval (not eir-jump-after-eval)))
       (eir-eval-in-shell)))
(add-hook 'sh-mode-hook
          '(lambda()
             (local-set-key (kbd "C-M-<return>") 'eir-eval-in-shell2)))

;;; Elixir support
;; (require 'elixir-mode) ; if not done elsewhere
;; (require 'alchemist)   ; if not done elsewhere
(require 'eval-in-repl-ruby)
(define-key elixir-mode-map (kbd "<C-return>") 'eir-eval-in-iex)

;;; Erlang support
;; (require 'erlang-mode) ; if not done elsewhere
(require 'eval-in-repl-erlang)
(define-key erlang-mode-map (kbd "<C-return>") 'eir-eval-in-erlang)

;;; Elm support
;; (require 'elm-mode) ; if not done elsewhere
(require 'eval-in-repl-elm)
(define-key elm-mode-map (kbd "<C-return>") 'eir-eval-in-elm)

;;; Scala support
;; (require 'ensime) ; if not done elsewhere
(require 'eval-in-repl-scala)
(define-key scala-mode-map (kbd "<C-return>") 'eir-eval-in-scala)
```

**Known issues**
--------------------

- racket-mode support and scheme support are not well tested as I use Geiser.
- The ```eir-always-split-script-window``` option is not functional for cider.
- The choice of a buffer for the REPL is dependent on the corresponding major/minor modes, and may be erratic.
- cider currently requires manual start up with ```cider-jack-in```.
- The Geiser support is incompatible with the racket-mode support (racket-mode major mode is incompatible with Geiser) and with the scheme-mode support (Geiser will invoke Guile Scheme for .scm files).


**Version history**
--------------------

- 2017-07-30 0.9.6 Fix the implementation for ```inf-ruby```.
- 2017-07-30 0.9.5 Add ```eir-use-python-shell-send-string``` option (default to ```t```). This avoids errors on blank lines by using ```python-mode```'s ```python-shell-send-string``` function. However, this does not allow showing code in the REPL. To recover the old behavior, set to ```nil```.
- 2016-12-24 0.9.4 Add ```eir-ielm-eval-in-current-buffer```. When this is ```t```, ielm's ```ielm-working-buffer``` is always changed to the current buffer prior to evaluation.
- 2016-04-18 0.9.3 Drop cider REPL start up function since it was not working.
- 2016-02-27 0.9.2 Deactivate selection explicitly as it is required in Emacs 25.
- 2016-01-17 0.9.1 Add ```eir-always-split-script-window```, which when turned on, splits the current script window at REPL start up, but does not replace any other window.
- 2016-01-01 0.9.0 Do not mess with the window layout at REPL startup (as much as before). ```eir-repl-placement``` option to control where the REPL shows up. New dependency on ```ace-window.el```.
- 2015-11-22 0.8.0 Add Javascript support (Thanks stardiviner); Drop essh.el dependency
- 2015-09-05 0.7.0 Add Prolog support (Thanks m00nlight); no jump option for other languages
- 2015-06-05 0.6.0 Add defcustom configuration to configure whether to jump after eval (Thanks arichiardi)
- 2014-12-28 0.5.1 Refactoring, comment and documentation changes.
- 2014-12-21 0.5.0 Add Hy and OCaml support
- 2014-12-04 0.4.1 Require slime-repl.el (Thanks syohex)
- 2014-11-26 0.4.0 Add Ruby support
- 2014-11-12 0.3.0 Add Standard ML support
- 2014-09-13 0.2.1 Add EOF handling for Python
- 2014-08-30 0.2.0 Add Geiser and Racket support
- 2014-07-06 0.1.1 Delete excess autoload macros, add paredit.el to dependency
- 2014-06-30 0.1.0 First MELPA Release


**Special thanks:**
--------------------

- This package was inspired by the wonderful Emacs Speaks Statistics (ESS) package.
- stardiviner https://github.com/stardiviner contributed the Javascript support and suggested better window handling.
- Yushi Wang https://github.com/m00nlight contributed the Prolog support.
- David Högberg https://github.com/dfh contributed temporary reversal of no jump configuration.
- Andrea Richiardi https://github.com/arichiardi contributed the no jump customization.
- Syohei YOSHIDA https://github.com/syohex contributed a fix for a missing dependency.
