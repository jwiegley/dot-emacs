;;; paredit-ext --- Extra functions for paredit

;; Copyright (C) 2012 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 03 Jul 2012
;; Version: 1.0
;; Keywords: paredit lisp
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; These commands are ones that I use very often.

(require 'paredit)

(defgroup paredit-ext nil
  "Extra functions for paredit"
  :group 'paredit)

(defun mark-containing-sexp ()
  (interactive)
  (paredit-backward-up)
  (mark-sexp))

(defun paredit-barf-all-the-way-backward ()
  (interactive)
  (paredit-split-sexp)
  (paredit-backward-down)
  (paredit-splice-sexp))

(defun paredit-barf-all-the-way-forward ()
  (interactive)
  (paredit-split-sexp)
  (paredit-forward-down)
  (paredit-splice-sexp)
  (if (eolp) (delete-horizontal-space)))

(defun paredit-slurp-all-the-way-backward ()
  (interactive)
  (catch 'done
    (while (not (bobp))
      (save-excursion
        (paredit-backward-up)
        (if (eq (char-before) ?\()
            (throw 'done t)))
      (paredit-backward-slurp-sexp))))

(defun paredit-slurp-all-the-way-forward ()
  (interactive)
  (catch 'done
    (while (not (eobp))
      (save-excursion
        (paredit-forward-up)
        (if (eq (char-after) ?\))
            (throw 'done t)))
      (paredit-forward-slurp-sexp))))

(nconc paredit-commands
       '("Extreme Barfage & Slurpage"
         (("C-M-)")
          paredit-slurp-all-the-way-forward
          ("(foo (bar |baz) quux zot)"
           "(foo (bar |baz quux zot))")
          ("(a b ((c| d)) e f)"
           "(a b ((c| d)) e f)"))
         (("C-M-}")
          paredit-barf-all-the-way-forward
          ("(foo (bar |baz quux) zot)"
           "(foo (bar|) baz quux zot)"))
         (("C-M-(")
          paredit-slurp-all-the-way-backward
          ("(foo bar (baz| quux) zot)"
           "((foo bar baz| quux) zot)")
          ("(a b ((c| d)) e f)"
           "(a b ((c| d)) e f)"))
         (("C-M-{")
          paredit-barf-all-the-way-backward
          ("(foo (bar baz |quux) zot)"
           "(foo bar baz (|quux) zot)"))))

(paredit-define-keys)
(paredit-annotate-mode-with-examples)
(paredit-annotate-functions-with-examples)

(provide 'paredit-ext)

;;; paredit-ext.el ends here
