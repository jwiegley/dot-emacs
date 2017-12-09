;;; eval-in-repl-racket.el --- ESS-like eval for racket  -*- lexical-binding: t; -*-

;; Copyright (C) 2014-  Kazuki YOSHIDA

;; Author: Kazuki YOSHIDA <kazukiyoshida@mail.harvard.edu>
;; Keywords: tools, convenience
;; URL: https://github.com/kaz-yos/eval-in-repl
;; Version: 0.9.4

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.


;;; Commentary:

;; racket.el-specific file for eval-in-repl
;; See below for configuration
;; https://github.com/kaz-yos/eval-in-repl/


;;; Code:

;;;
;;; Require dependencies
(require 'eval-in-repl)
(require 'racket-mode)


;;;
;;; RACKET RELATED
;;; eir-send-to-racket
(defalias 'eir-send-to-racket
  (apply-partially 'eir-send-to-repl
                   ;; fun-change-to-repl
                   #'(lambda ()
                       ;; Show Racket REPL (focus comes back)
                       (racket--repl-show-and-move-to-end)
                       ;; Go to the other window
                       (other-window 1))
                   ;; fun-execute
                   #'comint-send-input)
  "Send expression to *Racket REPL* and have it evaluated.")


;;; eir-eval-in-racket
;;;###autoload
(defun eir-eval-in-racket ()
  "eval-in-repl for Racket."
  (interactive)
  (eir-eval-in-repl-lisp
   ;; repl-buffer-regexp
   "\\*Racket REPL.*\\*$"
   ;; fun-repl-start
   #'racket-repl
   ;; fun-repl-send
   #'eir-send-to-racket
   ;; defun-string
   "(define "))


(provide 'eval-in-repl-racket)
;;; eval-in-repl-racket.el ends here

