;;; eval-in-repl-geiser.el --- ESS-like eval for geiser  -*- lexical-binding: t; -*-

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

;; geiser.el-specific file for eval-in-repl
;; See below for configuration
;; https://github.com/kaz-yos/eval-in-repl/


;;; Code:

;;;
;;; Require dependencies
(require 'eval-in-repl)
(require 'geiser-mode)


;;;
;;; GEISER RELATED
;;; eir-send-to-geiser
(defalias 'eir-send-to-geiser
  (apply-partially 'eir-send-to-repl
                   ;; fun-change-to-repl
                   #'switch-to-geiser
                   ;; fun-execute
                   #'geiser-repl--maybe-send)
  "Send expression to * Racket/Guile REPL * and have it evaluated.")


;;; eir-eval-in-geiser
;;;###autoload
(defun eir-eval-in-geiser ()
  "eval-in-repl for Geiser."
  (interactive)
  (eir-eval-in-repl-lisp
   ;; repl-buffer-regexp
   "\\* Racket REPL.*\\*$\\|\\* Guile REPL.*\\*$"
   ;; fun-repl-start
   #'run-geiser
   ;; fun-repl-send
   #'eir-send-to-geiser
   ;; defun-string
   "(define "
   ;; exec-in-script
   t))


(provide 'eval-in-repl-geiser)
;;; eval-in-repl-geiser.el ends here
