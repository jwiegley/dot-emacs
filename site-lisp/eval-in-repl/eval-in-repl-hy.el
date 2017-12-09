;;; eval-in-repl-hy.el --- ESS-like eval for hy mode  -*- lexical-binding: t; -*-

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

;; scheme.el-specific file for eval-in-repl
;; See below for configuration
;; https://github.com/kaz-yos/eval-in-repl/


;;; Code:

;;;
;;; Require dependencies
(require 'eval-in-repl)
(require 'hy-mode)
(require 'inf-lisp)


;;;
;;; HY RELATED
;;; eir-send-to-hy
(defalias 'eir-send-to-hy
  (apply-partially 'eir-send-to-repl
                   ;; fun-change-to-repl
                   #'(lambda ()
                       ;; Move to the other window
                       (other-window 1)
                       ;; Change to hy REPL
                       (switch-to-lisp t))
                   ;; fun-execute
                   #'comint-send-input)
  "Send expression to *inferior-lisp* and have it evaluated.")


;;; inferior-hy
(defun eir-inferior-hy ()
  "Call inferior hy process at any buffer"
  (interactive)
  (inferior-lisp hy-mode-inferior-lisp-command))


;;; eir-eval-in-hy
;;;###autoload
(defun eir-eval-in-hy ()
  "eval-in-repl for Hy."
  (interactive)
  (eir-eval-in-repl-lisp
   ;; repl-buffer-regexp
   "\\*inferior-lisp\\*"
   ;; fun-repl-start
   'eir-inferior-hy
   ;; fun-repl-send
   'eir-send-to-hy
   ;; defun-string
   "(defn "))


(provide 'eval-in-repl-hy)
;;; eval-in-repl-hy.el ends here
