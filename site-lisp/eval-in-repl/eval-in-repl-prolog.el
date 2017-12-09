;;; eval-in-repl-prolog.el --- ESS-like eval for Standard ML  -*- lexical-binding: t; -*-

;; Copyright (C) 2015  Yushi Wang

;; Author: Yushi Wang <dot_wangyushi@yeah.net>
;; Keywords: tools, convenience
;; URL: https://github.com/kaz-yos/eval-in-repl

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

;; prolog-mode.el-specific file for eval-in-repl
;; See below for configuration
;; https://github.com/kaz-yos/eval-in-repl/


;;; Code:

;;;
;;; Require dependencies
(require 'eval-in-repl)

;;;
;;; PROLOG RELATED
;;
;;; eir-send-to-prolog
(defun eir-send-to-prolog (beg end)
  "Send expression to *prolog* and have it evaluated."
  (prolog-consult-region beg end))



;;; eir-eval-in-prolog
;;;###autoload
(defun eir-eval-in-prolog ()
  "eval-in-repl for SWI Prolog."
  (interactive)
  ;; Define local variables
  (let* (;; Save current point
	 (initial-point (point)))

    ;; If buffer named *prolog* is not found, invoke run-prolog
    (eir-repl-start "\\*prolog\\*" #'run-prolog t)

    ;; Check if selection is present
    (if (and transient-mark-mode mark-active)
	;; If selected, send region
	(eir-send-to-prolog (point) (mark))
      ;; (eir-send-to-prolog (buffer-substring-no-properties (point) (mark)))

      ;; If not selected, do all the following
      ;; Move to the beginning of line
      (beginning-of-line)
      ;; Set mark at current position
      (set-mark (point))
      ;; Go to the end of line
      (end-of-line)
      ;; Send region if not empty
      (if (not (equal (point) (mark)))
	  (eir-send-to-prolog (point) (mark))
	;; If empty, deselect region
	(setq mark-active nil))

      ;; Move to the next statement code if jumping
      (if eir-jump-after-eval
          (eir-next-code-line)
        ;; Go back to the initial position otherwise
        (goto-char initial-point)))))


(provide 'eval-in-repl-prolog)
;;; eval-in-repl-prolog.el ends here

