;;; eval-in-repl-sml.el --- ESS-like eval for Standard ML  -*- lexical-binding: t; -*-

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

;; sml-mode.el-specific file for eval-in-repl
;; See below for configuration
;; https://github.com/kaz-yos/eval-in-repl/


;;; Code:

;;;
;;; Require dependencies
(require 'eval-in-repl)
(require 'sml-mode)


;;;
;;; SML RELATED
;; depends on sml-mode
;;
;;; eir-send-to-sml
(defalias 'eir-send-to-sml
  (apply-partially 'eir-send-to-repl
                   ;; fun-change-to-repl
                   #'(lambda () (switch-to-buffer-other-window "*sml*"))
                   ;; fun-execute
                   #'comint-send-input)
  "Send expression to *sml* and have it evaluated.")


;;; eir-eval-in-sml
;;;###autoload
(defun eir-eval-in-sml ()
  "eval-in-repl for Standard ML."
  (interactive)
  ;; Define local variables
  (let* (;; Save current point
	 (initial-point (point)))

    ;; If buffer named *sml* is not found, invoke sml-run
    (eir-repl-start "\\*sml\\*" #'sml-run t)

    ;; Check if selection is present
    (if (and transient-mark-mode mark-active)
	;; If selected, send region
	(eir-send-to-sml (buffer-substring-no-properties (point) (mark)))

      ;; If not selected, do all the following
      ;; Move to the beginning of line
      (beginning-of-line)
      ;; Set mark at current position
      (set-mark (point))
      ;; Go to the end of line
      (end-of-line)
      ;; Send region if not empty
      (if (not (equal (point) (mark)))
	  (eir-send-to-sml (buffer-substring-no-properties (point) (mark)))
	;; If empty, deselect region
	(setq mark-active nil))

      ;; Move to the next statement code if jumping
      (if eir-jump-after-eval
          (eir-next-code-line)
        ;; Go back to the initial position otherwise
        (goto-char initial-point)))))


;;; eir-send-to-sml-semicolon
(defun eir-send-to-sml-semicolon ()
  "Send a semicolon to *sml* and have it evaluated."
  (interactive)
  (eir-send-to-sml ";"))


(provide 'eval-in-repl-sml)
;;; eval-in-repl-sml.el ends here

