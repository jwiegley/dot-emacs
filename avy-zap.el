;;; avy-zap.el --- Zap to char using `avy'

;; Copyright (C) 2015  Junpeng Qiu

;; Author: Junpeng Qiu <qjpchmail@gmail.com>
;; URL: https://github.com/cute-jumper/avy-zap
;; Package-Requires: ((avy "0.2.0"))
;; Keywords: extensions

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

;;                              _____________

;;                                 AVY-ZAP

;;                               Junpeng Qiu
;;                              _____________


;; Table of Contents
;; _________________

;; 1 Setup
;; 2 Usage
;; 3 Customization
;; 4 Compared to ace-jump-zap
;; 5 Related packages


;; [[file:http://melpa.org/packages/avy-zap-badge.svg]]
;; [[file:http://stable.melpa.org/packages/avy-zap-badge.svg]]

;; Zap to char using [avy].

;; Note: The behaviors of the *dwim* function when called with prefix and
;; without prefix are inverted now! By default(i.e. when the *dwim*
;; function is called without prefix), the avy version will be used now!
;; For those who want the old behavior, set the following variable to
;; `nil':
;; ,----
;; | (setq avy-zap-dwim-prefer-avy nil)
;; `----

;; This package is basically a fork of the functionality of [ace-jump-zap],
;; but using [avy] instead of [ace-jump-mode] as the jumping method.


;; [[file:http://melpa.org/packages/avy-zap-badge.svg]]
;; http://melpa.org/#/avy-zap

;; [[file:http://stable.melpa.org/packages/avy-zap-badge.svg]]
;; http://stable.melpa.org/#/avy-zap

;; [avy] https://github.com/abo-abo/avy

;; [ace-jump-zap] https://github.com/waymondo/ace-jump-zap

;; [ace-jump-mode] https://github.com/winterTTr/ace-jump-mode


;; 1 Setup
;; =======

;;   ,----
;;   | (add-to-list 'load-path "/path/to/avy-zap.el")
;;   | (require 'avy-zap)
;;   `----

;;   Recommendation: install `avy-zap' via [melpa].


;; [melpa] http://melpa.org


;; 2 Usage
;; =======

;;   Use `avy-zap-to-char' or `avy-zap-up-to-char' to perform `zap-to-char'
;;   or `zap-up-to-char' in "avy-style"!

;;   There are two *Do-What-I-Mean* versions: `avy-zap-to-char-dwim' and
;;   `avy-zap-up-to-char-dwim'. `avy-zap-(up-)to-char-dwim' will perform
;;   `zap-(up-)to-char' with prefix. If calling *dwim* versions without
;;   prefix, then `avy-zap-(up-)to-char' will be used instead. The plain
;;   `zap-(up-)to-char' will also be used when you are defining or
;;   executing a macro.

;;   You can give key bindings to these commands. For example:
;;   ,----
;;   | (global-set-key (kbd "M-z") 'avy-zap-to-char-dwim)
;;   | (global-set-key (kbd "M-Z") 'avy-zap-up-to-char-dwim)
;;   `----


;; 3 Customization
;; ===============

;;   - `avy-zap-forward-only': Setting this variable to non-nil means
;;     zapping from the current point. The default value is `nil'.
;;   - `avy-zap-function': Choose between `kill-region' and
;;     `delete-region'. The default value is `kill-region'.
;;   - `avy-zap-dwim-prefer-avy': Whether the default dwim behavior(when
;;     called without prefix) of `avy-zap' should use `avy' or not. The
;;     default value is `t'. You can set this variable to `nil' if you
;;     prefer using plain zap when calling the dwim commands without
;;     prefix.


;; 4 Compared to ace-jump-zap
;; ==========================

;;   This package provides the same functionality as `ace-jump-zap', but
;;   lacks the `ajz/sort-by-closest' and `ajz/52-character-limit'
;;   customization options. I don't use the sorting feature of
;;   `ace-jump-zap', but if someone finds it useful, welcome to submit a
;;   pull request!


;; 5 Related packages
;; ==================

;;   - [ace-jump-zap]
;;   - [avy]


;; [ace-jump-zap] https://github.com/waymondo/ace-jump-zap

;; [avy] https://github.com/abo-abo/avy

;;; Code:

(require 'avy)

(autoload 'zap-up-to-char "misc"
  "Kill up to, but not including ARGth occurrence of CHAR.")

(defvar avy-zap-forward-only nil
  "Non-nil means zap forward from the current point.")

(defvar avy-zap-function 'kill-region
  "The function used for zapping to char.")

(defvar avy-zap-dwim-prefer-avy t
  "Whether the default dwim behavior of `avy-zap' should use `avy' or not.")

(defmacro avy-zap--flet-if (rebind-p binding &rest body)
  "If REBIND-P, temporarily override BINDING and execute BODY.
Otherwise, don't rebind."
  (declare (indent 2))
  (let* ((name (car binding))
         (old (cl-gensym (symbol-name name))))
    `(if ,rebind-p
         (let ((,old (symbol-function ',name)))
           (unwind-protect
               (progn
                 (fset ',name (lambda ,@(cdr binding)))
                 ,@body)
             (fset ',name ,old)))
       ,@body)))

(defsubst avy-zap--xor (a b)
  "Exclusive-or of A and B."
  (if a (not b) b))

(defun avy-zap--internal (&optional zap-up-to-char-p)
  "If ZAP-UP-TO-CHAR-P, perform `zap-up-to-char'."
  (let ((start (point))
        avy-all-windows)
    (avy-zap--flet-if
        avy-zap-forward-only
        (window-start (&optional window) (point))
      (if (or (equal avy-zap-function 'kill-region)
              (equal avy-zap-function 'delete-region))
          (and (numberp (call-interactively 'avy-goto-char))
               (funcall avy-zap-function start
                        (progn
                          (when (avy-zap--xor
                                 (<= start (point))
                                 zap-up-to-char-p)
                            (forward-char))
                          (point))))
        (error "Unknown value for `avy-zap-function'!\
 Please choose between `kill-region' and `delete-region'")))))

;;;###autoload
(defun avy-zap-to-char ()
  "Zap to char using `avy'."
  (interactive)
  (avy-zap--internal))

;;;###autoload
(defun avy-zap-to-char-dwim (&optional prefix)
  "Without PREFIX, call `avy-zap-to-char'.
With PREFIX, call `zap-to-char'."
  (interactive "P")
  (if (or defining-kbd-macro executing-kbd-macro
          (not (avy-zap--xor prefix avy-zap-dwim-prefer-avy)))
      (let (current-prefix-arg)
        (call-interactively 'zap-to-char))
    (avy-zap-to-char)))

;;;###autoload
(defun avy-zap-up-to-char ()
  "Zap up to char using `avy'."
  (interactive)
  (avy-zap--internal t))

;;;###autoload
(defun avy-zap-up-to-char-dwim (&optional prefix)
  "Without PREFIX, call `avy-zap-up-to-char'.
With PREFIX, call `zap-up-to-char'."
  (interactive "P")
  (if (or defining-kbd-macro executing-kbd-macro
          (not (avy-zap--xor prefix avy-zap-dwim-prefer-avy)))
      (let (current-prefix-arg)
        (call-interactively 'zap-up-to-char))
    (avy-zap-up-to-char)))

(provide 'avy-zap)
;;; avy-zap.el ends here
