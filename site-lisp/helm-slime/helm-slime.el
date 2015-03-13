;;; helm-slime.el --- helm-sources and some utilities for SLIME.

;; Copyright (C) 2009 Takeshi Banse <takebi@laafc.net>
;;               2012 Michael Markert <markert.michael@googlemail.com>
;; Author: Takeshi Banse <takebi@laafc.net>
;; Keywords: convenience, helm, slime

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:
;;
;; Some Helm and SLIME Configurations for using SLIME within the
;; Helm interface. (The `ascsa-' prefix comes here.)

;;; Installation:
;;
;; Put the helm-slime.el, helm.el to your load-path.
;; Set up the SLIME properly.
;; Call `slime-setup' and include 'helm-slime as the arguments:
;;
;;   (slime-setup '([others contribs ...] helm-slime))
;;
;; or simply require helm-slime in some appropriate manner.

;;; Commands:
;;
;; Below are complete command list:
;;
;;  `helm-slime-complete'
;;    Select a symbol from the SLIME's completion systems.
;;  `helm-slime-list-connections'
;;    Yet another `slime-list-connections' with `helm'.
;;  `helm-slime-apropos'
;;    Yet another `slime-apropos' with `helm'.
;;  `helm-slime-repl-history'
;;    Select an input from the SLIME repl's history and insert it.
;;

;;; Code:

(require 'helm)
(require 'slime)
(require 'slime-c-p-c)
(require 'slime-fuzzy)
(require 'slime-repl)


(defvar ascsa-complete-target "")

(defun ascsa-insert (candidate)
  (let ((pt (point)))
    (when (and (search-backward ascsa-complete-target nil t)
               (string= (buffer-substring (point) pt) ascsa-complete-target))
      (delete-region (point) pt)))
  (insert candidate))

(defun* ascsa-symbol-position-funcall
    (f &optional (end-pt (point)) (beg-pt (slime-symbol-start-pos)))
  (let* ((end (move-marker (make-marker) end-pt))
         (beg (move-marker (make-marker) beg-pt)))
    (unwind-protect
        (funcall f beg end)
      (set-marker end nil)
      (set-marker beg nil))))

(define-helm-type-attribute 'helm-slime-complete
  '((action
     . (("Insert" . ascsa-insert)
        ("Describe symbol" . slime-describe-symbol)
        ("Edit definition" . slime-edit-definition)))
    (persistent-action . slime-describe-symbol)
    (volatile)
    (candidates-in-buffer)
    (get-line . buffer-substring))
  "SLIME complete.")

(defun ascsa-asc-init-candidates-buffer-base (complete-fn insert-fn)
  (let ((put-text-property1 (lambda (s)
                              (put-text-property (point-at-bol 0)
                                                 (point-at-eol 0)
                                                 'helm-realvalue
                                                 s))))
    (let* ((completion-result (with-current-buffer helm-current-buffer
                                (funcall complete-fn)))
           (completions (first completion-result))
           (base  (second completion-result)))
      (with-current-buffer (helm-candidate-buffer 'global)
        (funcall insert-fn completions base put-text-property1)))))
(defun ascsa-asc-init-candidates-buffer-basic-insert-function (completions base put-text-property1)
  (let ((len (length base)))
    (dolist (c completions)
      (let ((start (point))
            end)
        (insert c)
        (setq end (point))
        (put-text-property start (+ start len) 'face 'bold)
        (insert "\n")
        (funcall put-text-property1 c)))))
(defun ascsa-asc-simple-init ()
  (ascsa-asc-init-candidates-buffer-base
   (slime-curry 'slime-simple-completions ascsa-complete-target)
   'ascsa-asc-init-candidates-buffer-basic-insert-function))
(defun ascsa-asc-compound-init ()
  (ascsa-asc-init-candidates-buffer-base
   (slime-curry 'ascsa-symbol-position-funcall 'slime-contextual-completions)
   'ascsa-asc-init-candidates-buffer-basic-insert-function))
(defun* ascsa-asc-fuzzy-init (&optional
                              (insert-choice-fn
                               'slime-fuzzy-insert-completion-choice))
  (ascsa-asc-init-candidates-buffer-base
   (slime-curry 'slime-fuzzy-completions ascsa-complete-target)
   (lambda (completions _ put-text-property1)
     (with-current-buffer (helm-candidate-buffer 'global)
       (let ((max-len (loop for (x _) in completions maximize (length x))))
         (dolist (c completions)
           (funcall insert-choice-fn c max-len)
           (funcall put-text-property1 (car c))))))))
;; These sources are private for the use of the `helm-slime-complete'
;; command, so I should not make `helm-c-source-*' symbols.
(defvar helm-slime-simple-complete-source
  '((name . "SLIME simple complete")
    (init . ascsa-asc-simple-init)
    (type . helm-slime-complete)))
(defvar helm-slime-compound-complete-source
  '((name . "SLIME compound complete")
    (init . ascsa-asc-compound-init)
    (type . helm-slime-complete)))
(defvar helm-slime-fuzzy-complete-source
  '((name . "SLIME fuzzy complete")
    (init . ascsa-asc-fuzzy-init)
    (type . helm-slime-complete)))
(defvar helm-slime-complete-sources
  '(helm-slime-simple-complete-source
    helm-slime-fuzzy-complete-source
    helm-slime-compound-complete-source))

(defun ascsa-helm-complete (sources target &optional limit idle-delay input-idle-delay target-is-default-input-p)
  (let ((helm-candidate-number-limit (or limit helm-candidate-number-limit))
        (helm-idle-delay (or idle-delay helm-idle-delay))
        (helm-input-idle-delay (or input-idle-delay helm-input-idle-delay))
        (helm-complete-targettarget target)
        (helm-execute-action-at-once-if-one t)
        (ascsa-complete-target target)
        (enable-recursive-minibuffers t)
        helm-samewindow)
    (helm :sources sources
          :input (if target-is-default-input-p target nil)
          :buffer "*helm complete*")))

(defun helm-slime-complete ()
  "Select a symbol from the SLIME's completion systems."
  (interactive)
  (ascsa-helm-complete helm-slime-complete-sources
                       (ascsa-symbol-position-funcall
                        #'buffer-substring-no-properties)))

(defvar helm-c-source-slime-connection
  '((name . "SLIME connections")
    (candidates
     . (lambda ()
         (let ((fstring "%s%2s  %-10s  %-17s  %-7s %-s")
               (collect (lambda (p)
                          (cons
                           (format fstring
                                   (if (eq slime-default-connection p) "*" " ")
                                   (slime-connection-number p)
                                   (slime-connection-name p)
                                   (or (process-id p) (process-contact p))
                                   (slime-pid p)
                                   (slime-lisp-implementation-type p))
                           p))))
           (mapcar collect (reverse slime-net-processes)))))
    (action
     . (("Go to repl"
         . (lambda (p)
             (let ((slime-dispatching-connection p))
               (switch-to-buffer (slime-output-buffer)))))
        ("Set default" . slime-select-connection)
        ("Restart" . slime-restart-connection-at-point)
        ("Quit" . slime-quit-connection-at-point)))))

(defun helm-slime-list-connections ()
  "Yet another `slime-list-connections' with `helm'."
  (interactive)
  (helm 'helm-c-source-slime-connection))

(defadvice helm-slime-update-connection-list (around ignore activate)
  "Don't call slime-update-connection-list if helming. (This is iffy.)"
  (when (not helm-source-name)
    ad-do-it))

(define-helm-type-attribute 'helm-slime-apropos
  '((action
     . (("Describe symbol" . slime-describe-symbol)
        ("Edit definition" . slime-edit-definition)))
    (persistent-action . slime-describe-symbol)
    (requires-pattern . 2))
    ;;(volatile)
  "SLIME apropos.")

(defun ascsa-apropos-source (name slime-expressions)
  `((name . ,name)
    (candidates
     . (lambda ()
         (with-current-buffer helm-current-buffer
           (loop for plist in (slime-eval ,slime-expressions)
                 collect (plist-get plist :designator)))))
    (type . helm-slime-apropos)))
(defvar helm-c-source-slime-apropos-symbol-current-package
  (ascsa-apropos-source "SLIME apropos (current package)"
                        (quote
                         `(swank:apropos-list-for-emacs
                           ,helm-pattern
                           nil
                           nil
                           ,(or slime-buffer-package
                                (slime-current-package))))))
(defvar helm-c-source-slime-apropos-symbol-current-external-package
  (ascsa-apropos-source "SLIME apropos (current external package)"
                        (quote
                         `(swank:apropos-list-for-emacs
                           ,helm-pattern
                           t
                           nil
                           ,(or slime-buffer-package
                                (slime-current-package))))))
(defvar helm-c-source-slime-apropos-symbol-all-external-package
  (ascsa-apropos-source "SLIME apropos (all external package)"
                        (quote
                         `(swank:apropos-list-for-emacs
                           ,helm-pattern
                           t
                           nil
                           nil))))
(defvar helm-c-source-slime-apropos-symbol-all-package
  (ascsa-apropos-source "SLIME apropos (all package)"
                        (quote
                         `(swank:apropos-list-for-emacs
                           ,helm-pattern
                           nil
                           nil
                           nil))))
(defvar helm-slime-apropos-sources
  '(helm-c-source-slime-apropos-symbol-current-package
    helm-c-source-slime-apropos-symbol-current-external-package
    helm-c-source-slime-apropos-symbol-all-external-package
    helm-c-source-slime-apropos-symbol-all-package))

(defun helm-slime-apropos ()
  "Yet another `slime-apropos' with `helm'."
  (interactive)
  (helm :sources helm-slime-apropos-sources
        :buffer "*helm SLIME apropos*"))

(defvar helm-c-source-slime-repl-history
  `((name . "SLIME repl history")
    (candidates
     . (lambda ()
         (with-current-buffer helm-current-buffer
           slime-repl-input-history)))
    ;;(multiline)
    (action
     . (lambda (cand)
         (slime-repl-history-replace 'backward
                                     (concat "^" (regexp-quote cand) "$"))))))
(defun helm-slime-repl-history ()
  "Select an input from the SLIME repl's history and insert it."
  (interactive)
  (ascsa-helm-complete helm-c-source-slime-repl-history
                       (ascsa-symbol-position-funcall
                        #'buffer-substring-no-properties
                        (point)
                        slime-repl-input-start-mark)
                       nil nil nil t))

(defun helm-slime-init ()
  (run-hooks 'helm-slime-init-hook))

(provide 'helm-slime)
;;; helm-slime.el ends here
