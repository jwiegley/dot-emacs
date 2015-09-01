;;; helm-C-x-b.el --- C-x b replacement based on helm-cmd-t

;; this file is not part of Emacs

;; Copyright (C) 2012 Le Wang
;; Author: Le Wang
;; Maintainer: Le Wang
;; Description: C-x b replacement based on helm-cmd-t
;; Author: Le Wang
;; Maintainer: Le Wang

;; Created: Tue Jul 24 23:28:07 2012 (+0800)
;; Version: 0.1

;;; Installation:

;; (require 'helm-C-x-b)
;;
;; (global-set-key [remap switch-to-buffer] 'helm-C-x-b)
;;

;;; Commentary:

;; This is a demonstration of how to use the helm-cmd-t source to form your
;; own choose-dwim-command.
;;
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Code:

(eval-when-compile (require 'cl))

(require 'helm-cmd-t)

(provide 'helm-C-x-b)

(defvar helm-C-x-b-sources '(helm-source-buffers-list
                             helm-source-session
                             helm-source-files-in-current-dir
                             helm-source-cmd-t
                             helm-source-buffer-not-found)
  "list of sources used for selecting files.

This could be used as a drop-in replacement for `switch-to-buffer'.

`helm-source-cmd-t' is a place-holder.
")

(defun helm-C-x-replace-in-list (list item replacement)
  "Reaplace ITEM with REPLACEMENT in LIST.

If REPLACEMENT is nil, then remove ITEM from the list."
  (let (before found)
    (loop for i on list
          do (if (eq (car i) item)
                 (progn
                   (setq found i)
                   (return))
               (setq before i)))
    (when found
        (if replacement
            (setcar found replacement)
          (if before
              (setcdr before (cdr found))
            ;; found as first item
            (setq list (cdr list)))))
    list))

(defun helm-C-x-b-sources ()
  "construct list of sources based on `helm-C-x-b-sources'.

`helm-source-cmd-t' is replaced with an appropriate item .
"
  (let ((root-data (helm-cmd-t-root-data)))
    (helm-C-x-replace-in-list (append helm-C-x-b-sources '()) ; copy
                              'helm-source-cmd-t (if root-data
                                                     (helm-cmd-t-get-create-source root-data)
                                                   nil))))


(defun helm-C-x-b (arg)
  "This command is designed to be a drop-in replacement for switch to buffer.

With universal prefix arg (C-u), run `helm-cmd-t-repos'.
"
  (interactive "P")
  (if (consp arg)
      (call-interactively 'helm-cmd-t-repos)
    (let ((helm-ff-transformer-show-only-basename nil))
      (helm :sources (helm-C-x-b-sources)
            :candidate-number-limit 20
            :buffer "*helm-cmd-t:*"))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; helm-C-x-b.el ends here
