;;; ee-ps.el --- display CPU processes

;; Copyright (C) 2002, 2003, 2004, 2010  Juri Linkov <juri@jurta.org>

;; Author: Juri Linkov <juri@jurta.org>
;; Keywords: ee

;; This file is [not yet] part of GNU Emacs.

;; This package is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This package is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this package; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; See the file README and documentation for more information.

;;; Code:

(require 'ee)

;;; Constants

(defconst ee-ps-mode-name "ee-ps")

;;; Customizable Variables

(defgroup ee-ps nil
  "Display CPU processes."
  :prefix "ee-ps-"
  :group 'ee)

(defcustom ee-ps-program "ps"
  "Name of ps command (usually `ps')."
  :type 'string
  :group 'ee-ps)

(defcustom ee-ps-program-switches '("aux")
  "Switches passed to `ps' (usually `aux')."
  :type '(repeat string)
  :group 'ee-ps)

;;; Data Description

(defvar ee-ps-data
  '[(meta
     (format-version . "0.0.1")
     (view-data-file . "view/ps.ee")
     (collector . ee-ps-data-collect)
     (fields ())
     (key-fields PID))])

;;; Data Extraction

(defun ee-ps-data-collect (data)
  (let ((new-data
         (ee-data-convert-lists-to-vectors
          (with-temp-buffer
            (apply 'call-process ee-ps-program nil t nil
                   (if (consp ee-ps-program-switches)
                       ee-ps-program-switches
                     (list ee-ps-program-switches)))
            (goto-char (point-min))
            (let ((field-names
                   (if (looking-at "\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\(.*\\)")
                       (vector nil
                               (intern (match-string-no-properties 1))
                               (intern (match-string-no-properties 2))
                               (intern (match-string-no-properties 3))
                               (intern (match-string-no-properties 4))
                               (intern (match-string-no-properties 5))
                               (intern (match-string-no-properties 6))
                               (intern (match-string-no-properties 7))
                               (intern (match-string-no-properties 8))
                               (intern (match-string-no-properties 9))
                               (intern (match-string-no-properties 10))
                               (intern (match-string-no-properties 11)))))
                  res)
              (forward-line 1)
              (while (not (eobp))
                (if (looking-at "\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\([^ ]+\\) +\\(.*\\)")
                    (setq res (cons
                               (list
                                (list (cons (aref field-names 1) (match-string-no-properties 1))
                                      (cons (aref field-names 2) (string-to-int (match-string-no-properties 2))) ; bad hack
                                      (cons (aref field-names 3) (string-to-int (match-string-no-properties 3))) ; bad hack
                                      (cons (aref field-names 4) (match-string-no-properties 4))
                                      (cons (aref field-names 5) (match-string-no-properties 5))
                                      (cons (aref field-names 6) (match-string-no-properties 6))
                                      (cons (aref field-names 7) (match-string-no-properties 7))
                                      (cons (aref field-names 8) (match-string-no-properties 8))
                                      (cons (aref field-names 9) (match-string-no-properties 9))
                                      (cons (aref field-names 10) (match-string-no-properties 10))
                                      (cons (aref field-names 11) (match-string-no-properties 11))))
                               res)))
                (forward-line 1))
              (nreverse res))))))
    (aset new-data 0 (aref data 0))
    new-data))

;;; Actions

(defun ee-ps-execute (r marks)
  (mapc (lambda (mark)
          (cond
           ((eq mark ee-mark-del)
            (start-process "kill" nil "kill" "-9"
                           (number-to-string (ee-field 'PID r))))))
        marks))

;;; Key Bindings

(defvar ee-ps-keymap nil
  "Local keymap for ee-ps mode.")

(defun ee-ps-keymap-make-default ()
  "Defines default key bindings for `ee-ps-keymap'.
It inherits key bindings from `ee-mode-map'."
  (or ee-mode-map
      (ee-mode-map-make-default))
  (let ((map (copy-keymap ee-mode-map)))
    ;; (define-key map "\C-o" 'ee-ps-start-process)
    (setq ee-ps-keymap map)))

(or ee-ps-keymap
    (ee-ps-keymap-make-default))

;;; Top-Level Functions

;;;###autoload
(defun ee-ps (&optional arg)
  "Display CPU processes."
  (interactive "P")
  (ee-view-buffer-create
   (format "*%s*" ee-ps-mode-name)
   ee-ps-mode-name
   ee-ps-keymap
   ee-ps-data))

;;;###autoload (fset 'ee-top 'ee-ps)

(provide 'ee-ps)

;;; ee-ps.el ends here
