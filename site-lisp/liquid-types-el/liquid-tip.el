;;; liquid-tip.el --- show inferred liquid-types

;; Copyright (C) 2014 by Ranjit Jhala

;; Author: Ranjit Jhala <jhala@cs.ucsd.edu>
;; Version: 0.0.1
;; Package-Requires: ((flycheck "0.13") (dash "1.2") (emacs "24.1") (popup "0.5.2") (pos-tip "0.5.0"))
;;; License:
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;; see https://github.com/ucsd-progsys/liquidhaskell#emacs

;;; Code:
(eval-when-compile (require 'cl))
(require 'json)
(require 'popup)
(require 'pos-tip nil t)
(require 'thingatpt)
(require 'button-lock)

;; ------------------------------------------------------------------------
;; A structure to represent positions 
;; ------------------------------------------------------------------------

(cl-defstruct position file row col)

;; ------------------------------------------------------------------------
;; Utilities for reading json/files
;; ------------------------------------------------------------------------

(defun get-string-from-file (filePath)
  "Return FILEPATH's file content."
  (with-temp-buffer
    (insert-file-contents filePath)
    (buffer-string)))

(defun get-json-from-file (filePath)
  "Return json object from FILEPATH content."
  (if (file-exists-p filePath)
      (let* ((json-key-type 'string)
	     (str (get-string-from-file filePath)))
	(json-read-from-string str))
      nil))

;; ------------------------------------------------------------------------
;; get/set annot information 
;; ------------------------------------------------------------------------

(defun gethash-nil (key table) 
  "Return the value of KEY from TABLE."
  (if table 
      (gethash key table nil)
      nil))

(defun liquid-annot-filepath-prefix (mode)
  "Return prefix of annotation file using MODE."
  (if (equal mode 'flycheck)
      "flycheck_"
      nil))

;; (liquid-annot 'flycheck "/path/to/file.hs") 
;;    ==> "/path/to/.liquid/flycheck_file.hs.json"
;;
;; (liquid-annot nil       "/path/to/file.hs") 
;;    ==> "/path/to/.liquid/file.hs.json"

(defun liquid-annot-filepath (mode file)
  "Return MODE dependent name of annotation FILE."
  (let* ((dir    (file-name-directory file))
	 (name   (file-name-nondirectory file))
	 (prefix (liquid-annot-filepath-prefix mode)))
    (concat dir ".liquid/" prefix name ".json")))

(defvar liquid-annot-table (make-hash-table :test 'equal))

;; API
(defun liquid-annot-set (file mode)
  "Load information for FILE (in current MODE) into liquid-annot-table."
  (let* ((file-path        (liquid-annot-filepath mode file))
	 (json-object-type 'hash-table)
	 (file-info        (get-json-from-file file-path)))
    (if file-info (puthash file file-info liquid-annot-table))))

;; API
(defun liquid-annot-get (file row col)
  "Get annotation for identifier in FILE at ROW and COL." 
  (let* ((table (gethash-nil file liquid-annot-table))
	 (r     (format "%d" row))
	 (c     (format "%d" col))
	 (tys   (gethash-nil "types" table))
	 (ro    (gethash-nil r tys)))
    (gethash-nil "ann" (gethash-nil c ro))))

;; ------------------------------------------------------------------------
;; Display Annot in Tooltip 
;; ------------------------------------------------------------------------

;; For simple, ascii popups, use:
;;    (setq liquid-tip-mode 'ascii) 
;;
;; For emacs', balloon based popups, use:
;;    (setq liquid-tip-mode 'balloon)

(defvar liquid-tip-mode 'balloon)

(defun pad-line (str)
  "Add extra blanks before and after STR."
  (concat " " str " "))

(defun popup-tip-pad (text)
  "Add extra blanks before and after TEXT."
  (let* ((lines     (split-string text "\n"))
         (pad-lines (mapcar 'pad-line lines))
	 (pad-text  (concat "\n" (mapconcat 'identity pad-lines "\n") "\n")))
    (popup-tip pad-text)))

(defun liquid-tip-popup-balloon (text)
  "Display TEXT in a balloon popup."
  (popup-tip-pad text))

  ;; (if (and (functionp 'ac-quick-help-use-pos-tip-p)
  ;;          (ac-quick-help-use-pos-tip-p))
  ;;     (pos-tip-show text 'popup-tip-face nil nil 300 popup-tip-max-width)
  ;;   (popup-tip-pad text)))

(defun liquid-tip-popup-ascii (text)
 "Display TEXT in ascii popup."
  (popup-tip-pad text))

(defun liquid-tip-popup (text)
  "Display TEXT."
  (if (equal liquid-tip-mode 'ascii)
      (liquid-tip-popup-ascii   text)
      (liquid-tip-popup-balloon text)))

;; -- Compute range ---------------------------------------------------------

(defvar liquid-id-regexp 
  (rx (one-or-more (not (in " \n\t()[]{}")))))

(defun liquid-splitters () 
  "List of  identifier splitters."
  '( ?\s  ?\t ?\n ?\( ?\) ?\[ ?\] ))

(defun liquid-is-split (char)
  "Predicate to check if CHAR is a splitter?"
  (member char (liquid-splitters)))

(defun liquid-id-start-pos (low p)
  "Find the largest position more than LOW but less than P that is a splitter."
  (let* ((ch (char-before p)))
     (if (or (<= p low) (liquid-is-split ch)) 
	 p 
         (liquid-id-start-pos low (- p 1)))))


(defun column-number-at-pos (pos)
  "Find the column of position POS."
  (+ (- pos (line-beginning-position)) 1))

(defun start-column-number-at-pos (pos)
  "Find the starting column of identifier at POS."
     (let* ((low   (line-beginning-position))
	    (start (liquid-id-start-pos low pos)))
       (column-number-at-pos start)))

(defsubst liquid-get-position ()
  "Return the current cursor position."
  (save-excursion
    (widen)
    (make-position
     :file (expand-file-name (buffer-file-name))
     :row  (line-number-at-pos)
     :col  (start-column-number-at-pos (point)))))

(defun position-string (pos)
  "Return the current POS as a string."
  (format "(%s, %s) in [%s]" 
	  (position-row pos) 
	  (position-col pos)
	  (position-file pos)))

;; DEBUG (defun liquid-annot-at-pos-0 (pos)
;; DEBUG   "Info to display: just the file/line/constant string"
;; DEBUG   (let* ((info  (format "hello!")))
;; DEBUG     (format "the information at %s is %s" 
;; DEBUG 	    (position-string pos)
;; DEBUG 	    info)))

;; DEBUG (defun liquid-annot-at-pos-1 (pos)
;; DEBUG   "Info to display: the identifier at the position or NONE" 
;; DEBUG   (let* ((ident (liquid-ident-at-pos pos)))
;; DEBUG     (format "the identifier at %s is %s" 
;; DEBUG 	    (position-string pos) 
;; DEBUG 	    ident)))

(defun liquid-ident-at-pos (pos)
  "Return the identifier at POS."
  (thing-at-point 'word))

(defun liquid-annot-at-pos-2 (pos)
  "Info to display: type annotation for the identifier at POS or NONE." 
  (let* ((file (position-file pos))
	 (row  (position-row  pos))
	 (col  (position-col  pos)))
    (liquid-annot-get file row col)))

(defun liquid-annot-at-pos (pos)
  "Determine info to display at POS."
  (liquid-annot-at-pos-2 pos))

;;;###autoload
(defun liquid-tip-show ()
  "Popup help about anything at point."
  (interactive)
  (let* ((pos    (liquid-get-position))
	 (ident  (liquid-ident-at-pos pos))
	 (sorry  (format "No information for %s" ident))
         (annot  (liquid-annot-at-pos pos)))
    (if annot 
	(liquid-tip-popup annot)
        ;; (hdevtools/show-type-info)
        (liquid-tip-popup sorry)
	)))


;;;###autoload
(defun liquid-tip-init (&optional mode)
  "Initialize liquid-tip by making all identifiers buttons using MODE."
  (interactive)
  (progn (if mode (setq liquid-tip-mode mode))
	 (button-lock-mode 1)
	 (button-lock-set-button liquid-id-regexp 'liquid-tip-show :mouse-face nil :face nil :face-policy nil :mouse-binding 'double-mouse-1)
	 ))

;;;###autoload
(defun liquid-tip-update (mode)
  "Update liquid-annot-table by reloading annot file for buffer in MODE."
  (interactive)
  (let* ((pos  (liquid-get-position))
	 (file (position-file pos)))
    (liquid-annot-set file mode)))


;; For simple, ascii popups, use:
;;    (liquid-tip-init 'ascii) 
;; For emacs', balloon based popups, use:
;;    (liquid-tip-init 'balloon)
;; or just
;;    (liquid-tip-init 'balloon)

;; Reload annotations after check
(add-hook 'flycheck-after-syntax-check-hook
	  (lambda () (liquid-tip-update 'flycheck)))



(provide 'liquid-tip)

;; Local Variables:
;; coding: utf-8
;; mode: emacs-lisp
;; End:

;;; liquid-tip.el ends here
