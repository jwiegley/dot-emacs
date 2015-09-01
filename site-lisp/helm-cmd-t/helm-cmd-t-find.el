;;; helm-cmd-t-find.el --- Elisp only project based file searching

;; this file is not part of Emacs

;; Copyright (C) 2012 Le Wang
;; Author: Le Wang
;; Maintainer: Le Wang
;; Description:Elisp only project based file searching
;; Author: Le Wang
;; Maintainer: Le Wang

;; Created: Sat Jun 30 22:22:28 2012 (+0800)
;; Version: 0.1
;; Last-Updated:
;;           By:
;;     Update #: 15
;; URL:
;; Keywords:
;; Compatibility:

;;; Installation:

;; This is a fairly optimized way to get a recursive file listing without
;; shelling out.  Although native implementations of `find', etc, will always
;; be faster.

;;; Commentary:

;;
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


(provide 'helm-cmd-t-find)

(defun helm-cmd-t-split-string (string &optional separators)
  "like `split-string' but keep separators in array returned "
  (let ((rexp separators)
        (start 0)
        notfirst
        (list nil))
    (while (and (string-match rexp string
                              (if (and notfirst
                                       (< start (length string))
                                       (= start (match-beginning 0)))
                                  (1+ start) start))
                (< start (length string)))
      (push (substring string start (match-beginning 0)) list)
      (push (match-string-no-properties 0 string) list)
      (setq notfirst t)
      (setq start (match-end 0)))
    (setq list
          (cons (substring string start)
                list))
    (nreverse (delete "" list))))

(defun helm-cmd-t-glob-to-regex (glob)
  "convert glob to regexp.  Only \"*\" and \"?\" are understood.
"
  (concat "\\`"
          (mapconcat
           (lambda (part)
             (cond ((equal "*" part)
                    ".*")
                   ((equal "?" part)
                    ".")
                   (t
                    (regexp-quote part))))
           (helm-cmd-t-split-string glob "[*?]")
           "")
          "\\'"))

(defun helm-cmd-t-dumb-glob-to-regexp (globs)
  "roughly convert globs to regexp using regexps NOT a parser.

\"*\" in prefix/suffix/NEITHER location are considered in that
order, first one wins.

`regexp-opt' optimization is done for the first two cases.

i.e. \"*\" appears once in each glob"
  (let (prefix-star
        suffix-star
        other-star
        regex)
    (dolist (glob-pattern globs)
      (cond ((equal (aref glob-pattern 0) ?*)
             (push (substring glob-pattern 1) suffix-star))
            ((equal (aref glob-pattern (1- (length glob-pattern))) ?*)
             (push (substring glob-pattern 0 (1- (length glob-pattern))) prefix-star))
            (t
             (push glob-pattern other-star))
            ))
    (when prefix-star
      (setq regex (concat "\\`"
                          (regexp-opt prefix-star))))
    (when suffix-star
      (when regex
        (setq regex (concat regex "\\|")))
      (setq regex (concat regex
                          (regexp-opt suffix-star)
                          "\\'")))
    (when other-star
      (when regex
        (setq regex (concat regex "\\|")))
      (setq regex (concat regex
                          (mapconcat
                           (lambda (glob)
                             (helm-cmd-t-glob-to-regex glob))
                           other-star
                           "\\|"))))
    regex))

(defun helm-cmd-t-insert-tree-1 (directory reject-regexp)
  (setq directory (or directory ""))
  (unless (string-match reject-regexp directory)
    (let (subdirs)
      (dolist (file (directory-files directory))
        (let ((rel-file (concat (if (zerop (length directory))
                                    ""
                                  (file-name-as-directory directory))
                                file)))
          (unless (string-match reject-regexp file)
            (if (file-directory-p rel-file)
                (push rel-file subdirs)
              (insert rel-file "\n")))))
      (dolist (dir subdirs)
        (helm-cmd-t-insert-tree-1 dir reject-regexp)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; helm-cmd-t-find.el ends here

