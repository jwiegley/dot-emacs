;;; shorten.el --- component-wise string shortener

;; Copyright (C) 2013  John J Foerch <jjfoerch@earthlink.net>

;; Keywords: extensions
;; Author: John J Foerch <jjfoerch@earthlink.net>
;; URL: https://github.com/jorgenschaefer/circe/blob/master/shorten.el

;; This program is free software: you can redistribute it and/or modify
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

;; This is a component-wise string shortener, meaning that, given a list
;; of strings, it breaks each string into parts, then computes shortest
;; prefix of each part with respect to others of the same 'depth', such
;; that when joined back together, the shortened form of the whole string
;; remains unique within the resulting list.  Many styles of shortening
;; are made possible via three functions that the caller may provide: the
;; split function, the join function, and the validate-component function.
;;
;; Strings are broken with the value of `shorten-split-function' (a
;; procedure string->list), and shortened components are rejoined with the
;; value of `shorten-join-function' (a procedure list->string[*]).  The
;; default split and join functions break the string on word boundaries,
;; and rejoin on the empty string.  Potential shortened forms of
;; components are tested with `shorten-validate-component-function'; its
;; default value passes only if its argument contains at least one
;; word-constituent character (regexp \w), meaning that by default,
;; components consisting entirely of non-word characters will not be
;; shortened, and components that start with non-word characters will only
;; be shortened so much that they have at least one word-constituent
;; character in them.
;;
;; The main entry point is `shorten-strings', which takes a list of strings
;; as its argument and returns an alist ((STRING . SHORTENED-STRING) ...).
;;
;; [*] Also takes a second argument; see docstring of
;; `shorten-join-function'.

;;; History:

;; - Version 0.1 (March 7, 2013): initial release

;;; Code:

;; Tree utils
;;
(defsubst shorten-make-tree-root ()
  (cons nil nil))

(defsubst shorten-tree-make-entry (token short full)
  (list token short full nil))

(defsubst shorten-tree-token (entry)
  (car entry))

(defsubst shorten-tree-fullname (entry)
  (nth 2 entry))

(defsubst shorten-tree-descendants (entry)
  (nthcdr 3 entry))

(defsubst shorten-tree-set-shortened (entry short)
  (setcar (cdr entry) short))

(defsubst shorten-tree-set-fullname (entry full)
  (setcar (nthcdr 2 entry) full))

(defsubst shorten-tree-insert (node item)
  (when (car node)
    (setcdr node (cons (car node) (cdr node))))
  (setcar node item))


;; Caller configuration
;;
(defun shorten-split (s)
  (split-string s "\\b" t))

(defun shorten-join (lst &optional tail-count)
  (mapconcat #'identity lst ""))

(defun shorten-join-sans-tail (lst tail-count)
  "A shorten-join that drops unnecessary tail components."
  (shorten-join (butlast lst tail-count)))

(defun shorten-validate-component (str)
  (string-match-p "\\w" str))

(defvar shorten-split-function #'shorten-split
  "Value should be a function of string->list that breaks a
string into components.  The default breaks on word-boundaries.
To get simple prefix shortening, bind this to `list'.

Users should not generally change the global value of this
variable; instead, bind it dynamically around calls to
`shorten-strings'.")

(defvar shorten-join-function #'shorten-join
  "A function that takes a list of components and a tail-count,
and returns a joined string.  Tail-count is the number of
components on the end of the list that are not needed to uniquify
the result, and so may be safely dropped if aggressive shortening
is desired.  The default preserves tail components, and joins the
list on the empty string.

Users should not generally change the global value of this
variable; instead, bind it dynamically around calls to
`shorten-strings'.")

(defvar shorten-validate-component-function #'shorten-validate-component
  "Predicate that returns t if a proposed shortened form of a
single component is acceptable, nil if a longer one should be
tried.  The default validates only when the candidate contains at
least one word-constituent character, thus strings consisting of
punctuation will not be shortened.  For aggressive shortening,
bind to a procedure that always returns t.

Users should not generally change the global value of this
variable; instead, bind it dynamically around calls to
`shorten-strings'.")


;; Main procedures
;;
(defun shorten-one (str others)
  "Return shortest unique prefix of STR among OTHERS, or STR if
it cannot be shortened.  If STR is a member of OTHERS (tested
with `eq') that entry is ignored.  The value of
`shorten-validate-component-function' will be used to validate
any prefix."
  (let ((max (length str))
        (len 1))
    (or (catch 'return
          (while (< len max)
            (let ((prefix (substring str 0 len)))
              (when (funcall shorten-validate-component-function prefix)
                (when (catch 'return
                        (dolist (other others t)
                          (when (and (>= (length other) len)
                                     (string= (substring other 0 len) prefix)
                                     (not (eq other str)))
                            (throw 'return nil))))
                  (throw 'return prefix)))
              (setq len (1+ len)))))
        str)))

(defun shorten-walk-internal (node path tail-count result-out)
  (let ((others (mapcar #'car node)))
    (setq tail-count (if (cdr node) 0 (1+ tail-count)))
    (dolist (entry node)
      (let* ((token (shorten-tree-token entry))
             (shortened (shorten-one token others))
             (path (cons shortened path))
             (fullname (shorten-tree-fullname entry))
             (descendants (shorten-tree-descendants entry))
             (have-descendants (not (equal '(nil) descendants))))
        (shorten-tree-set-shortened entry shortened)
        ;; if this entry has a fullname, add to result-out
        (when fullname
          (let ((joined (funcall shorten-join-function
                                 (reverse path)
                                 (if have-descendants 0 tail-count))))
            (shorten-tree-insert result-out (cons fullname joined))))
        ;; if this entry has descendants, recurse
        (when have-descendants
          (shorten-walk-internal descendants path
                                 (if fullname -1 tail-count)
                                 result-out))))))

(defun shorten-walk (tree)
  "Takes a tree of the type made by `shorten-make-tree' and
returns an alist ((STRING . SHORTENED-STRING) ...).  Uses
`shorten-join-function' to join shortened components back
together into SHORTENED-STRING.  See also
`shorten-validate-component-function'."
  (let ((result-out (shorten-make-tree-root)))
    (shorten-walk-internal tree '() -1 result-out)
    (if (equal '(nil) result-out) nil result-out)))

(defun shorten-make-tree (strings)
  "Takes a list of strings and returns a tree of the type used by
`shorten-walk' to generate shortened strings.  Uses
`shorten-split-function' to split the strings."
  (let ((tree (shorten-make-tree-root)))
    (dolist (s strings)
      (let ((node tree)
            (tokens (funcall shorten-split-function s))
            (entry nil))
        ;; create a path in tree for tokens
        (dolist (token tokens)
          (setq entry (assoc token node))
          (when (not entry)
            (setq entry (shorten-tree-make-entry token nil nil))
            (shorten-tree-insert node entry))
          (setq node (shorten-tree-descendants entry)))
        ;; for the last token, set 'fullname'
        (shorten-tree-set-fullname entry s)))
    (if (equal tree '(nil)) nil tree)))

;;;###autoload
(defun shorten-strings (strings)
  "Takes a list of strings and returns an alist ((STRING
. SHORTENED-STRING) ...).  Uses `shorten-split-function' to split
the strings, and `shorten-join-function' to join shortened
components back together into SHORTENED-STRING.  See also
`shorten-validate-component-function'."
  (shorten-walk (shorten-make-tree strings)))


(provide 'shorten)
;;; shorten.el ends here
