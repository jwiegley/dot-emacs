;;; esxpath.el --- testing phase -*- lexical-binding: t -*-

;; Copyright (C) 2013  Evan Izaksonas-Smith

;; Author: Evan Izaksonas-Smith <tali713@rastafy>
;; Keywords: extensions, lisp

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

;;

;;; Code:
(require 'esxml)


;;probable call

(defmacro esxpath-transform (pathspec)
  (pcase pathspec
    (`(,(and keyword) (pred keywordp) . ,_)
     (error "Keyword %s unhandled" keyword))
    (`(,(and root (pred symbolp)) ,(and body (pred symbolp)))
     `(if (eq ',root (car ,body)) (nthcdr 2 ,body)))
    (`(,(and node (pred symbolp)) ,(and body (pred consp)))
     `(remove-if-not (apply-partially 'esxpath-tag-p ',node)
                     (esxpath-transform ,body)))
    (_ pathspec)))

(pp (macroexpand '(esxpath-transform (title (book (bookstore test-sheet))))))
(remove-if-not
 (apply-partially 'esxpath-tag-p 'title)
 (remove-if-not
  (apply-partially 'esxpath-tag-p 'book)
  (if
    (eq 'bookstore
        (car test-sheet))
      (list test-sheet))))



;; (defun esxpath-child-p (child-node parent-node)
;;   (find child-node (esxpath-get-children parent-node)))

;; (defun esxpath-descendent-p (descendent-node ancestor-node)
;;   (or (esxpath-child-p descendent-node ancestor-node)
;;       (let ((children (esxpath-get-children ancestor-node)))
;;         (if children (every (apply-partially 'esxpath-descendent-p descendent-node)
;;                             children)))))



(defun esxpath-fill-missing-attributes (pathspec)
  (pcase pathspec
    (`(,key
       ,arg
       ,(and pathspec (pred consp)))
     `(,key ,arg ,(esxpath-fill-missing-attributes pathspec)))

    (`(,(and key (pred keywordp))
       ,(and pathspec (pred consp)))
     `(,key ,(esxpath-fill-missing-attributes pathspec)))

    (`(,key
       ,(and pathspec (pred consp)))
     `(,key () ,(esxpath-fill-missing-attributes pathspec)))

    (`(,key)
     `(,key ()))

    (_ pathspec)))

(defun esxpath-transform (pathspec)
  `(lambda (esxml)
     ,(pcase-recur `(,(car (last pathspec))
                     (esxpath-select-root ',(first pathspec) esxml))
        ;; (`((:has-child ,pathspec) ,form) (esxpath-select-with-child ))
        (`((,(and tag (pred symbolp))
            ,(and attrs (pred attrsp))
            ,pathspec)
           ,form)
         (:recur pathspec `(esxpath-select-from-children ',tag ',attrs ,form)))
        (`((,(and tag (pred symbolp))
            ,(and attrs (pred attrsp)))
           ,form)
         `(esxpath-select-from-children ',tag ',attrs ,form))
        (`(,pathspec ,form) `((pathspec ,pathspec) (form ,form))))))

(defmacro esxpath (pathspec)
  (esxpath-transform (esxpath-fill-missing-attributes pathspec)))



(pp (macroexpand '(esxpath (bookstore (book)))))
(pp (esxpath-transform
     (esxpath-fill-missing-attributes
      '(bookstore (book (title ((price . "1.00"))))))
     ))



(funcall (esxpath (bookstore (book)))
         test-sheet)

;; ABOVE HERE DISCARD




(defvar test-sheet
  (sxml-to-esxml '(bookstore
                   (book
                    (title (@ (lang "eng")) "Harry Potter")
                    (price  "29.99"))
                   (book
                    (title (@ (lang "eng")) "Learning XML")
                    (price  "39.95")))))

(defmacro plambda (&rest pcases)
  (declare (indent defun))
  (let ((args (gensym "args")))
    `(lambda (,args)
       (pcase ,args ,@pcases))))

(defun esxpath-tag-p (tag esxml)
  (and (consp esxml)
       (eq tag (car esxml))))

(defvar test-sheet2
  '(tag ((attr1 . "foo")
         (attr2 . "bar")
         (attr3 . "3"))))

(defun esxpath-attrs-match (test-attrs esxml)
  (pcase-let ((`(,_ ,attrs . ,_) esxml))
    (every (plambda
             (`(,key . ,(pred stringp)) (equal (assoc-default key test-attrs)
                                               (assoc-default key attrs)))
             (`(,key . (,op ,n)) (funcall op
                                          (string-to-number (assoc-default key attrs))
                                          n))
             (x (error "Unhandled attr: %s" x)))
           test-attrs)))

(defun esxpath-match (tag test-attrs esxml)
  (and (if tag (esxpath-tag-p tag esxml) t)
       (if test-attrs (esxpath-attrs-match test-attrs esxml) t)))


(defun on-nodeset (function)
  (lambda (node-set)
    (apply 'append (mapcar function node-set))))

(defun esxpath-select-root (root attrs esxml)
  "Returns the root node as a node-set if it matches ROOT.
ROOT is a symbol, the tag of the root node."
  (if (esxpath-match root attrs esxml)
      (list esxml)))

(ert-deftest esxpath-select-root ()
  "testing select-root"
  (should (equal (esxpath-select-root nil nil test-sheet)
                 '((bookstore nil
                              (book nil
                                    (title
                                     ((lang . "eng"))
                                     "Harry Potter")
                                    (price nil "29.99"))
                              (book nil
                                    (title
                                     ((lang . "eng"))
                                     "Learning XML")
                                    (price nil "39.95"))))))
  (should (equal (esxpath-select-root 'bookstore nil test-sheet)
                 '((bookstore nil
                              (book nil
                                    (title
                                     ((lang . "eng"))
                                     "Harry Potter")
                                    (price nil "29.99"))
                              (book nil
                                    (title
                                     ((lang . "eng"))
                                     "Learning XML")
                                    (price nil "39.95"))))))
  (should (equal (esxpath-select-root 'foo nil test-sheet)
                 nil)))

(defun esxpath-select (tag attrs node-set)
  (remove-if-not (apply-partially 'esxpath-match tag attrs) node-set))

(defun esxpath-get-children (esxml)
  (pcase esxml (`(,_ ,_ . ,body) body)))

(defalias 'esxpath-select-children (on-nodeset 'esxpath-get-children))

(defun esxpath-select-from-children (tag attrs node-set)
  (esxpath-select tag attrs (esxpath-select-children node-set)))

(ert-deftest esxpath-select-from-children ()
  (should (equal (esxpath-select-from-children 'book nil
                                               (esxpath-select-root nil nil test-sheet))
                 '((book nil
                         (title
                          ((lang . "eng"))
                          "Harry Potter")
                         (price nil "29.99"))
                   (book nil
                         (title
                          ((lang . "eng"))
                          "Learning XML")
                         (price nil "39.95")))))
  (should (equal (esxpath-select-from-children nil '((lang . "eng"))
                                               (esxpath-select-from-children
                                                'book nil
                                                (esxpath-select-root nil nil test-sheet)))
                 '((title
                    ((lang . "eng"))
                    "Harry Potter")
                   (title
                    ((lang . "eng"))
                    "Learning XML")))))

(defun esxpath-has-child (pred node)
  (and (member-if pred (esxpath-get-children node))
       node))


(esxpath-has-child (apply-partially 'esxpath-match 'book nil)
                   test-sheet)

(defun esxpath-select-with-child (pred)
  (lambda (node-set)
    (remove-if-not (apply-partially 'esxpath-has-child pred)
                   node-set)))

(provide 'esxpath)
;;; esxpath.el ends here
