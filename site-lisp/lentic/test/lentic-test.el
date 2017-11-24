;;; lentic-test.el --- Tests

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>

;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2014, 2015, 2016, Phillip Lord, Newcastle University

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

;;; Code:

(require 'lentic)
(require 'lentic-latex-code)
(require 'lentic-asciidoc)
(require 'lentic-org)
(require 'lentic-rot13)
(require 'lentic-mode)
(require 'f)

(require 'load-relative)

(require 'assess)
(require 'assess-call)

(setq lentic-condition-case-disabled t)

(defvar lentic-test-dir
  (f-join
   (f-parent
    (f-dirname (__FILE__)))
   "dev-resources/")
  "Location of test files.")

;; (defvar lentic-test-dir
;;   (concat
;;    (file-name-directory
;;     (find-lisp-object-file-name 'lentic-init 'defvar))
;;    "dev-resources/"))

(defun lentic-test-file (filename)
  "Fetch the long name of the resource FILENAME."
  (let ((file
         (f-join lentic-test-dir filename)))
    (when (not (file-exists-p file))
      (error "Test File does not exist: %s" file))
    file))

(defun lentic-test-clone (file init)
  "Clone FILE with INIT and clean up all buffers after."
  (assess-with-preserved-buffer-list
   (lentic-batch-clone-with-config
    (lentic-test-file file) init)))

(defun lentic-test-clone-to-assess (init file cloned-file)
  (cons
   (assess-file
    (lentic-test-file cloned-file))
   (lentic-test-clone
    file init)))

(defun lentic-test-clone= (init file cloned-file)
  "With INIT function clone FILE and compare to CLONED-file."
  (let ((comp (lentic-test-clone-to-assess init file cloned-file)))
    (assess= (car comp) (cdr comp))))

(put 'lentic-test-clone= 'ert-explainer 'lentic-test-clone-explain=)

(defun lentic-test-clone-explain= (init file cloned-file)
  "With INIT function clone FILE and compare to CLONED-file."
  (let ((comp (lentic-test-clone-to-assess init file cloned-file)))
    (assess-explain= (car comp) (cdr comp))))

(ert-deftest lentic-conf ()
  "Test whether the default configuration does sensible things."
  (should
   (equal nil
          (oref
           (lentic-default-configuration "bob")
           :lentic-mode))))

(ert-deftest lentic-simple ()
  "Simple clone."
  (should
   (assess=
    "simple\n"
    (lentic-test-clone
     "simple-contents.txt"
     'lentic-default-init))))

(ert-deftest lentic-clojure-latex ()
  "Clojure to LaTeX transform."
  (should
   (lentic-test-clone=
    'lentic-clojure-latex-init
    "chunk-comment.clj"
    "chunk-comment-out.tex")))


(ert-deftest lentic-asciidoc-clojure ()
  (should
   (lentic-test-clone=
    'lentic-asciidoc-clojure-init
    "asciidoc-clj.txt" "asciidoc-clj-out.clj")))

;; org mode start up prints out "OVERVIEW" from the cycle. Can't see any way
;; to stop this
(ert-deftest lentic-org-el ()
  (should
   (lentic-test-clone=
    'lentic-org-el-init
    "org-el.org" "org-el.el")))

(ert-deftest lentic-org-el-with-tags ()
  "Tests whether on the begin_src elements disrupt lentic behaviour.

Addresses issue #32."
  (should
   (lentic-test-clone=
    'lentic-org-el-init
    "org-el-with-tags.org" "org-el-with-tags.el")))


(ert-deftest lentic-el-org ()
  (should
   (lentic-test-clone=
    'lentic-el-org-init
    "el-org.el" "el-org.org")))

(ert-deftest lentic-orgel-org()
  (should
   (lentic-test-clone=
    'lentic-orgel-org-init
    "orgel-org.el" "orgel-org.org")))

(ert-deftest lentic-org-orgel()
  (should
   (lentic-test-clone=
    'lentic-org-orgel-init
    "org-orgel.org" "org-orgel.el")))

(ert-deftest lentic-orgel-org-with-tags ()
  "Test that we can have tags on section headers.

Addresses issue #19."
  (should
   (lentic-test-clone=
    'lentic-orgel-org-init
    "orgel-org-with-tags.el" "orgel-org-with-tags.org")))

(ert-deftest lentic-orgel-org-with-inline-delimitor()
  "Test that stringed or otherwise not at the start of
line delimitors are not detected.

Addresses issue #36."
  (should
   (lentic-test-clone=
    'lentic-org-orgel-init
    "string-src-block.org"
    "string-src-block.el")))

(ert-deftest lentic-org-clojure ()
  (should
   (lentic-test-clone=
    'lentic-org-clojure-init
    "org-clojure.org" "org-clojure.clj"
    )))

(ert-deftest lentic-rot13 ()
  (should
   (lentic-test-clone=
    'lentic-rot13-init
    "abc.txt" "rot13-abc.txt")))

(ert-deftest three-way ()
  (should
   (assess-with-preserved-buffer-list
    (with-current-buffer
        (find-file-noselect
         (lentic-test-file "chunk-comment.clj"))
      (setq lentic-init
            '(lentic-clojure-latex-init
              lentic-default-init))
      (lentic-init-all-create)
      (and (get-buffer "chunk-comment.tex")
           (get-buffer "*lentic: chunk-comment.clj*"))))))

;; incremental testing
;; these test that buffers which are created and then changed are correct.
;; At the moment, this does not check that the changes are actually
;; incremental, cause that's harder.
(defun lentic-test-clone-and-change-with-config
  (filename init &optional f-this f-that retn-this)
  "Clone file and make changes to check incremental updates.
Using INIT clone FILE, then apply F in the buffer, and return the
results. If RETN-THIS is non-nil return the contents of this
buffer, else return that buffer."
  ;; most of this is the same as batch-clone..
  (let ((retn nil)
        (f-this
         (or f-this
             (lambda ())))
        (f-that
         (or f-that
             (lambda ()))))
    (assess-with-preserved-buffer-list
     (let (this that)
       (with-current-buffer
           (setq this
                 (find-file-noselect filename))
         (setq lentic-init (-list init))
         (progn
           (setq that
                 (car (lentic-init-all-create)))
           (funcall f-this)
           (with-current-buffer
               that
             (funcall f-that)
             (unless retn-this
               (setq retn
                     (buffer-substring-no-properties
                      (point-min)
                      (point-max))))
             (set-buffer-modified-p nil)))
         (when retn-this
           (setq retn
                 (buffer-substring-no-properties
                  (point-min)
                  (point-max))))
         (set-buffer-modified-p nil)
         retn)))))

(defun lentic-test-clone-and-change=
  (init file cloned-file
        &optional f-this f-that retn-that)
  (assess=
   (assess-file (lentic-test-file cloned-file))
   (lentic-test-clone-and-change-with-config
    (lentic-test-file file) init f-this f-that
    retn-that)))

(defun lentic-test-clone-and-change-explain=
  (init file cloned-file
        &optional f-this f-that retn-that)
  (assess-explain=
   (assess-file (lentic-test-file cloned-file))
   (lentic-test-clone-and-change-with-config
    (lentic-test-file file) init f-this f-that
    retn-that)))

(put 'lentic-test-clone-and-change= 'ert-explainer
     #'lentic-test-clone-and-change-explain=)

(defun capture-last-arg (sym-fn fn)
  (cdar
   (assess-call-capture sym-fn fn)))

(defun clone-with-preserve (file init fn)
  (assess-with-preserved-buffer-list
   (lentic-test-clone-and-change-with-config
    (lentic-test-file file)
    init fn)))

(defmacro with-capture-insertion (&rest body)
  `(capture-last-arg
    'lentic-insertion-string-transform
    (lambda ()
      ,@body)))

(ert-deftest lentic-simple-with-change ()
  (should
   (assess=
    "not simple"
    (with-capture-insertion
     (should
      (assess=
       (clone-with-preserve
        "simple-contents.txt"
        'lentic-default-init
        (lambda ()
          (goto-char (point-max))
          (insert "not simple")))
       "simple\nnot simple"))))))

(ert-deftest lentic-simple-with-change-file()
  "Test simple-contents with a change and compare to file.
This mostly checks my test machinary."
  (should
   (assess=
    "simple"
    (with-capture-insertion
     (should
      (lentic-test-clone-and-change=
       'lentic-default-init
       "simple-contents.txt" "simple-contents-chg.txt"
       (lambda ()
         (goto-char (point-max))
         (insert "simple"))))))))

(ert-deftest lentic-clojure-latex-incremental ()
  (should
   (assess=
    ";; inserted\n"
    (with-capture-insertion
     (should
      (lentic-test-clone-and-change=
       'lentic-clojure-latex-init
       "chunk-comment.clj" "chunk-comment-changed-out.tex"
       (lambda ()
         (forward-line 1)
         (insert ";; inserted\n")))))))

  (should
   (assess=
    ";; inserted\n"
    (with-capture-insertion
     (should
      (and
       (lentic-test-clone-and-change=
        'lentic-latex-clojure-init
        "chunk-comment.tex" "chunk-comment-changed-1.clj"
        (lambda ()
          (forward-line 1)
          (insert ";; inserted\n"))))))))

  (should
   (assess=
    "(form inserted)\n"
    (with-capture-insertion
     (lentic-test-clone-and-change=
      'lentic-latex-clojure-init
      "chunk-comment.tex" "chunk-comment-changed-2.clj"
      (lambda ()
        (search-forward "\\begin{code}\n")
        (insert "(form inserted)\n")))))))

(ert-deftest clojure-latex-first-line ()
  "Tests for a bug after introduction of incremental chunks."
  (should
   (lentic-test-clone-and-change=
    'lentic-clojure-latex-init
    "chunk-comment.clj" "chunk-comment.tex"
    (lambda ()
      (delete-char 1)
      (delete-char 1)
      (insert ";")
      (insert ";")))))

(ert-deftest clojure-latex-empty-line ()
  "Tests for a deletion of an empty line"
  (should
   (lentic-test-clone-and-change=
    'lentic-clojure-latex-init
    "chunk-comment.clj" "chunk-comment.tex"
    nil
    (lambda ()
      (goto-char (point-min))
      (forward-line 1)
      (delete-char 1)
      (insert "\n")))))

(ert-deftest orgel-org-incremental ()
  (should
   (lentic-test-clone-and-change=
    'lentic-orgel-org-init
    "orgel-org.el" "orgel-org.el"
    nil
    (lambda ()
      (show-all)
      (goto-char (point-min))
      (forward-line)
      (insert "a")
      (delete-char -1))
    t)))

;; Editing the header one lines causes problems
(ert-deftest orgel-org-incremental-on-header-one ()
  (should
   (lentic-test-clone-and-change=
    'lentic-orgel-org-init
    "orgel-org.el" "orgel-org.el"
    nil
    (lambda ()
      (show-all)
      (goto-char (point-max))
      ;; add a "a" just after the * character of the new line
      (search-backward " Commentary")
      (insert "a")
      ;; move to the beginning of the a
      (search-backward "a")
      ;; delete the "*" character
      (delete-char -1)
      ;; insert the * character and a space
      (insert "*")
      ;; remove the "a")
      (search-forward "a")
      (delete-char -1)
      ;; this should be a round trip but isn't!
      )
    t)))

;; ** delayed init

;; Probably time to deprecate this package now

;; (ert-deftest lentic-simple-delayed ()
;;   (should
;;    (equal
;;     (concat "x" abc-txt)
;;     (lentic-test-clone-and-change-with-config
;;      (lentic-test-file "abc.txt")
;;      'lentic-delayed-default-init
;;      (lambda ()
;;        (goto-char (point-min))
;;        (insert "x")
;;        ;; run timer by ourselves.
;;        (lentic-delayed-timer-function))))))

;; tests for lots of types of change and whether they break the incremental
;; updates.
(defvar abc-txt "aaa\nbbb\nccc\n")

(defun simple-change-that (f)
  "Do a single change and check that."
  (lentic-test-clone-and-change-with-config
     (lentic-test-file "abc.txt")
     'lentic-default-init  f
     nil nil))

(ert-deftest null-operation ()
  (should
   (assess=
    abc-txt
    (simple-change-that nil))))

(ert-deftest single-insertion ()
  (should
   (assess=
    (concat "x" abc-txt)
    (simple-change-that
     (lambda ()
       (goto-char (point-min))
       (insert "x"))))))

(ert-deftest single-delete ()
  (should
   (assess=
    (substring abc-txt 1)
    (simple-change-that
     (lambda ()
       (goto-char (point-min))
       (delete-char 1))))))

(ert-deftest line-delete ()
  (should
   (assess=
    (substring abc-txt 3)
    (simple-change-that
     (lambda ()
       (goto-char (point-min))
       (kill-line))))))

(ert-deftest erase-buffer ()
  (should
   (assess=
    ""
    (simple-change-that
     (lambda ()
       (erase-buffer))))))

(provide 'lentic-test)
