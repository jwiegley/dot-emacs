(require 'lentic)
(require 'lentic-latex-code)
(require 'lentic-asciidoc)
(require 'lentic-org)
(require 'lentic-rot13)
(require 'lentic-mode)
(require 'f)

(require 'load-relative)

(setq lentic-condition-case-disabled t)

(defvar lentic-test-dir
  (f-join
   (f-parent
    (f-dirname (__FILE__)))
   "dev-resources/"))

;; (defvar lentic-test-dir
;;   (concat
;;    (file-name-directory
;;     (find-lisp-object-file-name 'lentic-init 'defvar))
;;    "dev-resources/"))

(defun lentic-test-file (filename)
  (let ((file
         (f-join lentic-test-dir filename)))
    (when (not (file-exists-p file))
      (error "Test File does not exist: %s" file))
    file))

(defvar lentic-test-quiet nil)

(defun lentic-test-equal-loudly (a b)
  "Actually, this just tests equality and shouts if not."
  ;; change this to t to disable noisy printout
  (if lentic-test-quiet
      (string= a b)
    (if (string= a b)
        t
      (message "Results:\n%s\n:Complete\nShouldbe:\n%s\nComplete:" cloned-results cloned-file)
      (let* ((a-buffer
              (generate-new-buffer "a"))
             (b-buffer
              (generate-new-buffer "b"))
             (a-file
              (make-temp-file
               (buffer-name a-buffer)))
             (b-file
              (make-temp-file
               (buffer-name b-buffer))))
        (with-current-buffer
            a-buffer
          (insert a)
          (write-file a-file))
        (with-current-buffer
            b-buffer
          (insert b)
          (write-file b-file))
        (message "diff:%senddiff:"
                 (with-temp-buffer
                   (call-process
                    "diff"
                    nil
                    (current-buffer)
                    nil
                    "-c"
                    a-file
                    b-file)
                   (buffer-string))))
      nil)))

(defun lentic-test-clone-with-cleanup (file init)
  (unwind-protect
      (lentic-batch-clone-with-config (lentic-test-file file) init)
    (let ((this (get-file-buffer (lentic-test-file file)))
          ;; keep everything!
          (lentic-kill-retain t))
      (when this
        (with-current-buffer this
          (let ((that (lentic-that (car lentic-config)))
                (kill-buffer-query-functions nil))
            (with-current-buffer that
              (set-buffer-modified-p nil)
              (kill-buffer that))))
        (let ((kill-buffer-query-functions nil))
          (set-buffer-modified-p nil)
          (kill-buffer this))))))

(defun lentic-test-clone-equal (init file cloned-file)
  (let ((cloned-file
         (f-read
          (lentic-test-file cloned-file)))
        (cloned-results
         (lentic-test-clone-with-cleanup
          file init)))
    (lentic-test-equal-loudly cloned-file cloned-results)))

(defun lentic-test-clone-equal-generate
  (init file cloned-file)
  "Generates the test file for `lentic-batch-clone-equal'."
  (f-write
   (lentic-test-clone-with-cleanup
    (lentic-test-file file) init)
   o'utf-8
   (concat lentic-test-dir cloned-file))
  ;; return nil, so if we use this in a test by mistake, it will crash out.
  nil)

(ert-deftest lentic-conf ()
  (should
   (equal nil
          (oref
           (lentic-default-configuration "bob")
           :lentic-mode))))

(ert-deftest lentic-simple ()
  (should
   (equal "simple\n"
          (lentic-test-clone-with-cleanup
           "simple-contents.txt"
           'lentic-default-init))))

(ert-deftest lentic-clojure-latex ()
  (should
   (lentic-test-clone-equal
    'lentic-clojure-latex-init
    "chunk-comment.clj"
    "chunk-comment-out.tex")))


(ert-deftest lentic-asciidoc-clojure ()
  (should
   (lentic-test-clone-equal
    'lentic-asciidoc-clojure-init
    "asciidoc-clj.txt" "asciidoc-clj-out.clj")))

;; org mode start up prints out "OVERVIEW" from the cycle. Can't see any way
;; to stop this
(ert-deftest lentic-org-el ()
  (should
   (lentic-test-clone-equal
    'lentic-org-el-init
    "org-el.org" "org-el.el")))

(ert-deftest lentic-org-el-with-tags ()
  "Tests whether on the begin_src elements disrupt lentic behaviour.

Addresses issue #32."
  (should
   (lentic-test-clone-equal
    'lentic-org-el-init
    "org-el-with-tags.org" "org-el-with-tags.el")))


(ert-deftest lentic-el-org ()
  (should
   (lentic-test-clone-equal
    'lentic-el-org-init
    "el-org.el" "el-org.org")))

(ert-deftest lentic-orgel-org()
  (should
   (lentic-test-clone-equal
    'lentic-orgel-org-init
    "orgel-org.el" "orgel-org.org")))

(ert-deftest lentic-org-orgel()
  (should
   (lentic-test-clone-equal
    'lentic-org-orgel-init
    "org-orgel.org" "org-orgel.el")))

(ert-deftest lentic-orgel-org-with-tags ()
  "Test that we can have tags on section headers.

Addresses issue #19."
  (should
   (lentic-test-clone-equal
    'lentic-orgel-org-init
    "orgel-org-with-tags.el" "orgel-org-with-tags.org")))

(ert-deftest lentic-orgel-org-with-inline-delimitor()
  "Test that stringed or otherwise not at the start of
line delimitors are not detected.

Addresses issue #36."
  (should
   (lentic-test-clone-equal
    'lentic-org-orgel-init
    "string-src-block.org"
    "string-src-block.el")))


(ert-deftest lentic-org-clojure ()
  (should
   (lentic-test-clone-equal
    'lentic-org-clojure-init
    "org-clojure.org" "org-clojure.clj"
    )))

(ert-deftest lentic-rot13 ()
  (should
   (lentic-test-clone-equal
    'lentic-rot13-init
    "abc.txt" "rot13-abc.txt")))

(ert-deftest three-way ()
  (should
   (with-current-buffer
       (find-file-noselect
        (lentic-test-file "chunk-comment.clj"))
     (setq lentic-init
           '(lentic-clojure-latex-init
             lentic-default-init))
     (lentic-init-all-create)
     (let ((tex
            (get-buffer "chunk-comment.tex"))
           (clj
            (get-buffer "*lentic: chunk-comment.clj*")))
       (kill-buffer tex)
       (kill-buffer clj)
       (and clj tex)))))



;; incremental testing
;; these test that buffers which are created and then changed are correct.
;; At the moment, this does not check that the changes are actually
;; incremental, cause that's harder.
(defun lentic-test-clone-and-change-with-config
  (filename init &optional f-this f-that retn-this)
  "Clone file and make changes to check incremental updates.
Using INIT clone FILE, then apply F in the buffer, and return the
results."
  ;; most of this is the same as batch-clone..
  (let ((retn nil)
        (f-this
         (or f-this
             (lambda ())))
        (f-that
         (or f-that
             (lambda ()))))
    (let (this that)
      (unwind-protect
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
            retn)

        ;; unwind forms
        (when this (kill-buffer this))
        (when that (kill-buffer that))))))

(defun lentic-test-clone-and-change-equal
  (init file cloned-file
        &optional f-this f-that retn-that)
  (let ((cloned-file
         (f-read
          (lentic-test-file cloned-file)))
        (cloned-results
         (lentic-test-clone-and-change-with-config
          (lentic-test-file file) init f-this f-that
          retn-that)))
    (if
        (string= cloned-file cloned-results)
        t
      ;; comment this out if you don't want it.
      (lentic-test-equal-loudly cloned-file cloned-results)
      nil)))

(defun lentic-test-clone-and-change-equal-generate
  (init file cloned-file f)
  "Generates the test file for `lentic-test-clone-and-change-with-config'."
  (f-write
   (lentic-test-clone-and-change-with-config
    (lentic-test-file file) init
    f)
   'utf-8
   (concat lentic-test-dir  cloned-file))
  ;; return nil, so that if we use this in a test by mistake, it returns
  ;; false, so there is a good chance it will fail the test.
  nil)

(defvar lentic-test-last-transform "")

(defadvice lentic-insertion-string-transform
  (before store-transform
         (string)
         activate)
  (setq lentic-test-last-transform string))

(ert-deftest lentic-simple-with-change ()
  "Test simple-contents with a change, mostly to check my test machinary."
  (should
   (and
    (equal "simple\nnot simple"
           (lentic-test-clone-and-change-with-config
            (lentic-test-file "simple-contents.txt")
            'lentic-default-init
            (lambda ()
              (goto-char (point-max))
              (insert "not simple"))))
    (equal lentic-test-last-transform "not simple"))))

(ert-deftest lentic-simple-with-change-file()
  "Test simple-contents with a change and compare to file.
This mostly checks my test machinary."
  (should
   (and
    (lentic-test-clone-and-change-equal
     'lentic-default-init
     "simple-contents.txt" "simple-contents-chg.txt"
     (lambda ()
       (goto-char (point-max))
       (insert "simple")))
    (equal lentic-test-last-transform "simple"))))

(ert-deftest lentic-clojure-latex-incremental ()
  (should
   (and
    (lentic-test-clone-and-change-equal
     'lentic-clojure-latex-init
     "chunk-comment.clj" "chunk-comment-changed-out.tex"
     (lambda ()
       (forward-line 1)
       (insert ";; inserted\n")))
    (equal lentic-test-last-transform ";; inserted\n")))

  (should
   (and
    (lentic-test-clone-and-change-equal
     'lentic-latex-clojure-init
     "chunk-comment.tex" "chunk-comment-changed-1.clj"
     (lambda ()
       (forward-line 1)
       (insert ";; inserted\n")))
    (equal lentic-test-last-transform ";; inserted\n")))

  (should
   (and
    (lentic-test-clone-and-change-equal
     'lentic-latex-clojure-init
     "chunk-comment.tex" "chunk-comment-changed-2.clj"
     (lambda ()
       (search-forward "\\begin{code}\n")
       (insert "(form inserted)\n")))
    (equal lentic-test-last-transform "(form inserted)\n"))))

(ert-deftest clojure-latex-first-line ()
  "Tests for a bug after introduction of incremental chunks."
  (should
   (lentic-test-clone-and-change-equal
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
   (lentic-test-clone-and-change-equal
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
   (lentic-test-clone-and-change-equal
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
   (lentic-test-clone-and-change-equal
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
   (equal
    abc-txt
    (simple-change-that nil))))

(ert-deftest single-insertion ()
  (should
   (equal
    (concat "x" abc-txt)
    (simple-change-that
     (lambda ()
       (goto-char (point-min))
       (insert "x"))))))

(ert-deftest single-delete ()
  (should
   (equal
    (substring abc-txt 1)
    (simple-change-that
     (lambda ()
       (goto-char (point-min))
       (delete-char 1))))))

(ert-deftest line-delete ()
  (should
   (equal
    (substring abc-txt 3)
    (simple-change-that
     (lambda ()
       (goto-char (point-min))
       (kill-line))))))

(ert-deftest erase-buffer ()
  (should
   (equal
    ""
    (simple-change-that
     (lambda ()
       (erase-buffer))))))
