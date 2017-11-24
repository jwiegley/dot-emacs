;;; lentic-org.el --- org support for lentic -*- lexical-binding: t -*-

;;; Header:

;; This file is not part of Emacs

;; Author: Phillip Lord <phillip.lord@russet.org.uk>
;; Maintainer: Phillip Lord <phillip.lord@russet.org.uk>

;; The contents of this file are subject to the GPL License, Version 3.0.

;; Copyright (C) 2014,2015,2016 Phillip Lord, Newcastle University

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

;; This file provides lentic for org and emacs-lisp files. This enables a
;; literate form of programming with Elisp, using org mode to provide
;; documentation mark up.

;; It provides too main ways of integrating between org and emacs-lisp. The
;; first which we call org-el (or el-org) is a relatively simple translation
;; between the two modes.

;; #+BEGIN_SRC emacs-lisp
(require 'cl-lib)
(require 'rx)
(require 'lentic-chunk)
(require 'm-buffer-at)
;; #+END_SRC


;;; Code:

;; ** Simple org->el

;; The simple transformation between org and elisp is to just comment out
;; everything that is not inside a BEGIN_SRC/END_SRC chunk. This provides only
;; minimal advantages over the embedded org mode environment. Org, for instance,
;; allows native fontification of the embedded code (i.e. elisp will be coloured
;; like elisp!), which is something that org-el translation also gives for free;
;; in this case of org-el, however, when the code is high-lighted, the org mode
;; text is visually reduced to `comment-face'. The other key advantage is
;; familiarity; it is possible to switch to the `emacs-lisp-mode' buffer and
;; eval-buffer, region or expression using all the standard keypresses.

;; One problem with this mode is that elisp has a first line semantics for
;; file-local variables. This is a particular issue if setting `lexical-binding'.
;; In a literate org file, this might appear on the first line of the
;; embedded lisp, but it will *not* appear in first line of an emacs-lisp
;; lentic, so the file will be interpreted with dynamic binding.


;; *** Implementation

;; The implementation is a straight-forward use of `lentic-chunk' with
;; regexps for org source chunks. It currently takes no account of
;; org-mode :tangle directives -- so all lisp in the buffer will be present in
;; the emacs-lisp mode lentic.

;; #+BEGIN_SRC emacs-lisp
(defun lentic-org-oset (conf)
  (lentic-m-oset
   conf
   :this-buffer (current-buffer)
   :comment ";; "
   :comment-stop "#\\\+BEGIN_SRC emacs-lisp.*"
   :comment-start "#\\\+END_SRC"))

;;;###autoload
(defun lentic-org-el-init ()
  (lentic-org-oset
   (lentic-unmatched-uncommented-chunk-configuration
    "lb-org-to-el"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name))
     ".el"))))

(add-to-list 'lentic-init-functions
             'lentic-org-el-init)

;;;###autoload
(defun lentic-el-org-init ()
  (lentic-org-oset
   (lentic-unmatched-commented-chunk-configuration
    "lb-el-to-org"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name))
     ".org"))))

(add-to-list 'lentic-init-functions
             'lentic-el-org-init)
;; #+END_SRC


;; ** orgel->org

;; In this section, we define a different transformation from what we call an
;; orgel file. This is a completely valid emacs-lisp file which transforms
;; cleanly into a valid org file. This requires constraits on both the emacs-lisp
;; and org representation. However, most of the features of both modes are
;; available.

;; The advantages of orgel files over a tangle-able literate org file are
;; several. The main one, however, is that the =.el= file remains a source
;; format. It can be loaded directly by Emacs with `load-library' or `require'.
;; Developers downloading from a VCS will find the =.el= file rather than looking
;; for an =.org= file. Developers wishing to offer patches can do so to the =.el=
;; file. Finally, tools which work over =.el= such as checkdoc will still work.
;; Finally, there is no disjoint between the org file and the emacs-lisp
;; comments. The commentary section, for example, can be edited using `org-mode'
;; rather than as comments in an elisp code chunk.

;; The disadvantages are that the structure of the org file is not arbitrary; it
;; most follow a specific structure. Without an untangling process, things like
;; noweb references will not work.

;; The transformation (orgel -> org) works as follows:
;;  - the first line summary is transformed into a comment in org
;;  - all single word ";;;" headers are transformed into level 1 org headings.
;;  - ";;" comments are removed except inside emacs-lisp source chunks.

;; *** Converting an Existing file

;; It is relatively simple to convert an existing emacs-lisp file, so that it
;; will work with the orgel transformation. orgel files work with (nearly) all
;; existing Emacs-Lisp documentaton standards but have a few extra bits added
;; in to work with org.

;; Current ";;;" section demarcation headers in emacs-lisp are used directly
;; and are transformed into Section 1 headings in org-mode. Unfortunately, in
;; emacs-lisp the header is *not* explicitly marked -- it's just the start
;; to the ";;; Commentary:" header. To enable folding of the header,
;; therefore, you need to introduce a ";;; Header:" line *after* the first line.
;; You may also wish to add a ";;; Footer:" heading as well.

;; Secondly, mark *all* of the code with org-mode source demarks. Finally, set
;; `lentic-init' to `lentic-orgel-org-init' (normally with a
;; file-local or dir-local variable). Now lentic can be started. The
;; header will appear as normal text in the org-mode buffer, with all other
;; comments inside a source chunk. You can now move through the buffer splitting
;; the source chunk (with `org-babel-demarcate-block' which has to win a prize
;; for the most obscurely named command), and move comments out of the source
;; chunk into the newly created text chunk.

;; *** Limitations

;; Currently, the implementation still requires some extra effort from the elisp
;; side, in that lisp must be marked up as a source code block. The short term
;; fix would be to add some functionality like `org-babel-demarcate-block' to
;; emacs-lisp-mode. Even better would to automatically add source markup when "("
;; was pressed at top level (if paredit were active, then it would also be
;; obvious where to put the close). Finally, have both `lentic-org' and
;; `org-mode' just recognise emacs-lisp as a source entity *without* any further
;; markup.

;; Finally, I don't like the treatment of the summary line -- ideally this should
;; appear somewhere in the org file not as a comment. I am constrained by the
;; start of file semantics of both =.org= and =.el= so this will probably remain.
;; The content can always be duplicated which is painful, but the summary line is
;; unlikely to get updated regularly.


;; *** Implementation

;; The main transformation issue is the first line. An =.el= file has a summary
;; at the top. This is checked by checkdoc, used by the various lisp management
;; tools, which in turn impacts on the packaging tools. Additionally, lexical
;; binding really must be set here.

;; We solve this problem by transforming the first line ";;;" into "# #". Having
;; three characters means that the width is maintained. It also means I can
;; distinguish between this kind of comment and an "ordinary" `org-mode' comment;
;; in practice, this doesn't matter, because I only check on the first line. The
;; space is necessary because `org-mode' doesn't recognised "###" as a comment.

;; Another possibility would be to transform the summary line into a header. I
;; choose against this because first it's not really a header being too long and
;; second `org-mode' uses the space before the first header to specify, for
;; example, properties relevant to the entire tree. This is prevented if I make
;; the first line a header 1.

;; **** org to orgel

;; Here we define a new class or org-to-orgel, as well as clone function which
;; adds the ";;;" header transformation in addition to the normal chunk semantics
;; from the superclass. Currently only single word headers are allowed which
;; seems consistent with emacs-lisp usage.

;; #+BEGIN_SRC emacs-lisp
(defclass lentic-org-to-orgel-configuration
  (lentic-unmatched-chunk-configuration lentic-uncommented-chunk-configuration)
  ())


(defun lentic-org--first-line-fixup (conf first-line-end)
  "Fixup the first line of an org->orgel file.

This swaps lines of form:

;; ;;; or
# #

into

;;;"
  (m-buffer-replace-match
   (m-buffer-match
    (lentic-that conf)
    ;; we can be in one of two states depending on whether we have made a new
    ;; clone or an incremental change
    (rx
     (and line-start ";; "
          (submatch (or ";;;"
                        "# #"))))
    :end first-line-end)
   ";;;"))

(defun lentic-org--h1-fixup-from-start (conf first-line-end)
  "Fixup h1 with start

This swaps lines of form

;; * Header

or

;; * Header    :tag:

into

;;; Header:    :tag:"
  (m-buffer-replace-match
           (m-buffer-match
            (lentic-that conf)
            (rx
             (and line-start ";; * "
                  (submatch (1+ word))
                  (optional
                   (submatch
                    (0+ " ")
                    ":" (1+ word) ":"))))
            :begin first-line-end)
           ";;; \\1:\\2"))

(defun lentic-org--h1-fixup-from-semi (conf first-line-end)
  "Fixup h1 with semis"
  (m-buffer-replace-match
   (m-buffer-match
    (lentic-that conf)
    (rx
     (and line-start
          ";; ;;; "
          (submatch (1+ word))
          (optional ":")
          (optional
           (submatch
            (0+ " ")
            ":" (1+ word) ":"))))
    :begin first-line-end)
   ";;; \\1:\\2"))


(defmethod lentic-clone
  ((conf lentic-org-to-orgel-configuration)
   &optional start stop length-before
   start-converted stop-converted)
  ;; do everything else to the buffer
  (m-buffer-with-markers
      ((first-line
        (m-buffer-match-first-line
         (lentic-this conf)))
       (header-one-line
        (m-buffer-match
         (lentic-this conf)
         (rx line-start
             "* " (0+ word)
             (optional (1+ " ")
                       ":" (1+ word) ":")
             line-end)
         :begin (cl-cadar first-line)))
       (special-lines
        (-concat first-line header-one-line)))
    ;; check whether we are in a special line -- if so widen the change extent
    (let*
        ((start-in-special
          (when
              (and
               start
               (m-buffer-in-match-p
                special-lines start))
            (m-buffer-at-line-beginning-position
             (lentic-this conf)
             start)))
         (start (or start-in-special start))
         (start-converted
          (if start-in-special
              (m-buffer-at-line-beginning-position
               (lentic-that conf)
               start-converted)
            start-converted))
         (stop-in-special
          (when
              (and
               stop
               (m-buffer-in-match-p
                special-lines stop))
            (m-buffer-at-line-end-position
             (lentic-this conf)
             stop)))
         (stop (or stop-in-special stop))
         (stop-converted
          (if stop-in-special
              (m-buffer-at-line-end-position
               (lentic-that conf)
               stop-converted)
            stop-converted))
         (clone-return
          (call-next-method conf start stop length-before
                            start-converted stop-converted))
         (first-line-end-match
          (cl-cadar
           (m-buffer-match-first-line
            (lentic-that conf))))
         ;; can't just use or here because we need non-short circuiting
         (c1 (lentic-org--first-line-fixup conf first-line-end-match))
         ;; replace big headers, in either of their two states
         (c2 (lentic-org--h1-fixup-from-start conf first-line-end-match))
         (c3 (lentic-org--h1-fixup-from-semi conf first-line-end-match)))
      (if (or start-in-special stop-in-special c1 c2 c3)
          nil
        clone-return))))

(defmethod lentic-convert
  ((conf lentic-org-to-orgel-configuration)
   location)
  (let ((converted (call-next-method conf location)))
    (m-buffer-with-current-position
        (oref conf :this-buffer)
        location
      (beginning-of-line)
      (if (looking-at
           (rx (submatch "* ")
               (submatch (1+ word))
               (optional (1+ " ")
                         ":" (1+ word) ":")
               line-end))
          (cond
           ((= location (nth 2 (match-data)))
            (m-buffer-at-line-beginning-position
             (oref conf :that-buffer)
             converted))
           ((< location (nth 5 (match-data)))
            (- converted 1))
           (t
            converted))
        converted))))

(defmethod lentic-invert
  ((conf lentic-org-to-orgel-configuration))
  (lentic-m-oset
   (lentic-orgel-org-init)
   :that-buffer
   (lentic-this conf)))

;;;###autoload
(defun lentic-org-orgel-init ()
  (lentic-org-oset
   (lentic-org-to-orgel-configuration
    "lb-orgel-to-el"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name))
     ".el"))))

(add-to-list 'lentic-init-functions
             'lentic-org-orgel-init)
;; #+END_SRC

;; **** orgel->org

;; And the orgel->org implementation. Currently, this means that I have all the
;; various regexps in two places which is a bit ugly. I am not sure how to stop
;; this.

;; #+BEGIN_SRC emacs-lisp
(defvar lentic-orgel-org-init-hook nil)

;; shut byte compiler up and define var for setq-local
(defvar org-archive-default-command)

(defun lentic-orgel-org-init-default-hook (conf)
  ;; Better to open all trees in lentic so that both buffers appears the same
  ;; size.
  (show-all)
  ;; Archiving very easy to and almost always a disaster when it removes an
  ;; entire tree from the buffer.
  (require 'org-archive)
  ;; shorten the fill column by 3, so that the emacs-lisp buffer is the
  ;; correct width.
  (set-fill-column
   (with-current-buffer
       (lentic-that conf)
     (- fill-column 3)))
  (setq-local org-archive-default-command
              (let ((old-archive
                     org-archive-default-command))
                (lambda ()
                  (interactive)
                  (if (yes-or-no-p
                       "Really archive in lentic mode? ")
                      (funcall old-archive)
                    (message "Archiving aborted"))))))

(add-hook 'lentic-orgel-org-init-hook
          #'lentic-orgel-org-init-default-hook)


(defclass lentic-orgel-to-org-configuration
  (lentic-unmatched-chunk-configuration lentic-commented-chunk-configuration)
  ())

(defmethod lentic-create
  ((conf lentic-orgel-to-org-configuration))
  (let ((buf
         (call-next-method conf)))
    (with-current-buffer
        buf
      (run-hook-with-args 'lentic-orgel-org-init-hook conf))
    buf))

(defmethod lentic-clone
  ((conf lentic-orgel-to-org-configuration)
   &optional start stop length-before start-converted stop-converted)
  ;; do everything else to the buffer
  (let* ((clone-return
          (call-next-method conf start stop length-before
                            start-converted stop-converted))
         (m1
          (m-buffer-replace-match
           (m-buffer-match
            (lentic-that conf)
            ";;; "
            :end
            (cl-cadar
             (m-buffer-match-first-line
              (lentic-that conf))))
           "# # "))
         (m2
          (m-buffer-replace-match
           (m-buffer-match (lentic-that conf)
                           (rx line-start ";;; "
                               (submatch (0+ word))
                               ":"
                               (optional
                                (submatch
                                 (0+ " ")
                                 ":" (1+ word) ":"))
                               line-end))
           "* \\1\\2")))
    (unless
        ;; update some stuff
        (or m1 m2)
      ;; and return clone-return unless we have updated stuff in which case
      ;; return nil
      clone-return)))

(defmethod lentic-convert
  ((conf lentic-orgel-to-org-configuration)
   location)
  ;; if we are a header one and we are *after* the first :, then just call
  ;; next-method.
  (let* ((cnm
         (call-next-method conf location))
        (line-start-that
         (m-buffer-at-line-beginning-position
          (oref conf :that-buffer) cnm))
        (line-start-this
         (m-buffer-at-line-beginning-position
          (oref conf :this-buffer) location)))
    (if
        (m-buffer-with-current-position
            (oref conf :this-buffer)
            location
          (beginning-of-line)
          (looking-at
           (rx ";;; "
               (1+ word)
               (submatch ":")
               (optional (1+ " ")
                         ":" (1+ word) ":"))))
        ;; hey global state!
        (let ((colon (nth 3 (match-data))))
          ;; if in the comments, just return the start of the
          ;; line, if we are after the comments but before the colon, fudge
          ;; it. If we are after the colon, count from the end
          (cond
           ((> 3 (- location line-start-this))
            line-start-that)
           ((> location colon)
            cnm)
           (t
            (+ cnm 1))))
      cnm)))

(defmethod lentic-invert
  ((conf lentic-orgel-to-org-configuration))
  (lentic-m-oset
   (lentic-org-orgel-init)
   :delete-on-exit t
   :that-buffer (lentic-this conf)))

;;;###autoload
(defun lentic-orgel-org-init ()
  (lentic-org-oset
   (lentic-orgel-to-org-configuration
    "lb-orgel-to-org"
    ;; we don't really need a file and could cope without, but org mode assumes
    ;; that the buffer is file name bound when it exports. As it happens, this
    ;; also means that file saving is possible which in turn saves the el file
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name))
     ".org"))))

(add-to-list 'lentic-init-functions
             'lentic-orgel-org-init)

;; #+END_SRC


;; ** org->clojure

;; #+BEGIN_SRC emacs-lisp
(defun lentic-org-clojure-oset (conf)
  (lentic-m-oset
   conf
   :this-buffer (current-buffer)
   :comment ";; "
   :comment-stop "#\\\+BEGIN_SRC clojure.*"
   :comment-start "#\\\+END_SRC"))

;;;###autoload
(defun lentic-org-clojure-init ()
  (lentic-org-clojure-oset
   (lentic-unmatched-uncommented-chunk-configuration
    "lb-org-to-clojure"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name))
     ".clj"))))

(add-to-list 'lentic-init-functions
             'lentic-org-clojure-init)

;;;###autoload
(defun lentic-clojure-org-init ()
  (lentic-org-clojure-oset
   (lentic-unmatched-commented-chunk-configuration
    "lb-clojure-to-org"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name))
     ".org"))))

(add-to-list 'lentic-init-functions
             'lentic-clojure-org-init)
;; #+END_SRC

;; ** org->python

;; #+begin_src emacs-lisp
(defun lentic-org-python-oset (conf)
  (lentic-m-oset
   conf
   :this-buffer (current-buffer)
   :comment "## "
   :comment-stop "#\\\+BEGIN_SRC python.*"
   :comment-start "#\\\+END_SRC"))

;;;###autoload
(defun lentic-org-python-init ()
  (lentic-org-python-oset
   (lentic-unmatched-uncommented-chunk-configuration
    "lb-org-to-python"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name))
     ".py"))))

(add-to-list 'lentic-init-functions
             'lentic-org-python-init)

;;;###autoload
(defun lentic-python-org-init ()
  (lentic-org-python-oset
   (lentic-unmatched-commented-chunk-configuration
    "lb-python-to-org"
    :lentic-file
    (concat
     (file-name-sans-extension
      (buffer-file-name))
     ".org"))))

(add-to-list 'lentic-init-functions
             'lentic-python-org-init)
;; #+end_src

;;; Footer:

;; Declare the end of the file, and add file-local support for orgel->org
;; transformation. Do not use lentics on this file while changing the
;; lisp in the file without backing up first!

;; #+BEGIN_SRC emacs-lisp
(provide 'lentic-org)
;;; lentic-org.el ends here
;; #+END_SRC
