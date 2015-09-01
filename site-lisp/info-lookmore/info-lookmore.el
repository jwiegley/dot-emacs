;;; info-lookmore.el --- more things for info-look.el

;; Copyright 2008, 2009, 2010, 2011 Kevin Ryde

;; Author: Kevin Ryde <user42@zip.com.au>
;; Version: 5
;; Keywords: help, languages, info-look
;; URL: http://user42.tuxfamily.org/info-lookmore/index.html

;; info-lookmore.el is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by the
;; Free Software Foundation; either version 3, or (at your option) any later
;; version.
;;
;; info-lookmore.el is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General
;; Public License for more details.
;;
;; You can get a copy of the GNU General Public License online at
;; <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is some more stuff for `info-lookup-symbol' -- some specific manuals
;; to add and a couple of mode setups.
;;
;; Functions adding manuals are `interactive' you can M-x whatever to have
;; it just for the current session.
;;
;; For manuals not covered see `info-lookmore-add-doc'.  Usually you have to
;; find the node name for the index, then check whether entries can be used
;; directly or need mangling.  The easiest is when there's a separate
;; "Functions" or "Functions and Variables" index.  See `info-lookup-alist'
;; for the details.

;;; Install:

;; Put info-lookmore.el in one of your `load-path' directories, and in your
;; .emacs add for example
;;
;;     (autoload 'info-lookmore-elisp-cl "info-lookmore" nil t)
;;     (eval-after-load "info-look" '(info-lookmore-elisp-cl))
;;
;; for each setup function you want.
;;
;; There's autoload cookies for the functions if you know how to use
;; `update-file-autoloads' and friends, after which just `eval-after-load'
;; for each you want permanently, or M-x for one session.

;;; History:

;; Version 1 - the first version
;; Version 2 - new info-lookmore-coreutils-index
;; Version 3 - info-lookmore-c++-use-c correction to file setup
;;           - info-lookmore-coreutils-index do nothing in emacs21
;; Version 4 - new info-lookmore-makefile-derivatives
;; Version 5 - new info-lookmore-c-gsl

;;; Code:

(require 'info-look)

(put  'info-lookmore->mode-value 'side-effect-free t)
(defun info-lookmore->mode-value (topic mode)
  "Return the mode value list for TOPIC and MODE.
This is `info-lookup->mode-value', but signalling an error if
TOPIC and MODE are not found."
  (or (info-lookup->mode-value topic mode)
      (error "Topic `%S' or mode `%S' not found in info-lookup-alist"
             topic mode)))

(put  'info-lookmore-modify-doclist 'lisp-indent-function 2)
(defun info-lookmore-modify-doclist (topic mode func)
  "Call FUNC to modify the document list for info-lookup TOPIC and MODE.
FUNC is called (FUNC doc-list) and its return value is set as the
new doc-list.  FUNC mustn't change the old value, but should copy
or cons as necessary.

If FUNC returns a changed DOC-LIST then `info-lookup-reset' is
called to let it take effect on the next lookup."

  ;; (declare (indent 1)) ;; emacs22,xemacs21, or 'cl
  (let* ((mode-value (info-lookmore->mode-value topic mode))
         (old        (nth 3 mode-value))
         (new        (funcall func old)))
    (unless (equal old new)
      (setcar (nthcdr 3 mode-value) new)
      (info-lookup-reset))))

;;;###autoload
(defun info-lookmore-add-doc (topic mode doc-spec &optional append)
  "Add DOC-SPEC to an existing `info-lookup-alist' entry.
DOC-SPEC should be (INFO-NODE TRANS-FUNC PREFIX SUFFIX) as
described by `info-lookup-alist'.

If DOC-SPEC is not already present then it's added before
existing docs, or if APPEND is non-nil then after."

  (info-lookmore-modify-doclist topic mode
    (lambda (doc-list)
      (add-to-list 'doc-list doc-spec append))))

;; ;;;###autoload
;; (defun info-lookmore-remove-doc (topic mode info-node)
;;   "Remove INFO-NODE from an `info-lookup-alist' entry, if present."
;;   (info-lookmore-modify-doclist topic mode
;;     (lambda (doc-list)
;;       (remove (assoc info-node doc-list)
;;               doc-list))))

;;;###autoload
(defun info-lookmore-add-other-mode (topic mode other-mode &optional append)
  "Add OTHER-MODE to an `info-lookup-alist' entry.
OTHER-MODE is added if not already present and is added before
existing other-modes, or if APPEND is non-nil then after existing
other-modes."
  (let* ((mode-value (info-lookmore->mode-value topic mode))
         (lst    (nth 5 mode-value)))
    (add-to-list 'lst other-mode append)
    (setcar (nthcdr 5 mode-value) lst)))


;;-----------------------------------------------------------------------------
;; elisp

;;;###autoload
(defun info-lookmore-elisp-userlast ()
  "Put the Emacs user manual last for `info-lookup-symbol'.
This is good for programming when you'll prefer to look in the
reference manual for a function or variable in both the user and
reference manuals.

See info node `(elisp)Top' for the elisp reference manual and
info node `(emacs)Top' for the user manual."

  (interactive)
  (info-lookmore-modify-doclist 'symbol 'emacs-lisp-mode
    (lambda (doc-list)
      (let ((case-fold-search nil)
            pre post)
        (dolist (doc doc-list)
          (add-to-list (if (string-match "\\`(emacs)" (car doc)) 'post 'pre)
                       doc t))
        (append pre post)))))

;;;###autoload
(defun info-lookmore-elisp-cl ()
  "Add the Emacs CL manual to `emacs-lisp-mode' info-lookup.
CL is appended to the document list, so as to prefer the main
elisp manual for the few functions like `push' which are in both.
But maybe CL should be preferred when using CL, so perhaps this
will change.

See info node `(cl)Top' for the CL manual."

  (interactive)
  (info-lookmore-add-doc 'symbol 'emacs-lisp-mode
                          '("(cl)Function Index" nil
                            "^ --? .*: "
                            "\\( \\|$\\)")
                          t) ;; append
  (info-lookmore-add-doc 'symbol 'emacs-lisp-mode
                          '("(cl)Variable Index" nil
                            "^ --? .*: "
                            "\\( \\|$\\)")
                          t)) ;; append

;;;###autoload
(defun info-lookmore-elisp-gnus ()
  "Add the Gnus and MIME manuals to `emacs-lisp-mode' info-lookup.
See info node `(gnus)Top' for the Gnus manual and info
node `(emacs-mime)Top' for the Emacs MIME manual."

  (interactive)
  (info-lookmore-add-doc 'symbol 'emacs-lisp-mode
                         '("(gnus)Index"
                           nil
                           ;; Match various `foo' unindented as well as
                           ;; "-- Function: " style.
                           ;;
                           ;; `mm-file-name-trim-whitespace' unfortunately
                           ;; only appears in the middle of a para, so it
                           ;; doesn't get found by these patterns.
                           ;;
                           "^\\( --? .*: \\|`\\)"
                           "\\([ ']\\|$\\)")
                         t) ;; append
  (info-lookmore-add-doc 'symbol 'emacs-lisp-mode
                         (eval-when-compile
                           `("(emacs-mime)Index"
                             ,(lambda (item)
                                ;; the lisp functions are lower-case, avoid
                                ;; concept entries like "LaTeX"
                                (let ((case-fold-search nil))
                                  (and (string-match "\\`[a-z]" item)
                                       item)))
                             ;; same unindented etc (gnus) above
                             "^\\( --? .*: \\|`\\)"
                             "\\([ ']\\|$\\)"))
                         t)) ;; append

;;;###autoload
(defun info-lookmore-apropos-elisp ()
  "Set `apropos-mode' info-lookup to follow `emacs-lisp-mode'.
apropos-mode is the function/variable docstring display for
`describe-function' etc.  Symbols etc are usually elisp things
and following `emacs-lisp-mode' lets you look them up.

This function is for use in Emacs 23.1 and earlier.  23.2 and up
has this setup already and this function does nothing there."

  (info-lookup-maybe-add-help
   :topic       'symbol
   :mode        'apropos-mode
   :regexp      (info-lookup->regexp     'symbol 'emacs-lisp-mode)
   :parse-rule  (info-lookup->parse-rule 'symbol 'emacs-lisp-mode))
  (info-lookmore-add-other-mode 'symbol 'apropos-mode 'emacs-lisp-mode))


;;-----------------------------------------------------------------------------
;; C

;;;###autoload
(defun info-lookmore-c-gcc ()
  "Add the GCC manual to `c-mode' info-lookup.
This gives various GCC specifics like __builtin_expect() or
__func__.  It's appended to the doc-list, so the main GNU C
Library is preferred for things appearing in both (which includes
lots of math.h functions).

See info node `(gcc)Top' for the GCC manual, and info
node `(libc)Top' for the GNU C manual."

  ;; As of gcc 4.3 the cpp manual doesn't have an index node with its
  ;; predefined macros like __GNUC__, so can't get those.  The preprocessor
  ;; directives like #if in "Index of Directives" would be a possibility,
  ;; but would want `info-lookup-guess-c-symbol' to recognise the "#".

  (interactive)
  (info-lookmore-add-doc
   'symbol 'c-mode
   (eval-when-compile
     `("(gcc)Keyword Index"
       ,(lambda (item)
          ;; strip trailing bits from
          ;;     "__float128 data type"
          ;;     "__complex__ keyword"
          ;;     "__func__ identifier"
          (if (string-match " \\(data type\\|keyword\\|identifier\\)\\'" item)
              (setq item (substring item 0 (match-beginning 0))))
          ;; anything with a space is a concept rather than a func/var/etc
          (and (not (string-match " " item))
               item))
       "^ -.* "
       "\\>"))
   t)) ;; append

;;;###autoload
(defun info-lookmore-c-readline ()
  "Add the readline manuals to `c-mode' info-lookup.
See info node `(readline)Top' for the readline manual, and info
node `(history)Top' for the related history manual, which is also
added."
  (interactive)
  (info-lookmore-add-doc 'symbol 'c-mode
                          '("(readline)Function and Variable Index" nil
                            "^ -.* " "\\>"))
  (info-lookmore-add-doc 'symbol 'c-mode
                          '("(history)Function and Variable Index" nil
                            "^ -.* " "\\>")))

;;;###autoload
(defun info-lookmore-c-gsl ()
  "Add the GNU Scientific Library manuals to `c-mode' info-lookup.
See info node `(gsl-ref)Top' for the GSL manual."
  (interactive)
  (info-lookmore-add-doc 'symbol 'c-mode
                         '("(gsl-ref)Function Index"
                           nil
                           "^ -.* " "\\>"))
  (info-lookmore-add-doc 'symbol 'c-mode
                         '("(gsl-ref)Type Index"
                           nil
                           "^ -.* " "\\>"))
  (info-lookmore-add-doc
   'symbol 'c-mode
   `("(gsl-ref)Variable Index"
     ,(lambda (item)
        ;; As of GSL 1.15 only the "gsl_*" and "GSL_*" names in the Variable
        ;; Index are globals.  Entries for "alpha", "verbose" etc are fields
        ;; of "struct gsl_monte_vegas_params" and similar.
        (and (let ((case-fold-search t))
               (string-match "\\`gsl" item))
             item))
     "^ -.* " "\\>")))


;;-----------------------------------------------------------------------------
;; C++

;;;###autoload
(defun info-lookmore-c++-use-c ()
  "Set `c++-mode' info-lookup to follow `c-mode'.
This is good if you write a lot of C-like things in C++, or at
least want to include the C manuals.

`info-lookup-alist' doesn't have a c++-mode entry by default.
This function copies the c-mode regexp and parse rule if nothing
else has already made a c++-mode entry.  Not sure if that comes
out quite right for real C++, but it's fine for mostly-C things."

  (interactive)
  (info-lookup-maybe-add-help
   :topic      'file
   :mode       'c++-mode
   :regexp     (info-lookup->regexp     'file 'c-mode)
   :parse-rule (info-lookup->parse-rule 'file 'c-mode))
  (info-lookup-maybe-add-help
   :topic      'symbol
   :mode       'c++-mode
   :regexp     (info-lookup->regexp     'symbol 'c-mode)
   :parse-rule (info-lookup->parse-rule 'symbol 'c-mode))

  (info-lookmore-add-other-mode 'file   'c++-mode 'c-mode)
  (info-lookmore-add-other-mode 'symbol 'c++-mode 'c-mode))


;;-----------------------------------------------------------------------------
;; makefile-mode derivatives

;;;###autoload
(defun info-lookmore-makefile-derivatives ()
  "Add info-lookup setups for `makefile-mode' derivatives.
The following modes are setup, if they don't already have setups.

    `makefile-automake-mode'
    `makefile-bsdmake-mode'
    `makefile-gmake-mode'
    `makefile-imake-mode'
    `makefile-makepp-mode'

`makefile-automake-mode' looks in the automake manual then the
make manual.  The others go to `makefile-mode' only."

  (interactive)
  (info-lookup-maybe-add-help
   :topic      'symbol
   :mode       'makefile-automake-mode
   ;; similar regexp/parse-rule as makefile-mode, but also
   ;;   "##" special automake comment
   ;;   "+=" append operator, separate from the GNU make one
   :regexp     "\\$[^({]\\|\\.[_A-Z]*\\|[_a-zA-Z][_a-zA-Z0-9-]*\\|##\\|\\+="
   :parse-rule "\\$[^({]\\|\\.[_A-Z]*\\|[_a-zA-Z0-9-]+\\|##\\|\\+="
   :doc-spec   '(
                 ;; "(automake)Macro Index" is autoconf macros used in
                 ;; configure.in, not Makefile.am, so don't have that here.
                 ("(automake)Variable Index" nil "^[ \t]*`" "'")
                 ;; in automake 1.4 it was a combined node
                 ("(automake)Macro and Variable Index" nil "^[ \t]*`" "'")

                 ;; Directives like "if" are in the General Index.
                 ;; Prefix "`" since the text for say `+=' isn't always have
                 ;; an @item etc of its own.
                 ("(automake)General Index" nil "`" "'")
                 ;; In automake 1.3 there was just a single "Index" node.
                 ("(automake)Index" nil "`" "'")))

  ;; Same REGEXP, PARSE-RULE as makefile-mode.
  ;; Even if these make variants have their own variable forms etc there no
  ;; benefit recognising them if theres nothing in the GNU make manual
  ;; describing them.
  (let ((regexp     (info-lookup->regexp     'symbol 'makefile-mode))
        (parse-rule (info-lookup->parse-rule 'symbol 'makefile-mode)))
    (dolist (mode '(makefile-bsdmake-mode
                    makefile-gmake-mode
                    makefile-imake-mode
                    makefile-makepp-mode))
      (info-lookup-maybe-add-help
       :topic       'symbol
       :mode        mode
       :regexp      regexp
       :parse-rule  parse-rule
       :other-modes '(makefile-mode)))))


;;-----------------------------------------------------------------------------
;; sh-mode

;;;###autoload
(defun info-lookmore-coreutils-index ()
  "Add \"(coreutils)Concept Index\" node name.
Past coreutils used node name \"Index\", versions circa 8.1 use
\"Concept Index\".  The latter is added to `sh-mode' setups if
not already present.

This function is for use in Emacs 22.x and 23.1.  Emacs 23.2 has
this setup already and this function does nothing there.  Emacs
21 and XEmacs 21 don't have any `sh-mode' setups and nothing is
done there unless you've added your own (in which case copying
from the latest Emacs is probably best)."

  (interactive)
  (when (let ((doc-specs (info-lookup->doc-spec 'symbol 'sh-mode)))
          (and doc-specs
               (not (assoc "(coreutils)Concept Index" doc-specs))))
    (info-lookmore-add-doc
     'symbol 'sh-mode
     (eval-when-compile
       `("(coreutils)Concept Index"
         ,(lambda (item) (if (string-match "\\`[a-z]+\\'" item) item)))))))


(provide 'info-lookmore)

;;; info-lookmore.el ends here
