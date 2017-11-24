;;; info-lookmore.el --- more things for info-look.el

;; Copyright 2008, 2009, 2010, 2011, 2013, 2014, 2015, 2016, 2017 Kevin Ryde

;; Author: Kevin Ryde <user42_kevin@yahoo.com.au>
;; Version: 7
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

;; This is some more manuals and a couple more mode setups for
;; `info-lookup-symbol'.
;;
;; Functions adding manuals are `interactive' so you can for example
;; `M-x info-lookmore-c-gcc' to see it just for the current session.
;;
;; More manuals can be added with `info-lookmore-add-doc' calls.  Usually
;; you have to find the node name of the index, then check whether entries
;; can be used directly or need mangling.  The easiest is when there's a
;; separate "Functions" or "Functions and Variables" index.  See docstring
;; of `info-lookup-alist' for the details.

;;; Emacsen:

;; Designed for Emacs 21 and up.  Works in XEmacs 21.
;; Doesn't work in Emacs 20 due to "append" parameter to `add-to-list'.

;;; Install:

;; Put info-lookmore.el in one of your `load-path' directories, and in your
;; .emacs add for each setup function you want,
;;
;;     (autoload 'info-lookmore-c-gcc "info-lookmore" nil t)
;;     (eval-after-load "info-look" '(info-lookmore-c-gcc))
;;
;; There's autoload cookies for the functions below if you install via
;; `M-x package-install' or know how to use `update-file-autoloads'.  Then
;; `eval-after-load' for each you want permanently, or M-x for one session.

;;; History:

;; Version 1 - the first version
;; Version 2 - new info-lookmore-coreutils-index
;; Version 3 - info-lookmore-c++-use-c correction to file setup
;;           - info-lookmore-coreutils-index do nothing in emacs21
;; Version 4 - new info-lookmore-makefile-derivatives
;; Version 5 - new info-lookmore-c-gsl
;; Version 6 - makeinfo single-quote variants
;; Version 7 - really end at "ends here", don't add-to-list on let binding

;;; Code:

(require 'info-look)

(eval-when-compile
  (unless (and (fboundp 'declare)  ;; macros
               (fboundp 'ignore-errors))
    (require 'cl))) ;; for macros


(defun info-lookmore->mode-value (topic mode)
  "An internal part of info-lookmore.el.
Return the mode value list for TOPIC and MODE.
This is `info-lookup->mode-value', but signalling an error if
TOPIC and MODE are not found."
  (or (info-lookup->mode-value topic mode)
      (error "Topic `%S' or mode `%S' not found in info-lookup-alist"
             topic mode)))
(eval-when-compile
  (put 'info-lookmore->mode-value 'side-effect-free t))

(defun info-lookmore-modify-doclist (topic mode func)
  "Modify document list for info-lookup TOPIC and MODE by calling FUNC.
FUNC is called (FUNC doc-list) and its return value is set as the
new doc-list.  FUNC mustn't change the given doc-list, but should
copy or cons as necessary.

If FUNC returns a changed DOC-LIST then `info-lookup-reset' is
called so that it takes effect on the next lookup."

  (declare (indent 2))
  (let* ((mode-value (info-lookmore->mode-value topic mode))
         (old        (nth 3 mode-value))
         (new        (funcall func old)))
    (unless (equal old new)
      (setcar (nthcdr 3 mode-value) new)
      (info-lookup-reset))))

;;;###autoload
(defun info-lookmore-add-doc (topic mode doc-spec &optional append)
  "Add a document to `info-lookup-alist'.
TOPIC is a symbol, either `symbol' or `file'.
MODE is a symbol, a major mode name such as `foo-mode'.
DOC-SPEC should be (INFO-NODE TRANS-FUNC PREFIX SUFFIX) as
described by `info-lookup-alist'.

If DOC-SPEC is not already present then it's added before
existing docs, or if APPEND is non-nil then after."

  (info-lookmore-modify-doclist topic mode
    (lambda (doc-list)
      (cond ((member doc-spec doc-list)
             doc-list) ;; already present, list unchanged
            (append    ;; otherwise add by append or prepend
             (append doc-list (list doc-spec)))
            (t
             (cons doc-spec doc-list))))))

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
reference manual for a function or variable which might be in
both the user manual and reference manual.

See info node `(elisp)Top' for the Elisp reference manual and
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
Elisp manual for the few functions like `push' which are in both.
Or maybe CL should be preferred when using CL, so perhaps this
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
                         (eval-when-compile
                           `("(gnus)Index"
                             nil
                             ;; Match various `foo' unindented as well as
                             ;; "-- Function: " style.
                             ;;
                             ;; `mm-file-name-trim-whitespace' unfortunately
                             ;; only appears in the middle of a para, so it
                             ;; doesn't get found by these patterns.
                             ;;
                             ,(concat "^\\( --? .*: \\|[`'"  ;; prefix
                                      ;; U+2018 left single quote, if possible
                                      (or (ignore-errors (string (decode-char 'ucs 8216))) "")
                                      "]\\)")
                             ,(concat "\\([ '"  ;; suffix
                                      ;; U+2019 right single quote, if possible
                                      (or (ignore-errors (string (decode-char 'ucs 8217))) "")
                                      "]\\|$\\)")))
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
                             ;; same unindented etc as the (gnus) setup above
                             ,(concat "^\\( --? .*: \\|[`'"
                                      ;; U+2018 left single quote, if possible
                                      (or (ignore-errors (string (decode-char 'ucs 8216))) "")
                                      "]\\)")
                             ,(concat "\\([ '"
                                      ;; U+2019 right single quote, if possible
                                      (or (ignore-errors (string (decode-char 'ucs 8217))) "")
                                      "]\\|$\\)")))
                         t)) ;; append

;;;###autoload
(defun info-lookmore-apropos-elisp ()
  "Set `apropos-mode' info-lookup to follow `emacs-lisp-mode'.
apropos-mode is the function/variable docstring display for
`describe-function' etc.  Symbols etc are usually Elisp things
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
  "Add the GNU C manual to `c-mode' info-lookup.
This gives various GCC specifics like __builtin_expect() or
__func__.  It's appended to the doc-list, so the main GNU C
Library manual is preferred for things appearing in both (such as
most of the math.h functions).

See info node `(gcc)Top' for the GCC manual, and info
node `(libc)Top' for the GNU C manual."

  ;; As of gcc 4.9 the cpp manual doesn't have an index node with its
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
This function copies the `c-mode' regexp and parse rule if
nothing else has already made a `c++-mode' entry.  Not sure if
that comes out quite right for real C++, but it's fine for
mostly-C things."

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
make manual.  The others go to `makefile-mode' only.

These setups are incorporated in Emacs 24 info-look.el so are not
needed there."

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
                 ("(automake)Variable Index" nil "^[ \t]*[`']" "'")
                 ;; in automake 1.4 it was a combined node
                 ("(automake)Macro and Variable Index" nil "^[ \t]*`" "'")

                 ;; Directives like "if" are in the General Index.
                 ;; Prefix "`" since the text for say `+=' isn't always have
                 ;; an @item etc of its own.
                 ("(automake)General Index" nil "[`']" "'")
                 ;; In automake 1.3 there was just a single "Index" node.
                 ("(automake)Index" nil "[`']" "'")))

  ;; Same REGEXP, PARSE-RULE as makefile-mode.  These make variants probably
  ;; have some of their own syntax variations etc, but there won't be
  ;; anything in the GNU make manual to describe that, so no benefit to
  ;; extra PARSE-RULE etc.
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

;;------------------------------------------------------------------------------

;; LocalWords:  lookup FUNC docstring builtin func readline automake Elisp
;; LocalWords:  coreutils lookmore

(provide 'info-lookmore)

;;; info-lookmore.el ends here
