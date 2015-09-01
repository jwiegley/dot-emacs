;;; muse-init-project.el --- Use Emacs Muse to publish ikiwiki documents

;; The code in this file may be used, distributed, and modified
;; without restriction.

;;; Setup

(add-to-list 'load-path (expand-file-name "~ikiwiki/elisp/muse/lisp"))

;; Initialize
(require 'muse)          ; load generic module
(require 'muse-html)     ; load (X)HTML publishing style
(require 'muse-ikiwiki)  ; load Ikiwiki integration
(require 'muse-project)  ; load support for projects
(require 'muse-wiki)     ; load Wiki support

;;; Settings

;; New variables
(defvar muse-ikiwiki-project "HCoopWiki"
  "Name of the project to publish using ikiwiki.")
(defvar muse-ikiwiki-source "/afs/hcoop.net/common/ikiwiki/repo"
  "Source directory for Muse files.")
(defvar muse-ikiwiki-dest "/afs/hcoop.net/common/ikiwiki/dest"
  "Destination directory for published files.")

;; Project listing
(setq muse-project-alist
      `((,muse-ikiwiki-project
         (,@(muse-project-alist-dirs muse-ikiwiki-source))
         ;; Publish this directory and its subdirectories.  Arguments
         ;; are as follows.  The above `muse-project-alist-dirs' part
         ;; is also needed.
         ;;   1. Source directory
         ;;   2. Output directory
         ;;   3. Publishing style
         ;;   remainder: Other things to put in every generated style
         ,@(muse-project-alist-styles muse-ikiwiki-source
                                      muse-ikiwiki-dest
                                      "ikiwiki"))))

;; Wiki settings
(setq muse-wiki-allow-nonexistent-wikiword t
      muse-wiki-match-all-project-files t
      muse-wiki-interwiki-delimiter "::")
(add-to-list 'muse-publish-desc-transforms 'muse-wiki-publish-pretty-interwiki)
(add-to-list 'muse-publish-desc-transforms 'muse-wiki-publish-pretty-title)
(setq muse-wiki-interwiki-alist
      '(("EmacsWiki" . "http://www.emacswiki.org/cgi-bin/wiki/")
        ("UbuntuLinux" . "http://ubuntulinux.org/")))

;; Permitted modes for <src> to colorize
(setq muse-html-src-allowed-modes
      '("ada" "apache" "asm" "awk" "c++" "c" "cc" "change-log" "context"
        "css" "diary" "diff" "dns" "domtool" "emacs-lisp" "f90" "fortran"
        "fundamental" "html" "java" "jython" "latex" "lisp" "lua" "m4"
        "makefile" "markdown" "matlab" "maxima" "message" "modula-2" "muse"
        "nroff" "octave" "org" "outline" "pascal" "perl" "ps" "python" "rst"
        "ruby" "scheme" "sgml" "sh" "slang" "sml" "sml-cm" "sml-lex" "sml-yacc"
        "sql" "tcl" "tex" "texinfo" "xml" "zone"))
;; In case someone does <src lang="muse">
(setq muse-colors-evaluate-lisp-tags nil
      muse-colors-inline-images nil)
;; In case someone does <src lang="org">
(require 'org)
(setq org-inhibit-startup t
      org-table-formula-evaluate-inline nil)

;; Don't allow dangerous tags to be published
(setq muse-publish-enable-dangerous-tags nil)

;;; Custom variables

(custom-set-variables
 '(muse-html-charset-default "utf-8")
 '(muse-html-encoding-default (quote utf-8))
 '(muse-html-meta-content-encoding (quote utf-8))
 '(muse-publish-comments-p t)
 '(muse-publish-date-format "%b. %e, %Y"))
(custom-set-faces
 '(muse-bad-link ((t (:foreground "DeepPink" :underline "DeepPink" :weight bold)))))

;;; muse-init-project.el ends here
