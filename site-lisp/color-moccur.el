;;; color-moccur.el ---  multi-buffer occur (grep) mode
;; -*- Mode: Emacs-Lisp -*-

;; $Id: color-moccur.el,v 2.71 2010-05-06 13:40:54 Akihisa Exp $

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;;; for hi-lock
;; Hi-lock: (("^;;; .*" (0 (quote hi-black-hb) t)))
;; Hi-lock: (("^;;;; .*" (0 (quote hi-black-b) t)))
;; Hi-lock: (("make-variable-buffer-\\(local\\)" (0 font-lock-keyword-face)(1 'italic append)))
;; Hi-lock: end

;;; Commentary:
;; If this program doesn't run, I might change the program for the
;; worse.  So please send mail to akihisa@mail.ne.jp .

;; This elisp is the extention of moccur.el.
;; Thanks to the authors for writing moccur.el

;; With color-moccur, you can search a regexp in all buffers. And you
;; can search files like grep(-find) without grep (and find) command.

;;; Motivation
;; moccur is a major mode modelled after the 'Occur' mode of the
;; standard distribution. It is quite nice to use when you need to
;; work with a lot of buffers.
;;
;; Incompatibilites to Occur mode:
;; a) it browses through *all* buffers that have a file name
;; associated with them; those may or may not include the current
;; buffer. Especially, while standard occur works
;; on 'all lines following point', Moccur does not.
;; b) there is no support for the 'NLINE' argument.

;;; Install:
;; Put this file into load-path'ed directory, and byte compile it if
;; desired.  And put the following expression into your ~/.emacs.
;;
;;     (require 'color-moccur)

;; The latest version of this program can be downloaded from
;; http://www.bookshelf.jp/elc/color-moccur.el

;; moccur-edit.el
;;   With this packege, you can edit *moccur* buffer and apply
;;   the changes to the files.
;;   You can get moccur-edit.el at
;;   http://www.bookshelf.jp/elc/moccur-edit.el

;;; Functions
;; moccur, dmoccur, dired-do-moccur, Buffer-menu-moccur,
;; grep-buffers, search-buffers, occur-by-moccur
;; isearch-moccur
;; moccur-grep, moccur-grep-find

;;; usage:moccur
;; moccur <regexp> shows all occurrences of <regexp> in all buffers
;; currently existing that refer to files.
;; The occurrences are displayed in a buffer running in Moccur mode;
;;;; keybind
;; C-c C-c or RET gets you to the occurrence
;; q : quit
;; <up>, n, j   : next matches
;; <down>, p, k : previous matches
;; b :scroll-down in matched buffer
;; SPC : scroll-up in matched buffer
;; M-v :scroll-down in moccur buffer
;; C-v : scroll-up in moccur buffer
;; < : M-< in matched buffer
;; > : M-> in matched buffer
;; t : toggle whether a searched buffer is displayed to other window.
;; r : re-search in only matched buffers.
;; d,C-k : kill-line
;; M-x moccur-flush-lines : flush-lines for moccur
;; M-x moccur-keep-lines : keep-lines for moccur
;; / : undo (maybe doesn't work)
;; s : run moccur by matched bufffer only.
;; u : run moccur by prev condition

;;; usage:moccur-grep, moccur-grep-find
;; moccur-grep <regexp> shows all occurrences of <regexp> in files of current directory
;; moccur-grep-find <regexp> shows all occurrences of <regexp>
;;                  in files of current directory recursively.
;;
;;;; Variables of M-x moccur-grep(-find)
;; dmoccur-exclusion-mask : if filename matches the regular
;; expression, dmoccur/moccur-grep *doesn't* open the file.
;;
;; dmoccur-maximum-size: Maximum size (kB) of a buffer for dmoccur and
;; moccur-grep(-find).
;;
;; moccur-following-mode-toggle :
;; If this value is t, cursor motion in the moccur buffer causes
;; automatic display of the corresponding buffer location.
;;
;; moccur-grep-following-mode-toggle :
;; If this value is t, cursor motion in the moccur-grep buffer causes
;; automatic display of the corresponding source code location.
;;
;; moccur-grep-default-word-near-point :
;; If this value is t, moccur-grep(-find) command get a word near the
;; point as default regexp string
;;
;; moccur-grep-default-mask :
;; example in .emacs: (setq-default moccur-grep-default-mask ".el")
;; File-mask string used for default in moccur-grep and moccur-grep-find
;; Run moccur-grep, and chose directory, in minibuffer, following text is displayed
;; Input Regexp and FileMask:  .el

;;; usage:isearch-moccur
;; isearch and M-o
;; Run `moccur' with current isearch string.
;; isearch and M-O
;; Run `moccur' with current isearch string in all buffers.

;;; usage:M-x occur-by-moccur
;; suearch current buffer by moccur

;;; usage:Buffer-menu-moccur
;; `Buffer-menu-moccur' command searches buffers marked in
;; buffer-menu or ibuffer.

;;; usage:dired-do-moccur
;; Search through all marked files in dired buffer.

;;; usage:search-buffers <regexp>
;; junk tool. To search all buffers, type in
;; a few descriptive words like "setq gnus" hit the 'enter' key.
;; This program only returns web pages that contain all the words in
;; your query. And Type RET in the result buffer to call moccur.

;;; usage:grep-buffers <regexp>
;; Run grep on all visited files.

;;; usage:M-x dmoccur
;; dmoccur opens files under current directory, and searches your
;; regular expression by moccur.

;;;; Variables of M-x dmoccur
;; dmoccur-mask : if filename matches the regular expression, dmoccur
;; opens the file.
;; dmoccur-exclusion-mask : if filename matches the regular
;; expression, dmoccur/moccur-grep *doesn't* open the file.
;; dmoccur-maximum-size : Only buffers less than this can be opend.

;;;; C-u M-x dmoccur
;; Probably you will search same directory many times. So dmoccur has
;; your favorite directory list. And if you input a name, dmoccur can
;; search files under a directory.

;;;; variable:dmoccur-mask
;; dmoccur-mask is masks for searched file. defult is (".*").

;;;; variable:dmoccur-maximum-size
;; Maximum size (kB) of a searched buffer by dmoccur.

;;;; variable:dmoccur-exclusion-mask
;; dmoccur-exclusion-mask is masks for *not* searched file by dmoccur and moccur-grep(-find).

;;;; Variables of C-u M-x dmoccur
;; dmoccur-list : Your favorite directory list. This valiable is used
;; as bellow.

;; (setq dmoccur-list
;;       '(
;;         ;;name    directory         mask               option
;;         ("dir"    default-directory (".*")              dir)
;;         ("config" "~/mylisp/"       ("\\.js" "\\.el$")  nil)
;;         ("multi" (("~/mylisp/")
;;                   ("~/lisp/"))     ("\\.js" "\\.el$")  nil)
;;         ("emacs"  "d:/unix/emacs/"  (".*")              sub)
;;         ))

;; name : Input your favorite name
;; directory : Directory you'd like to search
;; mask : list of file-mask (regular expression).
;; option : usually option is nil. If option is "dir", you can select
;; directory like find-file. If option is "sub", you can select sub
;; directory.

;; Moreover you can also customize dmoccur-list as bellow.
;; (setq dmoccur-list
;;        '(
;;         ;; multi-directory can be setted if option is nil
;;         ("soft"
;;          (
;;           ("~/www/soft/")
;;           ("~/mylisp/")
;;           )
;;          ("\\.texi$") nil)
;;
;;          ;; In ~/mylisp, dmoccur search files recursively.
;;          ;; and dmoccur search files in ~/user.
;;          ("test-recursive"
;;           (("~/mylisp" t)
;;            ("~/user"))
;;           (".*") nil)
;;
;;          ;; In ~/mylisp, dmoccur search files recursively
;;          ;; but if (string-match ".+.txt" filename)
;;          ;; or (string-match ".+.el" filename) is t,
;;          ;; the file is *not* searched.
;;          ("ignore-txt"
;;           (("~/mylisp" t (".+.txt" ".+.el"))
;;            ("~/user"))
;;           (".*") nil)
;;
;;          ;; if option is dir (or sub),
;;          ;; you can set single directory only.
;;          ("dir-recursive" ((default-directory t)) (".*") dir)
;;          ))

;;; variables
;;;; moccur-split-word
;; non-nil means to input word splited by space. You can search
;; "defun color-moccur (regexp)" by "defun regexp" or "regexp defun".
;; You don't need to input complicated regexp.
;; And you can search "defun" in buffers whose name match "moccur".

;;;; dmoccur-use-list
;; if non-nill, M-x dmoccur is equal to C-u M-x dmoccur.

;;;; dmoccur-use-project
;; dmoccur need a name of dmoccur-list. If dmoccur-use-project is nil,
;; you have to type a name every time. If dmoccur-use-project is
;; non-nil and you searched current buffer by a name of dmoccur,
;; dmoccur use the name.

;;;; moccur-use-ee
;; non-nil means to display a result by ee.
;; ee: http://www.jurta.org/emacs/ee/
;; if you use allout.el, it's not displayed by ee.

;;; sample settings
;; (load "color-moccur")
;; (setq *moccur-buffer-name-exclusion-list*
;;       '(".+TAGS.+" "*Completions*" "*Messages*"
;;         "newsrc.eld" ".bbdb"))
;; (setq moccur-split-word t)
;; (setq dmoccur-use-list t)
;; (setq dmoccur-use-project t)
;; (setq dmoccur-list
;;       '(
;;         ("dir" default-directory (".*") dir)
;;         ("soft" "~/www/soft/" ("\\.texi$") nil)
;;         ("config" "~/mylisp/"  ("\\.js" "\\.el$") nil)
;;         ("1.99" "d:/unix/Meadow2/1.99a6/" (".*") sub)
;;         ))
;; (global-set-key "\C-x\C-o" 'occur-by-moccur)
;; (define-key Buffer-menu-mode-map "O" 'Buffer-menu-moccur)
;; (define-key dired-mode-map "O" 'dired-do-moccur)
;; (global-set-key "\C-c\C-x\C-o" 'moccur)
;; (global-set-key "\M-f" 'grep-buffers)
;; (global-set-key "\C-c\C-o" 'search-buffers)

;;; Furthermore
;;;; Function for regexp
;; (moccur-set-regexp)
;; function to set up regexp.
;; if moccur-split-word is non-nil,
;; *moccur-regexp-list* is list of regexp.
;; ex. "defun search" -> moccur-regexp-list = '("defun" "search")
;;     "^[ ]+( search" -> moccur-regexp-list = '("^[ ]+(" "search")

;;;; Search Function
;; (moccur-search-line <regexp>) : my original function.
;; basically (re-search-forward regexp nil t) (default)
;; If moccur-split-word is non-nil,
;; regexp for *moccur-search-line* is created by *moccur-set-regexp*
;; and *moccur-search-line* returns lines that include all of your search terms.
;; ex. (moccur-search-line "moccur defun line") matches
;; (defun moccur-search-line
;; and
;; (defun test () (moccur-search-line regexp))

;; (moccur-search-buffer (&optional regexp currbuf name))
;; Search <regexp> in <currbuf>, and output result.
;; Special feature
;; if moccur-split-word is non-nil, first word is special.
;; if first word is ";", that is, "; function",
;; moccur-search-buffer returns lines that is comment.
;; "! function" -> return lines that is function.
;; "" string" -> return lines that is string.
;; "/ comment" -> return lines that is comment.

;; moccur-set-regexp
;; convert regexp for moccur.

;; if moccur-use-keyword is non-nil and
;; keyword of moccur-search-keyword-alist is in regexp,
;; convert keyword to <regexp>
;; ex. "url" -> "[fht]*ttp://[-_.!~*'()a-zA-Z0-9;/?:@&=+$,%#]+"

;;; Idea and Todo

;; if you have idea or function you want,
;; please mail to akihisa@mail.ne.jp
;;
;; Document
;;   --> Add doc-string :)
;;   --> defvar to defcustom
;;
;; Search
;;   --> speed up
;;     --> restrict ee
;;       --> ee is slow, if count of matches is large
;;     --> moccur stop, if result is large
;;   --> search word
;;   --> use history like \1 (latest word)
;;   --> multiline search
;;
;; Buffers
;;   --> M-x dmoccur M-x moccur : many buffers are displayed
;;     --> I'd like to make variable to select buffers to search.
;;       --> e.g. if current buffer is emacs-lisp-mode,
;;          buffers which is emacs-lisp-mode are searched in moccur.
;;
;; Usability
;;   --> in moccur buffer, I have to type "lllllll" or "C-u 7 l".
;;       I'd like to change to displayed buffer like iswitch.
;;   --> matched buffer list
;;   --> add keybind (e.g. mouse...)
;;
;; moccur buffer
;;   --> Add sort method (now alphabetic order of buffer-name)
;;     --> probably
;;            buffers with same major-mode have relations...
;;            files in same directory have relations
;;            same extention?
;;
;; Bug
;;   --> with ee, can't undo step by step
;;
;; dmoccur
;;   --> very difficult
;;   --> Add dired-d:/home/memo/, when I searched in a directory.
;;   --> customize buffer-menu.
;;       with many buffers, buffer-menu overflow.

;;; History:

;; 2010/05/06
;; Add user variable (moccur-following-mode-toggle)

;; 2010/04/14
;; Bug fix
;; I changed next-line to forward-line in moccur-prev and moccur-next

;; 2010/02/23
;; Bug fix.
;; line 2199
;; (cdr (reverse inputs))) -> (reverse (cdr (reverse inputs))))
;; Thanks for patch!

;; 2008/7/27
;; Bug fix.
;; Add wheel mouse keybind.

;; 2008/7/25
;; Turned (back) on the key binding "t" to "moccur-toggle-view" command in moccur-grep-mode
;; Command "moccur-narrow-down" now also works in moccur-grep-mode.
;; Thanks Mr. Lin. Your changes are great.

;; 2007/12/22
;; Add command "g" (moccur-search-update) in *moccur* buffer
;; Abd bug fix (Thanks Mr. Lin)

;; 2007/12/16
;; Add command "u" (moccur-search-undo) in *moccur* buffer
;; Update regexp (Thanks Mr. Lin)

;; 2007/09/05
;; Remove obsolete function

;; 2005/11/16
;; Add option:moccur-grep-following-mode-toggle

;; 2004/09/23
;; Bug fix

;; 2004/04/30
;; Add moccur-grep and moccur-grep-find

;; 2004/01/13
;; defvar -> defcustom

;; 2004/01/05
;; Add moccur-search-keyword-alist

;; 2003/12/24
;; changed value of *moccur-buffer-name-exclusion-list*
;; New functions:isearch-moccur-all ("M-O" isearch-mode-map)
;; Add moccur-kill-buffer-after-goto

;; 2003/12/17
;; Bug fix: moccur-prev didn't move the cursor to another buffer.
;; Bug fix: if moccur-split-word is nil, special-word was used.

;; 2003/12/16
;; Update: moccur-color-view
;; Update: search-buffers-mode
;; RET: changed search-buffers-goto to search-buffers-call-moccur

;; 2003/12/15
;; Bug fix: moccur-split-string

;; 2003/12/12
;; dmoccur-list: can set file-name instead of directory
;; sample
;; (setq dmoccur-list
;;       '(
;;         ("memo" (("~/clmemo.txt") ;; filename
;;                    ("~/memo/" t)  ;; directory
;;                   ) (".*") nil nil)
;;         ))
;; Removed internal variable, moccur-regexp

;; New variable: moccur-special-word-list
;; if moccur-split-word is t, first word is special.

;; Example:
;; List lines matching regexp: ; moccur
;; This regexp matches comment only.

;; List lines matching regexp: " moccur
;; This regexp matches string only like "moccur"

;; List lines matching regexp: ! moccur
;; This regexp matches function only like defun moccur.

;; 2003/11/30
;; New functions:occur-by-moccur,isearch-moccur

;; 2003/11/28
;; Bug fix: if moccur-split-word is t, when "[" is searched, error

;; 2003/11/26
;; Bug fix: set kill-buffer-after-dired-do-moccur to t and run
;; dired-do-moccur. After that, if you run moccur, buffers were killed.
;; New function:
;; In dired buffer, if a directory is marked and you run
;; dired-do-moccur, you can search files in the directory.

;; 2003/11/25
;; Upgrade many functions. But I can't remember changes :)

;; 2003/06/13
;; Matsushita Akihisa <akihisa@mail.ne.jp> improved moccur.
;; Add dmoccur, dired-do-moccur, Buffer-menu-moccur, and so on.

;; 2002 or 2003
;; color-moccur 1.0 was released to the net

;; moccur 1.0 was released to the net on August 1st, 1991
;; csteury@dsd.es.com (Craig Steury) provided the exclusion list
;; facility, which was changed to to regexps and enhanced with a
;; inclusion list.

;;; Code:
(eval-when-compile (require 'cl))

(defgroup color-moccur nil
  "Customize color-moccur"
  :group 'matching)

;;; variables
;;;; user variables
(defface moccur-face
  '((((class color)
      (background dark))
     (:background "light grey" :bold t :foreground "Black"))
    (((class color)
      (background light))
     (:background "light cyan" :bold t))
    (t
     ()))
  "*Face used by moccur to show the text that matches."
  :group 'color-moccur
  )

(defface moccur-current-line-face
  '((((class color)
      (background dark))
     (:underline t))
    (((class color)
      (background light))
     (:underline t))
    (t
     ()))
  "*Face used by moccur."
  :group 'color-moccur
  )

(defcustom moccur-kill-moccur-buffer nil
  "*Non-nil means to kill *Moccur* buffer automatically when you exit *Moccur* buffer."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom moccur-use-migemo nil
  "*Non-nil means to use migemo (for Japanese). migemo.el is required."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom moccur-split-word nil
  "*Non-nil means means to input word splited by space.
You can search \"defun color-moccur (regexp)\" by \"defun regexp\" or
\"regexp defun\".  You don't need to input complicated regexp.  But
you can not input regexp including space.."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom color-moccur-default-ime-status t
  "*Non-nil means to inherit ime status."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom *moccur-buffer-name-exclusion-list*
  '("TAGS" "*Completions*" "*Messages*" "^[ ].+")
  "Contains a list of regexps which don't search by moccur.
Matching buffers are *not* searched for occurrences.  Per default, the
TAGS file is excluded."
  :group 'color-moccur
  :type '(repeat regexp)
  )

(defcustom *moccur-buffer-name-inclusion-list* '("[^ ].*")
  "Contains a list of regexps.  *Only* matching buffers are searched.
Per default, this var contains only a \".*\" catchall-regexp."
  :group 'color-moccur
  :type '(repeat regexp)
  )

(defcustom dmoccur-mask '(".*")
  "Mask for dmoccur."
  :group 'color-moccur
  :type '(repeat regexp)
  )

(defcustom dmoccur-maximum-size nil
  "*Maximum size (kB) of a buffer for dmoccur and moccur-grep(-find)."
  :group 'color-moccur
  :type '(choice
          number
          (const :tag "infinite" nil))
  )

(defcustom dmoccur-exclusion-mask
  '( ;; binary
    "\\.elc$" "\\.exe$" "\\.dll$" "\\.lib$" "\\.lzh$"
    "\\.zip$" "\\.deb$" "\\.gz$" "\\.pdf$" "\\.tar$"
    "\\.gz$" "\\.7z$" "\\.o$" "\\.a$" "\\.mod$"
    "\\.nc$" "\\.obj$" "\\.ai$" "\\.fla$" "\\.swf$"
    "\\.dvi$" "\\.pdf$" "\\.bz2$" "\\.tgz$" "\\.cab$"
    "\\.sea$" "\\.bin$" "\\.fon$" "\\.fnt$" "\\.scr$"
    "\\.tmp$" "\\.wrl$" "\\.Z$"
    ;; sound & movie
    "\\.aif$" "\\.aiff$"  "\\.mp3$"  "\\.wma$" "\\.mpg$"
    "\\.mpeg$" "\\.aac$" "\\.mid$"  "\\.au$"  "\\.avi$"  "\\.dcr$"
    "\\.dir$"  "\\.dxr$" "\\.midi$"  "\\.mov$"  "\\.ra$"  "\\.ram$"
    "\\.vdo$" "\\.wav$"
    ;; Microsoft
    "\\.doc$" "\\.xls$" "\\.ppt$" "\\.mdb$" "\\.adp$"
    "\\.wri$"
    ;; image
    "\\.jpg$" "\\.gif$" "\\.tiff$" "\\.tif$" "\\.bmp$"
    "\\.png$" "\\.pbm$" "\\.jpeg$" "\\.xpm$" "\\.pbm$"
    "\\.ico$" "\\.eps$" "\\.psd$"
    ;;etc
    "/TAGS$"
    ;; backup file
    "\\~$"
    ;; version control
    "\\.svn/.+" "CVS/.+" "\\.git/.+"
    )
  "*List of file extensions which are excepted to search by dmoccur and moccur-grep(-find)."
  :group 'color-moccur
  :type '(repeat regexp)
  )

(defcustom dmoccur-use-list nil
  "Non-nil means to use your favorite directory list."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom dmoccur-use-project nil
  "Non-nil means to use your favorite directory list."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom moccur-use-ee nil
  "Non-nil means to use ee. However, this feature doesn't work now"
  :group 'color-moccur
  :type 'boolean
  )

(defcustom kill-buffer-after-dired-do-moccur nil
  "Non-nil means to kill buffer after dired do moccur."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom dmoccur-list
  '(
    ;; name directory mask option
    ;; option = nil , dir , sub
    ("dir" default-directory (".*") dir)
    ("lisp" "~/mylisp/" ("\\.el" "\\.*texi") nil))
  "*List of directory which are searched by dmoccur."
  :group 'color-moccur
  :type '(repeat
          (list (string :tag "Name")
                (choice
                 (directory :tag "Directory")
                 (file :tag "Filename")
                 (symbol :tag "Variable")
                 (repeat :tag "Advanced setting"
                         (list
                          (choice
                           (directory :tag "Directory")
                           (symbol :tag "Variable"))
                          (boolean :tag "Recursively" nil)
                          (repeat :tag "File Mask"
                                  (regexp :tag "File Mask not to search")))))
                (repeat :tag "File Mask" :default nil
                        (regexp :tag "File Mask" ".*"))
                (choice :tag "Option" :default nil
                        (const :tag "Default" nil)
                        (const :tag "Directory" dir)
                        (const :tag "Subdirectory" sub))
                (choice :tag "Control Migemo and Split" :default nil
                        (const :tag "Default" nil)
                        (list (boolean :tag "Use Migemo" nil)
                              (boolean :tag "Split Regexp" nil)))
                (choice :tag "Default regexp" :default nil
                        (const :tag "Empty" nil)
                        (string :tag "Regexp" "")
                        (symbol :tag "Function to make regexp")))))

(defcustom moccur-maximum-displayed-with-color 500
  "Max number that is displayed with color."
  :group 'color-moccur
  :type 'number
  )

(defcustom dmoccur-recursive-search nil
  "Non-nil means to search files recursively."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom moccur-buffer-sort-method 'moccur-filepath-string<
  "Function to sort buffers."
  :group 'color-moccur
  :type 'symbol
  )

(defcustom moccur-special-word-list
  '(
    (";"
     moccur-face-initialization
     moccur-comment-check)
    ("/"
     moccur-face-initialization
     moccur-comment-check)
    ("\""
     moccur-face-initialization
     moccur-string-check)
    ("!"
     moccur-face-initialization
     moccur-function-check)
    (t ;; default
     moccur-default-initial-function
     moccur-default-check-function
     )
    )
  "Special-word function-to-initialize function-to-check."
  :group 'color-moccur
  :type '(repeat
          (list (choice (string :tag "Keyword")
                        (const :tag "Default" t))
                (symbol :tag "Function to initialize")
                (symbol :tag "Function to check")
                )))

(defcustom moccur-kill-buffer-after-goto nil
  "Non-nil means to kill *moccur* buffer after goto-occurrence."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom moccur-search-keyword-alist
  '(("url"  . "[fht]*ttp://[-_.!~*'()a-zA-Z0-9;/?:@&=+$,%#]+")
    ("mail" . "[^][<>@ \n]+@[-_!~*'()a-zA-Z0-9?@&=+$,%#]+\\.[-_.!~*'()a-zA-Z0-9?@&=+$,%#]+"))
  "*Alist of KEYWORD and REGEXP."
  :group 'color-moccur
  :type '(repeat
          (cons (string :tag "Keyword")
                (regexp :tag "Regexp"))))

(defcustom moccur-use-keyword nil
  "Non-nil means to use moccur-search-keyword-alist."
  :group 'color-moccur
  :type 'boolean
  )

(defcustom moccur-use-xdoc2txt
  (if
      (and
       (locate-library "xdoc2txt.exe" nil exec-path)
       (if (file-name-extension shell-file-name)
           (locate-library shell-file-name nil exec-path)
         (locate-library (concat shell-file-name ".exe") nil exec-path)))
      t
    nil)
  "Non-nil means to use xdoc2txt.
xdoc2txt is Windows software to convert Word/Excel/PDF etc to Text file.
http://www31.ocn.ne.jp/~h_ishida/xdoc2txt.html (Japanese site)"
  :group 'color-moccur
  :type 'boolean
  )

(defcustom moccur-grep-xdoc2txt-maximum-size 1000
  "*Maximum size (kB) of a buffer for xdoc2txt."
  :group 'color-moccur
  :type 'number
  )

(defcustom moccur-grep-xdoc2txt-exts '(
                                       "\\.rtf" "\\.doc" "\\.xls" "\\.ppt"
                                       "\\.jaw" "\\.jtw" "\\.jbw" "\\.juw"
                                       "\\.jfw" "\\.jvw" "\\.jtd" "\\.jtt"
                                       "\\.oas" "\\.oa2" "\\.oa3" "\\.bun"
                                       "\\.wj2" "\\.wj3" "\\.wk3" "\\.wk4"
                                       "\\.123" "\\.wri" "\\.pdf" "\\.mht")
  "*List of file extensions which are handled by xdoc2txt."
  :type '(repeat string)
  :group 'Meadow-Memo)

(defcustom moccur-following-mode-toggle t
  "When t, cursor motion in the moccur buffer causes
automatic display of the corresponding buffer location."
  :group 'color-moccur
  :type 'boolean)

(defcustom moccur-grep-following-mode-toggle t
  "When t, cursor motion in the moccur-grep buffer causes
automatic display of the corresponding source code location."
  :group 'color-moccur
  :type 'boolean)

(defcustom moccur-grep-default-word-near-point nil
  "When t, get a word near the point as default regexp string"
  :group 'color-moccur
  :type 'boolean)

(defvar moccur-grep-default-mask nil
  "File-mask string used for default in moccur-grep and moccur-grep-find")
(make-variable-buffer-local 'moccur-grep-default-mask)

;;; Internal variables
;;;; moccur
(defvar moccur-buffer-heading-regexp "^[-+ ]*Buffer: \\([^\r\n]+\\) File: \\([^\r\n]+\\)$"
  "Regexp for matching buffer heading line in moccur-mode buffer.")
(defvar moccur-grep-buffer-heading-regexp "^[-+ ]*Buffer: File (grep): \\([^\r\n]+\\)$"
  "Regexp for matching buffer heading line in moccur-grep-mode buffer.")
(defvar moccur-line-number-regexp "^[ ]*\\([0-9]+\\) "
  "Regexp for matching line numbers in moccur buffer.")
(defvar regexp nil)
(defvar moccur-list nil)
(defvar moccur-overlays nil)
(make-variable-buffer-local 'moccur-overlays)
(defvar moccur-current-line-overlays nil)
(defvar moccur-regexp-color "")
(defvar moccur-regexp-list nil)
(defvar moccur-file-name-regexp nil)
(defvar moccur-regexp-input "")
(defvar moccur-buffer-name "")
(defvar moccur-buffer-match-count nil)
(defvar moccur-before-buffer-name "")
(defvar moccur-line nil)
(defvar buffer-menu-moccur nil)
(defvar moccur-view-other-window t)
(make-variable-buffer-local 'moccur-view-other-window)
(defvar moccur-view-other-window-nobuf t)
(make-variable-buffer-local 'moccur-view-other-window-nobuf)
(defvar moccur-current-buffer nil)
(defvar moccur-buffer-position nil)
(make-variable-buffer-local 'moccur-buffer-position)
(defvar moccur-buffers nil)
(defvar moccur-match-buffers nil)
(defvar moccur-buffers-before-moccur nil)
(defvar moccur-matches nil)
(defvar moccur-mocur-buffer nil)
(defvar moccur-last-command nil)
(defvar moccur-windows-conf nil)
(defvar moccur-special-word nil)
(defvar moccur-fontlock-buffer nil)
(make-variable-buffer-local 'moccur-fontlock-buffer)
;;;; dmoccur
(defvar dmoccur-mask-internal nil)
(defvar dmoccur-history nil)
(defvar dmoccur-list-history nil)
(defvar dmoccur-buffer-project nil)
(make-variable-buffer-local 'dmoccur-buffer-project)
(defvar dmoccur-project-name nil)
(defvar dmoccur-project-list nil)
(defvar dmoccur-recursive-ignore-dir nil)
;;;; moccur-grep
(defvar moccur-grep-buffer-list nil)
(make-variable-buffer-local 'moccur-grep-buffer-list)
(defvar moccur-xdoc2txt-buffers nil)
(make-variable-buffer-local 'moccur-xdoc2txt-buffers)
(defvar moccur-run-meadow-onwin
  (and
   ;; run win32
   (and
    (null
     (or (equal system-type 'gnu/linux)
         (equal system-type 'usg-unix-v)))
    (or (equal system-type 'windows-nt)
        (equal system-type 'ms-dos)))
   ;; meadow
   (featurep 'meadow)))
(defvar moccur-grep-search-file-pos nil)

;;; For All Emacs
(defmacro string> (a b) (list 'not (list 'or (list 'string= a b)
                                         (list 'string< a b))))
(autoload 'migemo-get-pattern "migemo" "migemo-get-pattern" nil)

;;; For xemacs
(unless (fboundp 'match-string-no-properties)
  (defalias 'match-string-no-properties 'match-string))
(when (and (boundp 'running-xemacs) running-xemacs)
  (require 'overlay)
  (if (not (functionp 'line-beginning-position))
      (fset 'line-beginning-position 'point-at-bol))
  (if (not (functionp 'line-end-position))
      (fset 'line-end-position 'point-at-eol)))

;;; moccur and other packages
;;;; moccur + isearch
(defun isearch-moccur ()
  "Invoke `moccur' from isearch within `current-buffer'."
  (interactive)
  (let ((case-fold-search isearch-case-fold-search) (isearch-buffer (current-buffer)))
    (isearch-exit)
    (moccur-setup)
    (moccur-search
     (if isearch-regexp
         isearch-string
       (regexp-quote isearch-string))
     t
     (list isearch-buffer))))

(defun isearch-moccur-all ()
  "Invoke `moccur' from isearch in all buffers."
  (interactive)
  (let ((case-fold-search isearch-case-fold-search)
        (buffers (moccur-filter-buffers (buffer-list))))
    ;; sort
    (setq buffers (sort buffers moccur-buffer-sort-method))
    (isearch-exit)
    (moccur-setup)
    (moccur-search
     (if isearch-regexp
         isearch-string
       (regexp-quote isearch-string))
     t
     buffers)))

(define-key isearch-mode-map (kbd "M-o") 'isearch-moccur)
(define-key isearch-mode-map (kbd "M-O") 'isearch-moccur-all)

;;;; occur
(defun occur-by-moccur (regexp arg)
  "Use this instead of occur.
Argument REGEXP regexp.
Argument ARG whether buffers which is not related to files are searched."
  (interactive (list (moccur-regexp-read-from-minibuf)
                     current-prefix-arg))
  (moccur-setup)

  (setq moccur-regexp-input regexp)

  (let ((buffers (list (current-buffer))))
    (moccur-search regexp t buffers)))

;;; moccur:function
;;;; utility
(defun moccur-filepath-string< (buf1 buf2)
  "String< by function `buffer-file-name'.
Argument BUF1 BUFFER.
Argument BUF2 BUFFER."
  (if (and (buffer-file-name buf1)
           (buffer-file-name buf2))
      (string< (buffer-file-name buf1) (buffer-file-name buf2))
    (if (buffer-file-name buf1)
        buf1
      (if (buffer-file-name buf2)
          buf2
        (string< (buffer-name buf1) (buffer-name buf2))))))

(defun moccur-buffer-string< (buf1 buf2)
  "String< by `buffer-name'.
Argument BUF1 BUFFER.
Argument BUF2 BUFFER."
  (string< (buffer-name buf1) (buffer-name buf2)))

(defun moccur-buffer-string> (buf1 buf2)
  "String> by `buffer-name'.
Argument BUF1 BUFFER.
Argument BUF2 BUFFER."
  (string> (buffer-name buf1) (buffer-name buf2)))

(defun moccur-buffer-in-list-p (buffer-name buffer-name-regexps)
  "Return t, if BUFFER-NAME match BUFFER-NAME-REGEXPS (list)."
  (cond ((null buffer-name-regexps) nil)
        ((eq (string-match (car buffer-name-regexps) buffer-name)
             0) t)
        (t (moccur-buffer-in-list-p
            buffer-name (cdr buffer-name-regexps)))))

(defun moccur-filter-buffers (buffer-list)
  "Return BUFFER-LIST which is filtered by some variables."
  (let ((moccur-buffers nil))
    (while buffer-list
      (if (and (moccur-buffer-in-list-p
                (buffer-name (car buffer-list))
                *moccur-buffer-name-inclusion-list*)
               (not (moccur-buffer-in-list-p
                     (buffer-name (car buffer-list))
                     *moccur-buffer-name-exclusion-list*)))
          (setq moccur-buffers
                (cons (car buffer-list)
                      moccur-buffers)))
      (setq buffer-list (cdr buffer-list)))
    moccur-buffers))

(defun moccur-kill-buffer-func ()
  (when (get-buffer "*Moccur*") ;; there ought to be just one of these
    (let ((cur-buffer (current-buffer)))
      (save-excursion
        (set-buffer "*Moccur*")
        ;; remove current buffer from moccur-grep-buffer-list so it won't get killed in
        ;; moccur-grep-sync-kill-buffers
        (setq moccur-grep-buffer-list (remq cur-buffer moccur-grep-buffer-list))))
    (kill-buffer "*Moccur*"))
  (if (get-buffer "*ee-outline*/*Moccur*")
      (kill-buffer "*ee-outline*/*Moccur*")))

(defun moccur-kill-buffer (arg)
  "Kill buffers related moccur."
  (if arg
      (moccur-kill-buffer-func)
    (if moccur-kill-moccur-buffer
        (moccur-kill-buffer-func)
      (bury-buffer))))

(defun moccur-bury-buffer ()
  "Kill buffers related moccur."
  (if (get-buffer "*Moccur*") ;; there ought to be just one of these
      (bury-buffer (get-buffer "*Moccur*")))
  (if (get-buffer "*ee-outline*/*Moccur*")
      (bury-buffer (get-buffer "*ee-outline*/*Moccur*"))))

(autoload 'ee-outline "ee-autoloads" nil t)
(defun moccur-setup ()
  "Initialization of moccur."
  ;;(setq moccur-last-command 'moccur)
  (if moccur-use-migemo
      (require 'migemo))
  (if moccur-use-ee
      (require 'ee-autoloads))
  (if (string= "*Moccur*"
               (buffer-name (current-buffer)))
      (moccur-quit))
  (moccur-kill-buffer t)
  (setq moccur-current-buffer (current-buffer))
  (setq moccur-windows-conf (current-window-configuration)))

(defun moccur-insert-heading(moccur-regexp-input)
  "Insert the 'Lines matching' heading in *Moccur* buffer, with the user input regexp
 displayed in font-lock-variable-name-face face."
  (let (pt)
    (setq pt (point))
    (insert "Lines matching")
    (when moccur-split-word
      (insert " (split words)"))
    (insert ": ")
    (put-text-property pt (point) 'face 'font-lock-keyword-face)
    (setq pt (point))
    (insert moccur-regexp-input "\n")
    (put-text-property pt (point) 'face 'font-lock-variable-name-face)))

(defun moccur-file-size< (filename maxsize)
  (if
      (or
       (not maxsize)
       (> (* 1000 maxsize)
          (nth 7 (file-attributes filename))))
      t
    nil))

;;;; color and overlay
(defun moccur-remove-overlays-on-all-buffers (&optional beg end length)
  "Remove all overlays in all buffers.
Optional argument BEG
 the positions of the beginning of the range of changed text
Optional argument END
 the positions of the end of the range of changed text
Optional argument LENGTH
 the length in bytes of the pre-change text replaced by that range."
  (interactive "p")
  (if moccur-current-line-overlays
      (progn
        (delete-overlay moccur-current-line-overlays)
        (setq moccur-current-line-overlays nil)))
  (save-excursion
    (let (ov buf (buflist (buffer-list)))
      (while buflist
        (setq buf (car buflist))
        (setq buflist (cdr buflist))
        (when (and buf
                   (buffer-live-p buf))
          (set-buffer buf)
          (when (not (memq major-mode '(moccur-mode moccur-grep-mode)))
            (while moccur-overlays
              (delete-overlay (car moccur-overlays))
              (setq moccur-overlays (cdr moccur-overlays))))
          (remove-hook 'after-change-functions
                       'moccur-remove-overlays-on-all-buffers)
          (when moccur-buffer-position
            (goto-char moccur-buffer-position)
            (setq moccur-buffer-position nil)))))))

(defun moccur-buffer-hide-region (start end)
  (let ((o (make-overlay start end)))
    (overlay-put o 'invisible 'moccur)
    (overlay-put o 'isearch-open-invisible
                 'outline-isearch-open-invisible)))

(defun moccur-buffer-color ()
  "Put overlays in *moccur* buffer."
  (let ((ov) (count 0))
    (save-excursion
      (goto-char (point-min))
      (while (and (re-search-forward moccur-line-number-regexp nil t)
                  (or (not moccur-maximum-displayed-with-color)
                      (< count moccur-maximum-displayed-with-color)))
        (progn
          (save-restriction
            (narrow-to-region (point) (line-end-position))
            (while (re-search-forward moccur-regexp-color nil t)
              (setq count (+ count 1))
              (setq ov (make-overlay (match-beginning 0)
                                     (match-end 0)))
              (overlay-put ov 'face 'moccur-face)
              (overlay-put ov 'priority 0)
              (setq moccur-overlays (cons ov moccur-overlays))))
          (when (> (+ 6 (save-excursion (end-of-line) (current-column)))
                   (if (and (boundp 'running-xemacs) running-xemacs)
                       (frame-width)
                     (frame-width)))
            (save-excursion
              (beginning-of-line)
              (re-search-forward moccur-line-number-regexp (line-end-position) t)
              (save-restriction
                (narrow-to-region (point) (line-end-position))
                (let ((end-pt (point)) (st (point)) (match-end-pt nil))
                  (while (re-search-forward moccur-regexp-color (line-end-position) t)
                    (setq st (match-beginning 0))
                    (setq match-end-pt (match-end 0))
                    (cond
                     ((and
                       (> (length (buffer-substring-no-properties
                                   end-pt st))
                          10)
                       (< end-pt (- st 5)))
                      (moccur-buffer-hide-region end-pt (- st 5))
                      (setq end-pt (+ 5 match-end-pt)))
                     (t
                      (setq end-pt (+ 5 match-end-pt))
                      (goto-char end-pt)
                      )))
                  (end-of-line)
                  (if (and
                       (> (line-end-position) end-pt)
                       (> (length (buffer-substring-no-properties
                                   end-pt (line-end-position)))
                          10))
                      (moccur-buffer-hide-region end-pt (- (line-end-position) 5)))))))
          )))))

(defun moccur-color-view ()
  "Put overlays to matched texts."
  (let ((ov) (count 0))
    (if (and moccur-buffer-name
             (get-buffer moccur-buffer-name))
        (progn
          (set-buffer (get-buffer moccur-buffer-name))
          (when moccur-current-line-overlays
            (delete-overlay moccur-current-line-overlays)
            (setq moccur-current-line-overlays nil))

          (save-excursion
            (goto-char (point-min))
            (moccur-special-word-call-initialize-function)
            (while (and
                    (moccur-search-line (car moccur-regexp-list))
                    (or (not moccur-maximum-displayed-with-color)
                        (< count moccur-maximum-displayed-with-color)))
              (when (moccur-special-word-call-check-function)
                (beginning-of-line)
                (while (and
                        (re-search-forward
                         moccur-regexp-color (line-end-position) t)
                        (or (not moccur-maximum-displayed-with-color)
                            (< count moccur-maximum-displayed-with-color)))
                  (progn
                    (setq count (+ count 1))
                    (setq ov (make-overlay (match-beginning 0)
                                           (match-end 0)))
                    (overlay-put ov 'face 'moccur-face)
                    (overlay-put ov 'priority 0)
                    (setq moccur-overlays (cons ov moccur-overlays)))))))
          (set-buffer moccur-mocur-buffer)))))

(defun moccur-color-current-line ()
  "Underline where the cursor is."
  (if (not moccur-current-line-overlays)
      (setq moccur-current-line-overlays
            (make-overlay
             (line-beginning-position) (1+ (line-end-position))))
    (move-overlay moccur-current-line-overlays
                  (line-beginning-position) (1+ (line-end-position))))
  (overlay-put moccur-current-line-overlays
               'face 'moccur-current-line-face))

;;;; display other window
(defun moccur-get-info ()
  "Gets buffer name and line."
  (setq moccur-view-other-window-nobuf t)
  (setq moccur-buffer-name nil)
  (let ((end-pt) (start-pt) (file nil) (buffer nil) (str nil) (buf nil)
        (buflst (buffer-list)))
    ;;for moccur-grep
    (when moccur-grep-following-mode-toggle
      (save-window-excursion
        (save-excursion
          (moccur-grep-goto)
          (setq buf (current-buffer))))
      (if (or
           (memq buf buflst)
           (memq buf moccur-grep-buffer-list))
          ()
        (setq moccur-grep-buffer-list
              (cons buf moccur-grep-buffer-list))))
    ;;for moccur-grep end
    (save-excursion
      (end-of-line)
      (if (re-search-backward
           "^[-+ ]*Buffer:[ ]*\\([^\r\n]*\\) File\\([^:/\r\n]*\\):[ ]*\\([^\r\n]+\\)$" nil t)
          (progn
            (setq start-pt (point))
            (setq buffer
                  (match-string-no-properties 1))
            (setq str (match-string-no-properties 2))
            (setq file (match-string-no-properties 3))
            (cond
             ((string-match "grep" str)
              (if (moccur-grep-xdoc2txt-p file)
                  (setq moccur-buffer-name (moccur-grep-binary-file-view file))
                (if (get-file-buffer file)
                    (setq moccur-buffer-name
                          (buffer-name
                           (get-file-buffer file))))))
             (t
              (setq moccur-buffer-name buffer))))
        (setq start-pt (point-min))))

    (save-excursion
      (end-of-line)
      (if (re-search-forward
           "^[-+ ]*Buffer: " nil t)
          (progn
            (beginning-of-line)
            (setq end-pt (point)))
        (setq end-pt (point-max))))

    (save-excursion
      (setq moccur-buffer-match-count 0)
      (goto-char start-pt)
      (while (re-search-forward moccur-line-number-regexp end-pt t)
        (setq moccur-buffer-match-count (+ 1 moccur-buffer-match-count))))

    (save-excursion
      (end-of-line)
      (if (re-search-backward moccur-line-number-regexp (line-beginning-position) t)
          (setq moccur-line (buffer-substring
                             (match-beginning 1)
                             (match-end 1)))
        (setq moccur-line "1")))
    (if (and moccur-buffer-name
             (get-buffer moccur-buffer-name)
             (buffer-live-p (get-buffer moccur-buffer-name)))
        ()
      (setq moccur-view-other-window-nobuf nil))))

(defun moccur-color-check-view ()
  "If a matched buffer exists, the buffer is displayed."
  (if (and moccur-buffer-name
           (get-buffer moccur-buffer-name))
      (progn
        (set-buffer (get-buffer moccur-buffer-name))
        (if moccur-overlays
            ()
          (moccur-color-view))
        (set-buffer moccur-mocur-buffer))))

(defun moccur-view-file ()
  "Display the matched buffer to other window."
  (if (string= moccur-before-buffer-name moccur-buffer-name)
      (moccur-color-check-view)
    (if moccur-current-line-overlays
        (progn
          (delete-overlay moccur-current-line-overlays)
          (setq moccur-overlays nil)))
    (moccur-color-view))

  (switch-to-buffer-other-window
   (get-buffer moccur-buffer-name))
  (goto-line (string-to-number moccur-line))
  (if (re-search-forward moccur-regexp-color (line-end-position) t)
      ()
    (goto-line (string-to-number moccur-line)))

  ;; color
  (moccur-color-current-line)

  (setq moccur-before-buffer-name moccur-buffer-name)
  (switch-to-buffer-other-window moccur-mocur-buffer))

(defun moccur-scroll-file (arg)
  "Scroll up the matched buffer.
If ARG is non-nil, scroll down the buffer."
  (switch-to-buffer-other-window
   (get-buffer moccur-buffer-name))
  (condition-case nil
      (if arg
          (scroll-down)
        (scroll-up))
    (error
     nil))

  ;; color
  (moccur-color-current-line)

  (setq moccur-before-buffer-name moccur-buffer-name)
  (switch-to-buffer-other-window moccur-mocur-buffer))

(defun moccur-internal-beginning-of-buffer (arg)
  "Begging-of-buffer in the matched buffer.
Argument ARG If non-nil, `end-of-buffer'."
  (switch-to-buffer-other-window
   (get-buffer moccur-buffer-name))
  (condition-case nil
      (if arg
          (goto-char (point-max))
        (goto-char (point-min)))
    (error
     nil))

  ;; color
  (moccur-color-current-line)

  (setq moccur-before-buffer-name moccur-buffer-name)
  (switch-to-buffer-other-window moccur-mocur-buffer))

;;;; minibuffer
(defvar dmoccur-default-word nil)
(defun moccur-set-default-word ()
  "Set default word to regexp."
  (cond
   ((and dmoccur-project-name
         (nth 5 (assoc (car dmoccur-project-name) dmoccur-list)))
    (setq dmoccur-default-word
          (if (nth 5 (assoc (car dmoccur-project-name) dmoccur-list))
              (nth 5 (assoc (car dmoccur-project-name) dmoccur-list))
            ""))
    (if (stringp dmoccur-default-word)
        dmoccur-default-word
      (condition-case err
          (funcall dmoccur-default-word)
        (error
         ""))))
   ((and
     (or (and (boundp 'mark-active) mark-active)
         (and (fboundp 'region-exists-p) (region-exists-p)))
     (< (- (region-end) (region-beginning)) 50))
    (buffer-substring-no-properties
     (region-beginning) (region-end)))
   ((> (length (thing-at-point 'symbol)) 0)
    (thing-at-point 'symbol))
   ((> (length (thing-at-point 'word)) 0)
    (thing-at-point 'word))
   (t
    (if (and regexp-history (stringp (car regexp-history)))
        (car regexp-history)
      ""))))

(defun moccur-regexp-read-from-minibuf ()
  "Read regexp from minibuffer."
  (let (default input lst (search-lst nil) dmoccur-default-word)
    (setq default (moccur-set-default-word))
    (setq input
          (read-from-minibuffer
           "List lines matching regexp: "
           ;;(format "List lines matching regexp (default `%s'): "
           ;;        default)
           (cons default 0) ;; initial string
           nil nil
           'regexp-history
           (if (and (boundp 'running-xemacs) running-xemacs)
               nil
             default)
           (if (and (boundp 'running-xemacs) running-xemacs)
               default
             color-moccur-default-ime-status)))
    (when (and (equal input "") default)
      (setq input default)
      (setq regexp-history (cons input regexp-history)))
    (when moccur-split-word
      (setq lst (moccur-split-string input))
      (while lst
        (if (string-match "^b:" (car lst))
            ()
          (setq search-lst (cons (car lst) search-lst)))
        (setq lst (cdr lst)))
      (if (= 0 (length search-lst))
          (error "Input search string")))
    input))

;;;; search function
(defun moccur-search-line (regexp)
  "Corresponding to re-search-line.
Argument REGEXP REGEXP to search."
  (let ((lst moccur-regexp-list)
        (split-match 0))
    ;; if return nil, moccur search next buffer
    (cond
     ((and moccur-split-word lst)
      ;; search method for split-word
      (while (and (not (= (length moccur-regexp-list) split-match))
                  (re-search-forward regexp nil t))
        (setq lst moccur-regexp-list)
        (setq split-match 0)
        (while lst
          (save-excursion
            (beginning-of-line)
            (if (re-search-forward (car lst) (line-end-position) t)
                (setq split-match (+ split-match 1)))
            (setq lst (cdr lst)))))
      (if (= (length moccur-regexp-list) split-match)
          t
        nil))
     (t
      ;; defualt
      (re-search-forward regexp nil t)))))

(make-variable-buffer-local 'moccur-buffer-position)
(defun moccur-search-buffer (&optional regexp currbuf name)
  "Search REGEXP in CURRBUF.
If NAME exists, `moccur-search-buffer' works as grep."
  (let ((match-str nil) fname)
    (set-buffer currbuf)
    (setq moccur-buffer-position (point))

    ;;(make-local-hook 'after-change-functions)
    ;;(remove-hook 'after-change-functions 'moccur-remove-overlays)
    (add-hook 'after-change-functions 'moccur-remove-overlays-on-all-buffers nil t)

    (goto-char (point-min))

    (moccur-special-word-call-initialize-function)

    (while (moccur-search-line regexp)
      (when (moccur-special-word-call-check-function)
        (setq moccur-matches (+ moccur-matches 1))
        (let* ((linenum (count-lines
                         (save-restriction (widen) (point-min)) (point)))
               (tag (format "\n%5d " linenum)))
          (put-text-property 0 (length tag) 'face 'font-lock-constant-face tag)
          (setq
           match-str
           (cons
            (concat tag
                    (buffer-substring
                     (line-beginning-position) (line-end-position)))
            match-str))
          (forward-line nil))))
    (setq match-str (reverse match-str))
    (save-excursion
      (set-buffer moccur-mocur-buffer)
      (if (not match-str)
          nil
        (let (pt)
          (cond
           (name
            (setq pt (point))
            (insert "Buffer: File (grep): ")
            (put-text-property pt (point) 'face 'font-lock-keyword-face)
            (setq pt (point))
            (insert name "\n")
            (put-text-property pt (point) 'face 'font-lock-variable-name-face))
           (t
            (if (buffer-file-name currbuf)
                (setq fname (buffer-file-name currbuf))
              (setq fname "Not file"))
            (setq pt (point))
            (insert "Buffer: ")
            (put-text-property pt (point) 'face 'font-lock-keyword-face)
            (setq pt (point))
            (insert (buffer-name currbuf))
            (put-text-property pt (point) 'face 'font-lock-variable-name-face)
            (setq pt (point))
            (insert " File: ")
            (put-text-property pt (point) 'face 'font-lock-keyword-face)
            (setq pt (point))
            (insert fname "\n")
            (put-text-property pt (point) 'face 'font-lock-variable-name-face))))

        (while match-str
          (insert (car match-str))
          (setq match-str (cdr match-str)))
        (insert "\n\n")
        t))))

(defvar moccur-searched-list nil)
(defun moccur-search (regexp arg buffers)
  "Search REGEXP in BUFFERS (list).
If ARG is non-nil, also search buffer that doesn't have file name"

  (when (or
         (not regexp)
         (string= regexp ""))
    (error "No search word specified!"))
  ;; initialize
  (let ((lst
         (list
          regexp arg buffers)))
    (if (equal lst (car moccur-searched-list))
        ()
      (setq moccur-searched-list
            (cons
             (list
              regexp arg buffers)
             moccur-searched-list))))

  (setq moccur-special-word nil)
  (moccur-set-regexp)
  (moccur-set-regexp-for-color)

  ;; variable reset
  (setq dmoccur-project-name nil)
  (setq moccur-matches 0)
  (setq moccur-match-buffers nil)
  (setq moccur-regexp-input regexp)
  (if (string= (car regexp-history) moccur-regexp-input)
      ()
    (setq regexp-history
          (cons moccur-regexp-input regexp-history)))

  (save-excursion
    (setq moccur-mocur-buffer (generate-new-buffer "*Moccur*"))
    (set-buffer moccur-mocur-buffer)
    (moccur-insert-heading moccur-regexp-input)
    (setq moccur-buffers buffers)

    ;; search all buffers
    (while buffers
      (if (and
           (car buffers)
           (buffer-live-p (car buffers))
           ;; if b:regexp exists,
           (if (and moccur-file-name-regexp
                    moccur-split-word)
               (string-match moccur-file-name-regexp
                             (buffer-name (car buffers)))
             t))
          (if (and (not arg)
                   (not (buffer-file-name (car buffers))))
              (setq buffers (cdr buffers))
            (if (moccur-search-buffer (car moccur-regexp-list) (car buffers))
                (setq moccur-match-buffers
                      (cons (car buffers) moccur-match-buffers)))
            (setq buffers (cdr buffers)))
        ;; illegal buffer
        (setq buffers (cdr buffers))))
    (if (> moccur-matches 0)
        (save-excursion
          (set-buffer moccur-mocur-buffer)
          (delete-other-windows)
          (moccur-mode)
          ;; highlight Moccur buffer
          (moccur-buffer-color)
          (setq buffer-undo-list nil)

          (moccur-ee-start)
          (setq buffer-undo-list nil)

          ;; move cursor to the first matching text
          (set-buffer moccur-mocur-buffer)

          (goto-char (point-min))
          (forward-line 2)

          (beginning-of-line)
          (re-search-forward moccur-line-number-regexp nil t)
          (re-search-forward (car moccur-regexp-list) nil t)

          (moccur-get-info)

          (setq moccur-before-buffer-name moccur-buffer-name)
          (moccur-color-view)

          ;; preview file
          (moccur-view-file)
          (pop-to-buffer moccur-mocur-buffer)
          (message "%d matches" moccur-matches)
          t)
      (message "no matches")
      (setq moccur-searched-list
            (cdr moccur-searched-list))
      (moccur-kill-buffer t)
      (moccur-remove-overlays-on-all-buffers)
      nil)))

(defun moccur-search-undo ()
  (interactive)
  (moccur-setup)
  (setq moccur-last-command 'moccur-search-undo)
  (unless (nth 1 moccur-searched-list)
    (error "No undo information"))
  (setq moccur-searched-list (cdr moccur-searched-list))
  (let ((buffers (car (cdr (cdr (car moccur-searched-list)))))
        (regexp (car (car moccur-searched-list)))
        (arg (car (cdr (car moccur-searched-list)))))
    ;; sort
    (setq buffers (sort buffers moccur-buffer-sort-method))
    (moccur-search regexp arg buffers)))

(defun moccur-search-update ()
  (interactive)
  (moccur-setup)
  (setq moccur-last-command 'moccur-search-update)
  (let ((buffers (car (cdr (cdr (car moccur-searched-list)))))
        (regexp (car (car moccur-searched-list)))
        (arg (car (cdr (car moccur-searched-list)))))
    ;; sort
    (setq buffers (sort buffers moccur-buffer-sort-method))
    (moccur-search regexp arg buffers)))

;;;; search word
(defun moccur-split-string (string &optional separators)
  "Splits STRING into substrings where there are matches for SEPARATORS.
Each match for SEPARATORS is a splitting point.
The substrings between the splitting points are made into a list
which is returned.
If SEPARATORS is absent, it defaults to \"[ ]+\".

But if substring is invalid regexp, this function doesn't split into
substrings.

Example:
 moccur split string -> '(\"moccur\" \"split\" \"string\")
 moccur [a-z ]+ search -> '(\"moccur\" \"[a-z ]+\" \"search\")"

  ;; strip whitespace from end of string
  (setq string
        (substring
         string
         0
         (string-match "[ ]+$" string)))
  (while (string-match "^[ ]+" string)
    (setq string
          (substring
           string
           1)))
  (let* ((rexp (or separators "[ ]+"))
         (lst (split-string string rexp))
         (new-lst nil)
         (current-regexp nil)
         (regexp-p nil)
         (regexp nil))

    (when (and
           moccur-split-word
           (assoc (car lst) moccur-special-word-list)
           (> (length lst) 1))
      (setq moccur-regexp-list (cdr moccur-regexp-list))
      (setq moccur-special-word (car lst))
      (setq lst (cdr lst)))

    (while lst
      (setq current-regexp (concat
                            regexp
                            (if regexp
                                " ")
                            (car lst)))
      (setq regexp nil)
      (setq lst (cdr lst))
      (setq regexp-p t)
      (condition-case err
          (string-match current-regexp "test")
        (error
         (setq regexp-p nil)))

      (cond
       ((and moccur-use-keyword
             regexp-p
             (assoc current-regexp moccur-search-keyword-alist))
        (setq new-lst
              (cons
               (cdr (assoc current-regexp moccur-search-keyword-alist))
               new-lst)))
       (regexp-p
        (setq new-lst (cons current-regexp new-lst)))
       (t
        (setq regexp (concat current-regexp
                             (if regexp " ") regexp)))))

    (if regexp
        (setq new-lst
              (append new-lst
                      (mapcar '(lambda (string)
                                 (if (and moccur-use-keyword
                                          (assoc string moccur-search-keyword-alist))
                                     (cdr (assoc string moccur-search-keyword-alist))
                                   (regexp-quote string)))
                              (split-string regexp)))))
    (if (and
         (not new-lst)
         (not regexp))
        (error "Invalid regexp"))

    (setq new-lst (reverse new-lst))

    new-lst))

(defun moccur-word-split (regexp &optional norestrict)
  "Splits REGEXP into substrings."
  (setq moccur-file-name-regexp nil)
  (let ((lst (moccur-split-string regexp))
        (regexp-list nil))

    (while lst
      (if (and (not norestrict)
               moccur-split-word (string-match "^b:" (car lst)))
          (setq moccur-file-name-regexp
                (cons (substring (car lst) 2) moccur-file-name-regexp))
        (setq regexp-list
              (cons
               (if moccur-use-migemo
                   (cond
                    ((string-match "^r:" (car lst))
                     (substring (car lst) 2))
                    ((not (string= (car lst) (regexp-quote (car lst))))
                     (car lst))
                    (t
                     (migemo-get-pattern (car lst))))
                 (car lst))
               regexp-list)))
      (setq lst (cdr lst)))

    (if (and moccur-split-word moccur-file-name-regexp)
        (progn
          (setq lst moccur-file-name-regexp)
          (setq moccur-file-name-regexp (concat "\\(" (car lst)))
          (setq lst (cdr lst))
          (while lst
            (setq moccur-file-name-regexp
                  (concat moccur-file-name-regexp
                          "\\|"
                          (car lst)))
            (setq lst (cdr lst)))
          (setq moccur-file-name-regexp
                (concat moccur-file-name-regexp "\\)"))))
    regexp-list))

(defun moccur-set-regexp ()
  "Set `moccur-regexp-list' and `moccur-file-name-regexp' from user regexp."
  (setq moccur-regexp-list nil)
  (setq moccur-file-name-regexp nil)

  (if moccur-split-word
      (setq moccur-regexp-list (moccur-word-split regexp))
    (if moccur-use-migemo
        (cond
         ((string-match "^r:" regexp)
          (setq moccur-regexp-list (list (substring regexp 2))))
         ((not (string= regexp (regexp-quote regexp)))
          (setq moccur-regexp-list (list regexp)))
         (t
          (setq moccur-regexp-list (list (migemo-get-pattern regexp)))))
      (setq moccur-regexp-list (list regexp)))))

(defun moccur-set-regexp-for-color ()
  "Make regexp for coloring up."
  (let ((list (cdr moccur-regexp-list)))
    (if moccur-split-word
        (progn
          (setq moccur-regexp-color (concat
                                     "\\(" (car moccur-regexp-list)))
          (while list
            (setq moccur-regexp-color
                  (concat moccur-regexp-color
                          "\\|"
                          (car list)))
            (setq list (cdr list)))
          (setq moccur-regexp-color
                (concat moccur-regexp-color "\\)")))
      (setq moccur-regexp-color (car moccur-regexp-list)))))

;;;; moccur special word
;;;;; basic functions
(defun moccur-special-word-call-initialize-function ()
  "Initialize function for special word function."
  (cond
   ((and moccur-split-word
         moccur-special-word)
    (if (nth 1 (assoc moccur-special-word moccur-special-word-list))
        (funcall
         (nth 1 (assoc moccur-special-word moccur-special-word-list)))))
   (t
    (if (nth 1 (assoc t moccur-special-word-list))
        (funcall
         (nth 1 (assoc t moccur-special-word-list)))))))

(defun moccur-special-word-call-check-function ()
  "Function to check whether the matched text is acceptable."
  (cond
   ((and moccur-split-word
         moccur-special-word)
    (or
     (and (assoc moccur-special-word moccur-special-word-list)
          (nth 2 (assoc moccur-special-word moccur-special-word-list))
          (funcall
           (nth 2 (assoc moccur-special-word moccur-special-word-list))))
     (not
      (assoc moccur-special-word moccur-special-word-list))
     (not
      (nth 2 (assoc moccur-special-word moccur-special-word-list)))))
   (t
    (if (nth 2 (assoc t moccur-special-word-list))
        (funcall
         (nth 2 (assoc t moccur-special-word-list)))
      t))))

;;;;; functions
(defun moccur-face-check (facename)
  "Check whether the face of current point is FACENAME."
  (let ((face
         (save-excursion
           (forward-char -1)
           (get-text-property (point) 'face))))
    (cond
     ((listp face)
      (memq facename face))
     (t
      (string=
       facename face)))))

(make-variable-buffer-local 'moccur-fontlock-buffer)
(defun moccur-face-initialization ()
  "Call 'font-lock-default-fontify-buffer'."
  (let ((font-lock-support-mode 'fast-lock-mode))
    (if moccur-fontlock-buffer
        ()
      (setq moccur-fontlock-buffer t)
      (font-lock-default-fontify-buffer))))

(defun moccur-default-initial-function ()
  ())

(defun moccur-default-check-function ()
  t)

(defun moccur-comment-check ()
  (moccur-face-check 'font-lock-comment-face))

(defun moccur-string-check ()
  (moccur-face-check 'font-lock-string-face))

(defun moccur-function-check ()
  (cond
   ((string= major-mode 'texinfo-mode)
    (moccur-face-check 'texinfo-heading-face))
   ((string= major-mode 'change-log-mode)
    (moccur-face-check 'change-log-file-face))
   ((string= major-mode 'outline-mode)
    (if (save-excursion
          (re-search-backward
           (concat "^" outline-regexp) (line-beginning-position) t))
        t
      nil))
   (t
    (or
     (moccur-face-check 'font-lock-function-name-face)
     (moccur-face-check 'font-lock-variable-name-face))
    )))

;;;; ee
(defun moccur-ee-start ()
  (let ((str (buffer-substring-no-properties
              (line-beginning-position) (line-end-position))))
    (when (and (not (featurep 'allout))
               moccur-use-ee
               (buffer-live-p (get-buffer "*Moccur*")))
      (if (buffer-live-p (get-buffer "*ee-outline*/*Moccur*"))
          (kill-buffer (get-buffer "*ee-outline*/*Moccur*")))

      (switch-to-buffer (get-buffer "*Moccur*"))
      (ee-outline)
      (re-search-forward (regexp-quote str) nil t)
      (moccur-mode t)
      ;;(use-local-map moccur-mode-map)
      (setq moccur-mocur-buffer (current-buffer))
      ;; highlight Moccur buffer
      (moccur-buffer-color))))

(defun moccur-switch-buffer (buf)
  (interactive)
  (when (and moccur-use-ee (not (featurep 'allout)))
    (if (string= 'normal buf)
        (if (get-buffer "*Moccur*")
            (switch-to-buffer (get-buffer "*Moccur*")))
      (if (get-buffer "*ee-outline*/*Moccur*")
          (switch-to-buffer (get-buffer "*ee-outline*/*Moccur*"))))))

;;;; interactive
(defun moccur (regexp arg)
  "Show all lines of all buffers containing a match for REGEXP.
The lines are shown in a buffer named *Moccur*.
It serves as a menu to find any of the occurrences in this buffer.
\\[describe-mode] in that buffer will explain how."
  (interactive (list (moccur-regexp-read-from-minibuf)
                     current-prefix-arg))

  (moccur-setup)
  (setq moccur-last-command 'moccur)

  (let ((buffers (moccur-filter-buffers (buffer-list))))
    ;; sort
    (setq buffers (sort buffers moccur-buffer-sort-method))
    (moccur-search regexp arg buffers)))

(defun moccur-grep-correspond-ext-p (filename list)
  (let ((ret nil))
    (while list
      (when (string-match (car list) filename)
        (setq ret t))
      (setq list (cdr list)))
    ret))

;;; moccur-grep
(defun moccur-grep-xdoc2txt-p (filename)
  (if (and
       moccur-run-meadow-onwin
       moccur-use-xdoc2txt
       (moccur-grep-correspond-ext-p
        filename moccur-grep-xdoc2txt-exts))
      t
    nil))

(defun moccur-search-file-p (filename)
  (and
   (file-readable-p filename)
   (or
    (and
     (not moccur-grep-xdoc2txt-maximum-size)
     (moccur-file-size< filename moccur-grep-xdoc2txt-maximum-size)
     (moccur-grep-xdoc2txt-p filename))
    (and
     (moccur-file-size< filename dmoccur-maximum-size)
     (not (dmoccur-in-list-p filename
                             dmoccur-exclusion-mask))))))

(defun moccur-search-files-init (regexp files)
  (setq moccur-special-word nil)
  (moccur-set-regexp)
  (moccur-set-regexp-for-color)

  (setq moccur-matches 0)
  (setq moccur-regexp-input regexp)
  (if (string= (car regexp-history) moccur-regexp-input)
      ()
    (setq regexp-history
          (cons moccur-regexp-input regexp-history))))

(defun moccur-files-insert-xdoc2txt-file (filename)
  (let ((fn (concat
             (expand-file-name
              (make-temp-name "xdoc2")
              temporary-file-directory)
             "."
             (file-name-extension filename)))
        (str nil)
        (coding-system-for-write 'binary)
        (coding-system-for-read 'binary))
    (set-buffer-file-coding-system 'euc-japan)
    (copy-file filename fn t)
    (insert
     (shell-command-to-string
      (concat
       "cd " (file-name-directory fn) ";"
       "xdoc2txt" " -e " (file-name-nondirectory fn))))
    (delete-file fn)
    (decode-coding-region (point-min) (point-max)
                          'euc-jp)
    (goto-char (point-min))
    (while (re-search-forward "\r" nil t)
      (delete-region (match-beginning 0)
                     (match-end 0)))
    (goto-char (point-min))
    (while (re-search-forward "\\([\n ]+\\)\n[ ]*\n" nil t)
      (delete-region (match-beginning 1)
                     (match-end 1)))
    (goto-char (point-min))))

(defun moccur-search-all-files (files)
  (let ((total (length files))
        (num 0))
    (condition-case err
        (while files
          (setq num (+ num 1))
          (with-temp-buffer
            (when
                (or
                 (string= moccur-last-command 'moccur-grep)
                 (and
                  (not (string= moccur-last-command 'moccur-grep))
                  (moccur-search-file-p (car files))))
              (message "Searching %d/%d (%d matches) : %s ..."
                       num total moccur-matches
                       (file-relative-name (car files) default-directory))
              (condition-case err
                  (cond
                   ((moccur-grep-correspond-ext-p
                     (car files) moccur-grep-xdoc2txt-exts)
                    (moccur-files-insert-xdoc2txt-file (car files)))
                   (t
                    (if moccur-grep-search-file-pos
                        (insert-file-contents (car files) nil 0 moccur-grep-search-file-pos)
                      (insert-file-contents (car files)))))
                (error
                 ())))
            (widen)
            (moccur-search-buffer (car moccur-regexp-list) (current-buffer)
                                  (car files)))
          (setq files (cdr files)))
      (quit
       ()))))

(defun moccur-search-files (regexp files)
  "Search REGEXP in FILES (list)."

  ;; initialize
  (moccur-search-files-init regexp files)

  (save-excursion
    (setq moccur-mocur-buffer (generate-new-buffer "*Moccur*"))
    (set-buffer moccur-mocur-buffer)
    (moccur-insert-heading moccur-regexp-input)

    ;; search all buffers
    (moccur-search-all-files files)
    (message "Searching done!")
    (if (> moccur-matches 0)
        (progn
          (set-buffer moccur-mocur-buffer)
          (delete-other-windows)
          (moccur-grep-mode)
          ;; highlight Moccur buffer
          (moccur-buffer-color)
          (setq buffer-undo-list nil)

          ;; move cursor to the first matching text
          (set-buffer moccur-mocur-buffer)
          ;;(setq moccur-view-other-window nil)

          (pop-to-buffer moccur-mocur-buffer)
          (goto-char (point-min))

          (make-local-variable 'moccur-xdoc2txt-buffers)
          (setq moccur-xdoc2txt-buffers nil)

          (message "%d matches" moccur-matches)
          t)
      (message "no matches")
      (moccur-kill-buffer t)
      (moccur-remove-overlays-on-all-buffers)
      nil)))

(defun moccur-grep-binary-file-view (file)
  (cond
   ((and (rassoc file moccur-xdoc2txt-buffers)
         (car (rassoc file moccur-xdoc2txt-buffers))
         (buffer-live-p (get-buffer (car (rassoc file moccur-xdoc2txt-buffers)))))
    (car (rassoc file moccur-xdoc2txt-buffers)))
   (t
    (save-current-buffer
      (let ((dummy-buff (generate-new-buffer
                         (concat "xdoc2txt:"
                                 (file-name-nondirectory
                                  file))))
            (coding-system-for-write 'binary)
            (coding-system-for-read 'binary))
        (set-buffer dummy-buff)
        (let ((fn (concat
                   (expand-file-name
                    (make-temp-name "xdoc2")
                    temporary-file-directory)
                   "."
                   (file-name-extension file)))
              (str nil)
              )
          (set-buffer-file-coding-system 'euc-japan)

          (copy-file file fn t)
          (insert
           (shell-command-to-string
            (concat
             "cd " (file-name-directory fn) ";"
             "xdoc2txt" " -e " (file-name-nondirectory fn))))
          (decode-coding-region (point-min) (point-max)
                                'euc-jp)
          (goto-char (point-min))
          (while (re-search-forward "\r" nil t)
            (delete-region (match-beginning 0)
                           (match-end 0)))
          (goto-char (point-min))
          (while (re-search-forward "\\([\n ]+\\)\n[ ]*\n" nil t)
            (delete-region (match-beginning 1)
                           (match-end 1)))
          (delete-file fn)
          )
        (setq buffer-read-only t)
        (goto-char (point-min))
        (view-mode t)
        (buffer-name dummy-buff)
        )))))

(defun moccur-grep-sync-kill-buffers ()
  (let (buf)
    (when moccur-grep-buffer-list
      (while moccur-grep-buffer-list
        (setq buf (car moccur-grep-buffer-list))
        (setq moccur-grep-buffer-list
              (cdr moccur-grep-buffer-list))
        (if (and (buffer-live-p buf)
                 (not (buffer-modified-p buf)))
            (kill-buffer buf)))
      (delete-other-windows))))

(add-hook 'kill-buffer-hook
          '(lambda ()
             (if (string= major-mode 'moccur-grep-mode)
                 (moccur-grep-sync-kill-buffers))))

(defun moccur-grep-goto ()
  (interactive)
  (let (file line str buf)
    (save-excursion
      (if (re-search-backward moccur-grep-buffer-heading-regexp nil t)
          (setq file
                (buffer-substring-no-properties
                 (match-beginning 1)
                 (match-end 1)))))
    (save-excursion
      (end-of-line)
      (if (re-search-backward moccur-line-number-regexp nil t)
          (setq line
                (string-to-number
                 (buffer-substring-no-properties
                  (match-beginning 1)
                  (match-end 1))))))
    (when (and file line)
      (cond
       ((moccur-grep-xdoc2txt-p file)
        (setq buf (moccur-grep-binary-file-view file))
        (when (not (assoc buf moccur-xdoc2txt-buffers))
          (setq moccur-xdoc2txt-buffers
                (cons
                 (cons buf file)
                 moccur-xdoc2txt-buffers)))
        (switch-to-buffer-other-window buf))
       (t
        (find-file-other-window file)))
      (widen)
      (goto-line line))))

(defun moccur-grep-read-directory ()
  (let ((dir default-directory))
    (setq dir
          (if (and (boundp 'running-xemacs) running-xemacs)
              (read-directory-name "Directory: " dir)
            (read-file-name "Directory: " nil nil t)))
    (if (and (file-exists-p dir)
             (file-directory-p  dir))
        (setq dir (file-name-as-directory dir))
      (setq dir (file-name-as-directory (file-name-directory dir)))
      (if (and (file-exists-p dir)
               (file-directory-p  dir))
          ()
        (error (format "No such directory %s" dir))
        (sleep-for 1)
        (setq dir nil)))
    dir))

(defun moccur-grep-read-regexp (&optional mask)
  (let (regexp input (wd nil) (init nil) (pt 1))
    (when moccur-grep-default-word-near-point
      ;; get a word near the point as default regexp string
      (setq wd (thing-at-point 'symbol))
      (set-text-properties 0 (length wd) nil wd)
      ;; put point to the end of default word
      (setq pt (1+ (length wd))))
    (setq init (cons (concat wd " " mask) pt))
    (setq input
          (read-from-minibuffer "Input Regexp and FileMask: " init))
    (moccur-split-string input " ")))

(defun moccur-grep (dir inputs)
  (interactive
   (list (moccur-grep-read-directory)
         (moccur-grep-read-regexp moccur-grep-default-mask)))
  (moccur-setup)
  (setq moccur-last-command 'moccur-grep)

  (let (regexps mask files)
    (setq regexps
          (mapconcat 'concat
                     (if (= 1 (length inputs))
                         inputs
                       (reverse (cdr (reverse inputs))))
                     " "))
    (setq mask
          (if (= 1 (length inputs))
              "."
            (car (reverse inputs))))
    (setq files (directory-files dir t mask))
    (let (list)
      (dolist (elt files)
        (cond
         ((file-directory-p elt)
          ())
         (t
          (push elt list))))
      (setq files (reverse list)))
    (moccur-search-files regexps files)
    ))

(defun moccur-grep-find-subdir (dir mask)
  (let ((files (cdr (cdr (directory-files dir t)))) (list) (plist))
    (if (not (moccur-search-file-p dir))
        (setq list nil)
      (dolist (elt files)
        (cond
         ((and
           (not (string-match "^[.]+$" (file-name-nondirectory elt)))
           (file-directory-p elt))
          (setq list (append (moccur-grep-find-subdir elt mask) list)))
         ((string-match "^[.]+$" (file-name-nondirectory elt))
          ())
         ((string-match mask (file-name-nondirectory elt))
          (push elt list))
         (t ()))
        (if (not (eq list plist))
            (message "Listing %s ..." (file-name-directory elt)))
        (setq plist list)))
    list))

(defun moccur-grep-find (dir inputs)
  (interactive
   (list (moccur-grep-read-directory)
         (moccur-grep-read-regexp moccur-grep-default-mask)))
  (moccur-setup)
  (setq moccur-last-command 'moccur-grep-find)

  (let (regexps
        mask (files nil)
        ;;(default-directory dir)
        )
    (setq regexps
          (mapconcat 'concat
                     (if (= 1 (length inputs))
                         inputs
                       (reverse (cdr (reverse inputs))))
                     " "))
    (setq mask
          (if (= 1 (length inputs))
              "."
            (car (reverse inputs))))
    (message "Listing files...")
    (cond
     ((listp dir)
      (while dir
        (cond
         ((file-directory-p (car dir))
          (setq files (append
                       (reverse (moccur-grep-find-subdir (car dir) mask))
                       files)))
         (t
          (setq files (cons
                       (car dir)
                       files))))
        (setq dir (cdr dir))))
     (t
      (setq files (reverse (moccur-grep-find-subdir dir mask)))))
    (message "Listing files done!")
    (moccur-search-files regexps files)
    ))

;;; dmoccur
;;;; utility
(defun dmoccur-in-list-p (dir-name dir-name-regexps)
  (let ((case-fold-search t))
    (cond ((null dir-name-regexps) nil)
          ((string-match  (car dir-name-regexps) dir-name) t)
          (t (dmoccur-in-list-p dir-name (cdr dir-name-regexps))))))

(defun moccur-add-files-to-search-list (files dir &optional norest recursive)
  (let ((buffers nil) (file-regexps dmoccur-recursive-ignore-dir)
        (file-ignore nil)
        file-name buf-name (cbuf (current-buffer))
        (enable-local-eval t))
    (while files
      (setq file-ignore nil)
      (setq file-regexps dmoccur-recursive-ignore-dir)
      (setq buf-name nil)
      (setq file-name (expand-file-name (car files) dir))

      (while file-regexps
        (if (string-match (car file-regexps) file-name)
            (setq file-ignore t))
        (setq file-regexps (cdr file-regexps)))
      (when (not file-ignore)
        (if (file-directory-p file-name)
            (cond
             ((string= 'dired recursive)
              (setq buffers
                    (append
                     (moccur-add-files-to-search-list
                      (directory-files file-name) file-name norest nil)
                     buffers)))
             ((and recursive
                   (not (string= (expand-file-name "." dir)
                                 file-name))
                   (not (string= (expand-file-name ".." dir)
                                 file-name)))
              (setq buffers
                    (append
                     (moccur-add-files-to-search-list
                      (directory-files file-name) file-name norest recursive)
                     buffers)))
             (t
              nil))
          (if (and
               (file-readable-p file-name)
               (or norest
                   (and
                    (moccur-file-size< file-name dmoccur-maximum-size)
                    (dmoccur-in-list-p file-name dmoccur-mask-internal)
                    (not (dmoccur-in-list-p file-name
                                            dmoccur-exclusion-mask)))))
              (progn
                (if (get-file-buffer file-name)
                    (setq buf-name (get-file-buffer file-name))
                  (setq buf-name (find-file-noselect file-name)))
                (if (cdr file-name-history)
                    (setq file-name-history (cdr file-name-history)))
                (save-current-buffer
                  (set-buffer buf-name)
                  (setq dmoccur-buffer-project dmoccur-project-name))
                (if buf-name
                    (setq buffers (cons buf-name buffers)))))))
      (setq files (cdr files)))
    buffers))

(defun moccur-add-directory-to-search-list (dir)
  (setq dmoccur-recursive-ignore-dir nil)
  (let ((buffers nil))
    (if (listp dir)
        (progn
          (let ((recursive nil) (cdir nil))
            (while dir
              (setq cdir (eval (car (car dir))))
              (setq dmoccur-recursive-ignore-dir
                    (nth 2 (car dir)))
              (setq recursive
                    (nth 1 (car dir)))
              (setq buffers
                    (append
                     (if (file-directory-p cdir)
                         (moccur-add-files-to-search-list
                          (directory-files cdir) cdir nil recursive)
                       (moccur-add-files-to-search-list
                        (list cdir) (file-name-directory cdir) t))
                     buffers))
              (setq dir (cdr dir)))))
      (let ((files (directory-files dir)))
        (setq buffers
              (moccur-add-files-to-search-list
               files dir nil dmoccur-recursive-search))))
    (let (list)
      (dolist (elt buffers)
        (unless (member elt list)
          (push elt list)))
      (setq buffers list))
    buffers))

;;;; minibuffer
(defun dmoccur-read-directory-from-minibuf (default)
  (let ((dir nil))
    (while (not dir)
      (setq dir
            (if (and (boundp 'running-xemacs) running-xemacs)
                (read-directory-name "Directory: " default)
              (read-file-name "Directory: " default nil t)))
      ;;(read-file-name "Directory: " nil nil t default)))
      (if (and (file-exists-p dir)
               (file-directory-p  dir))
          (setq dir (file-name-as-directory dir))
        (setq dir (file-name-as-directory (file-name-directory dir)))
        (if (and (file-exists-p dir)
                 (file-directory-p  dir))
            ()
          (message "No such directory %s" dir)
          (sleep-for 1)
          (setq dir nil))))
    dir))

(defun dmoccur-read-project-name-from-minibuf (arg)
  (let (input-name)
    (if (and dmoccur-buffer-project
             dmoccur-use-project
             (or
              (and
               (not arg)
               dmoccur-use-list)
              (and
               arg
               (not dmoccur-use-list))))
        (setq input-name (car dmoccur-buffer-project))
      (setq input-name
            (completing-read
             (concat
              "dmoccur name "
              (when (car dmoccur-list-history)
                (format "(default %s)"
                        (car dmoccur-list-history)))
              " : ")
             (let (list)
               (dolist (elt (append
                             dmoccur-project-list
                             dmoccur-list))
                 (unless (assoc (car elt) list)
                   (push elt list)))
               list)
             nil nil nil 'dmoccur-list-history
             (if (car dmoccur-list-history)
                 (car dmoccur-list-history)
               nil))))
    input-name))

(defun dmoccur-set-sub-directory (name dir)
  (let ((lst nil)
        (subdir
         (if (listp dir)
             (eval (nth 0 (car dir)))
           (eval dir))))
    (setq lst (mapcar '(lambda (file)
                         (if (and (not (string-match "\\.+$" file))
                                  (file-directory-p file))
                             (file-name-nondirectory file)))
                      (directory-files
                       subdir t)))
    (setq lst (delq nil lst))

    (if (and dmoccur-buffer-project
             dmoccur-use-project)
        (setq subdir (car (cdr dmoccur-buffer-project)))
      (setq subdir (concat
                    (file-name-as-directory subdir)
                    (completing-read
                     "dmoccur sub directory : "
                     (mapcar 'list lst)
                     nil t)
                    "/")))
    (if (listp dir)
        (list (cons subdir (nthcdr 1 (car dir))))
      subdir)))

(defun dmoccur-set-project (arg)
  (setq dmoccur-project-name nil)
  (let (input-name name lst dir)
    (setq input-name (dmoccur-read-project-name-from-minibuf arg))

    (if (assoc input-name dmoccur-project-list)
        (setq name (nth 1 (assoc input-name dmoccur-project-list)))
      (setq name input-name))
    (cond
     ((assoc name dmoccur-list)
      ;; default directory
      (setq dir
            (if (listp (nth 1 (assoc name dmoccur-list)))
                (condition-case err
                    (eval (nth 1 (assoc name dmoccur-list)))
                  (error
                   (nth 1 (assoc name dmoccur-list))))
              (file-name-as-directory
               (eval (nth 1 (assoc name dmoccur-list))))))

      ;; 'sub option
      (if (string= 'sub (nth 3 (assoc name dmoccur-list)))
          (if (and (listp dir)
                   (not (= (length dir) 1)))
              (error "Multiple directory exists!")
            (setq dir
                  (dmoccur-set-sub-directory name dir))))

      ;; if buffer-project exists, use it
      (if (and dmoccur-buffer-project
               dmoccur-use-project)
          ()
        (if (string= 'dir (nth 3 (assoc name dmoccur-list)))
            (if (and (listp dir)
                     (not (= (length dir) 1)))
                (error "Multiple directory exists!")
              (if (listp dir)
                  (setq dir
                        (list
                         (cons
                          (dmoccur-read-directory-from-minibuf
                           (eval (car (car dir)))) (cdr (car dir)))))
                (setq dir (dmoccur-read-directory-from-minibuf dir))))))

      ;; set current project
      (setq dmoccur-project-name
            (if (listp dir)
                (cons name dir)
              (cons name (cons dir dmoccur-project-name))))

      ;; mask
      (setq dmoccur-mask-internal (nth 2 (assoc name dmoccur-list))))

     ((assoc input-name dmoccur-project-list)
      (if (and (string= name input-name)
               (string-match "^dmoccur" name))
          (setq name "dmoccur"))
      (if (or (string= 'dir (nth 3 (assoc name dmoccur-list)))
              (string= 'sub (nth 3 (assoc name dmoccur-list)))
              (string= name "dmoccur"))
          (setq dir
                (substring input-name
                           (progn
                             (string-match (concat name "-") input-name)
                             (match-end 0))))
        (setq dir (nth 1 (assoc name dmoccur-project-list))))
      (setq dmoccur-project-name (cons name dir)))
     (t
      (setq dmoccur-list-history (cdr dmoccur-list-history))
      (error "Input correct name!")))
    dir))

(defun dmoccur-read-from-minibuf (arg)
  (let ((dir nil))
    (if (or arg
            dmoccur-use-list)
        (setq dir (dmoccur-set-project arg))
      (setq dir default-directory)
      (setq dmoccur-mask-internal dmoccur-mask)
      (setq dir (dmoccur-read-directory-from-minibuf dir)))
    dir))

;;;; interactive
(defun dmoccur (dir regexp arg)
  "Show all lines of all buffers containing a match for REGEXP.
The lines are shown in a buffer named *Moccur*.
It serves as a menu to find any of the occurrences in this buffer.
\\[describe-mode] in that buffer will explain how."
  (interactive (list (dmoccur-read-from-minibuf current-prefix-arg)
                     (moccur-regexp-read-from-minibuf)
                     current-prefix-arg))
  (moccur-setup)

  (setq moccur-last-command 'dmoccur)
  (let* ((list-name (if (car dmoccur-project-name)
                        (car dmoccur-project-name) "dmoccur"))
         (buffers
          (moccur-add-directory-to-search-list dir))
         (name
          (list
           (if (and
                (or dmoccur-use-list arg)
                (or
                 (not (or (string= 'dir
                                   (nth 3 (assoc list-name dmoccur-list)))
                          (string= 'sub
                                   (nth 3 (assoc list-name dmoccur-list)))))
                 (assoc list-name dmoccur-project-list)))
               list-name
             (concat list-name "-"
                     (if (listp dir) (expand-file-name (car (car dir)))
                       (expand-file-name dir))))
           list-name)))
    ;; sort
    (setq buffers (sort buffers moccur-buffer-sort-method))

    (if (assoc (car name) dmoccur-project-list)
        (progn
          (let* ((lst (assoc (car name) dmoccur-project-list))
                 (old-buffers (nthcdr 2 lst)))
            (setq dmoccur-project-list (delete lst dmoccur-project-list))
            (setq name
                  (append name
                          (let ((list nil))
                            (dolist (elt (append
                                          old-buffers
                                          buffers))
                              (unless (memq elt list)
                                (push elt list)))
                            list)))))
      (setq name
            (append name
                    buffers)))

    (setq dmoccur-project-list
          (cons
           name
           dmoccur-project-list))

    (if (nth 4 (assoc list-name dmoccur-list))
        (let* ((conf (if (nth 4 (assoc list-name dmoccur-list))
                         (nth 4 (assoc list-name dmoccur-list))
                       nil))
               (moccur-use-migemo (car conf))
               (moccur-split-word (car (cdr conf))))
          (moccur-search regexp arg buffers))
      (moccur-search regexp arg buffers))))

(defun clean-dmoccur-buffers ()
  (interactive)
  (let (name buffers lst)
    (setq name (completing-read
                (concat
                 "dmoccur name "
                 " : ")
                dmoccur-project-list))

    (setq buffers (nthcdr 2 (assoc name dmoccur-project-list)))
    (setq lst (list
               (nth 1 (assoc name dmoccur-project-list))))
    (setq lst (append (list name) lst))
    (setq lst (append lst buffers))

    (setq dmoccur-project-list (delete lst dmoccur-project-list))
    (while buffers
      (if (and (car buffers)
               (buffer-live-p (car buffers))
               (get-buffer (car buffers))
               (not (buffer-modified-p (car buffers))))
          (kill-buffer (car buffers)))
      (setq buffers (cdr buffers)))))

;;; call moccur
;;;; dired
(defun dired-do-moccur-by-moccur (regexp arg)
  (let ((buffers (moccur-add-files-to-search-list
                  (funcall (cond ((fboundp 'dired-get-marked-files) ; GNU Emacs
                                  'dired-get-marked-files)
                                 ((fboundp 'dired-mark-get-files) ; XEmacs
                                  'dired-mark-get-files))
                           t nil) default-directory t 'dired))
        (buff nil))
    (moccur-search regexp arg buffers)
    (setq moccur-last-command 'dired-do-moccur)
    (when kill-buffer-after-dired-do-moccur
      (while buffers
        (setq buff (car buffers))
        (if (memq buff moccur-match-buffers)
            ()
          (if (memq buff moccur-buffers-before-moccur)
              (delq buff buffers)
            (kill-buffer buff)))
        (setq buffers (cdr buffers))))))

(defun dired-do-moccur-by-mgrep (regexp arg)
  (let* ((files (funcall (cond ((fboundp 'dired-get-marked-files) ; GNU Emacs
                                'dired-get-marked-files)
                               ((fboundp 'dired-mark-get-files) ; XEmacs
                                'dired-mark-get-files))
                         t nil))
         (buff nil))
    (moccur-grep-find files
                      (moccur-split-string
                       (concat regexp " .") " "))
    (setq moccur-last-command 'dired-do-moccur)))

(defun dired-do-moccur (regexp arg)
  "Show all lines of all buffers containing a match for REGEXP.
The lines are shown in a buffer named *Moccur*.
It serves as a menu to find any of the occurrences in this buffer.
\\[describe-mode] in that buffer will explain how."
  (interactive (list (moccur-regexp-read-from-minibuf)
                     current-prefix-arg))
  (moccur-setup)
  (setq moccur-buffers-before-moccur (buffer-list))
  (if arg
      (dired-do-moccur-by-moccur regexp arg)
    (dired-do-moccur-by-mgrep regexp arg)))

;;;; kill-buffer when moccur-quit
(defadvice moccur-quit (before moccur-quit-kill-buffers activate)
  (let ((buffers moccur-match-buffers)
        (buff nil)
        (mocc-window (selected-window))
        (mocc-buffer (window-buffer (selected-window))))
    (while moccur-xdoc2txt-buffers
      (when (buffer-live-p
             (get-buffer (car (car moccur-xdoc2txt-buffers))))
        (kill-buffer (car (car moccur-xdoc2txt-buffers))))
      (setq moccur-xdoc2txt-buffers (cdr moccur-xdoc2txt-buffers)))
    (while buffers
      (setq buff (car buffers))
      (when (and (eq moccur-last-command 'dired-do-moccur)
                 kill-buffer-after-dired-do-moccur
                 (buffer-live-p buff)
                 (buffer-name buff))
        (select-window (next-window mocc-window))
        (set-window-buffer (selected-window) buff)
        (if (and (buffer-file-name buff)
                 (buffer-modified-p buff)
                 (y-or-n-p (concat "Buffer "
                                   (buffer-name buff)
                                   " modified. Save it? ")))
            (save-buffer)
          (set-buffer-modified-p nil)) ;; mark as not modified
        (display-buffer mocc-buffer)
        (select-window mocc-window)
        (if (memq buff moccur-buffers-before-moccur)
            (delq buff buffers)
          (kill-buffer buff)))
      (setq buffers (cdr buffers))))
  nil)

;;;; Buffer-menu-moccur
(defun Buffer-menu-moccur (regexp arg)
  (interactive (list (moccur-regexp-read-from-minibuf)
                     current-prefix-arg))
  (setq arg 1)
  (moccur-kill-buffer t)
  (setq moccur-last-command 'buffer-menu-moccur)
  (let ((marked-buffer) (marked-files))
    (goto-char (point-min))
    (while (search-forward "\n>" nil t)
      (setq marked-buffer (Buffer-menu-buffer t))
      (setq marked-files (cons marked-buffer marked-files)))
    (moccur-search regexp arg marked-files)))

(unless (featurep 'ibuffer)
  (defun ibuffer-map-marked-lines (func))
  (defun ibuffer-do-occur (regexp &optional nlines)))
(defadvice ibuffer-do-occur
  (around ibuffer-menu-moccur activate)
  (interactive (list (moccur-regexp-read-from-minibuf)
                     current-prefix-arg))
  (setq moccur-last-command 'buffer-menu-moccur)
  (let (arg (regexp (ad-get-arg 0)))
    (setq arg 1)
    (moccur-kill-buffer t)
    (let ((marked-buffers nil))
      (ibuffer-map-marked-lines
       #'(lambda (buf mark beg end)
           (push buf marked-buffers)))
      (ibuffer-unmark-all 62)
      (moccur-search regexp arg marked-buffers))))

;;; moccur mode
;;;; keybind
(defvar moccur-mode-map ())
(defun moccur-set-key ()
  (let ((map (make-sparse-keymap)))
    (define-key map "e" 'moccur-toggle-buffer)
    (define-key map "\C-c\C-c" 'moccur-mode-goto-occurrence)
    (define-key map "\C-m" 'moccur-mode-goto-occurrence)
    (define-key map "d" 'moccur-kill-line)
    (define-key map "\C-k" 'moccur-kill-line)
    (define-key map "\M-d" 'moccur-mode-kill-file)
    (define-key map "/" 'moccur-mode-undo)
    ;;(define-key map "f" 'moccur-flush-lines) ;; M-x
    ;;(define-key map "" 'moccur-keep-lines) ;; M-x
    (define-key map "q" 'moccur-quit)
    (define-key map "n" 'moccur-next)
    (define-key map "p" 'moccur-prev)
    (define-key map "j" 'moccur-next)
    (define-key map "k" 'moccur-prev)
    (define-key map '[wheel-down] 'moccur-next)
    (define-key map '[wheel-up] 'moccur-prev)
    (define-key map "s" 'moccur-narrow-down)
    (define-key map "u" 'moccur-search-undo)
    (define-key map "g" 'moccur-search-update)
    (define-key map '[down] 'moccur-next)
    (define-key map '[up] 'moccur-prev)
    (define-key map "t" 'moccur-toggle-view)
    (define-key map "b" 'moccur-file-scroll-down)
    (define-key map " " 'moccur-file-scroll-up)
    ;;     (define-key map "b" 'moccur-scroll-down)
    ;;     (define-key map " " 'moccur-scroll-up)
    (define-key map "\M-v" 'moccur-scroll-down)
    (define-key map "\C-v" 'moccur-scroll-up)
    (define-key map "h" 'moccur-next-file)
    (define-key map "l" 'moccur-prev-file)
    (define-key map "\M-n" 'moccur-next-file)
    (define-key map "\M-p" 'moccur-prev-file)
    (define-key map '[M-wheel-down] 'moccur-next-file)
    (define-key map '[M-wheel-up] 'moccur-prev-file)

    (define-key map '[down-mouse-1] 'moccur-mouse-select1)

    (define-key map "<" 'moccur-file-beginning-of-buffer)
    (define-key map ">" 'moccur-file-end-of-buffer)

    (condition-case nil
        (progn
          (require 'moccur-edit)
          (define-key map "r" 'moccur-edit-mode-in)
          (define-key map "\C-x\C-q" 'moccur-edit-mode-in)
          (define-key map "\C-c\C-i" 'moccur-edit-mode-in))
      (error
       nil))
    map))

(if moccur-mode-map
    ()
  (setq moccur-mode-map (make-sparse-keymap))
  (setq moccur-mode-map (moccur-set-key)))

(defvar moccur-ee-mode-map ())
(defun moccur-set-key-ee ()
  (let ((map (make-sparse-keymap)))
    (setq map (moccur-set-key))
    ;; Expansion visibility
    (define-key map "+" 'ee-view-expansion-show)
    (define-key map "-" 'ee-view-expansion-hide)
    (define-key map "=" 'ee-view-expansion-show)
    ;; on some keyboards "=" is on same key as "+", but typed w/o shift
    (define-key map "*" 'ee-view-expansion-show-subtree)
    ;;(define-key map "/" 'ee-view-expansion-hide-subtree)
    ;; Help
    (define-key map "?" 'describe-mode)
    ;;(define-key map "r"
    ;; (lambda () (interactive) (message "%S" (ee-view-record-get))))
    ;;(define-key map "\C-c\C-hr"
    ;; (lambda () (interactive) (message "%S" (ee-view-record-get))))
    ;; Buffer
    (define-key map "g" 'ee-view-buffer-revert)
    (define-key map "\C-x\C-s" 'ee-data-file-save)
    ;; outline-like key bindings
    (define-key map "\C-c\C-n" 'ee-view-expansion-next-visible)
    (define-key map "\C-c\C-p" 'ee-view-expansion-prev-visible)
    (define-key map "\C-c\C-f" 'ee-view-expansion-next-same-level)
    (define-key map "\C-c\C-b" 'ee-view-expansion-prev-same-level)
    (define-key map "\C-c\C-u" 'ee-view-expansion-up)
    (define-key map "\C-c\C-i" 'ee-view-expansion-show-children)
    (define-key map "\C-c\C-s" 'ee-view-expansion-show-subtree)
    (define-key map "\C-c\C-d" 'ee-view-expansion-hide-subtree)
    (define-key map "\C-c\C-t" 'ee-view-expansion-hide-body)
    (define-key map "\C-c\C-a" 'ee-view-expansion-show-all)
    (define-key map "\C-c\C-l" 'ee-view-expansion-hide-leaves)
    (define-key map "\C-c\C-k" 'ee-view-expansion-show-branches)
    (define-key map "\C-c\C-q" 'ee-view-expansion-hide-sublevels)
    (define-key map "\C-c\C-o" 'ee-view-expansion-hide-other)
    ;; dired-like key bindings
    (define-key map "$" 'ee-view-expansion-show-or-hide)
    ;;     (define-key map ">" 'ee-view-expansion-next)
    ;;     (define-key map "<" 'ee-view-expansion-prev)
    (define-key map "^" 'ee-view-expansion-up)
    (define-key map [(meta ?o)] 'ee-view-filter-omit)
    (define-key map [down-mouse-1] 'ee-mouse-navigation)
    (define-key map [right] 'ee-view-expansion-show-or-next)
    (define-key map [left] 'ee-view-expansion-hide-or-up-or-prev)
    (define-key map [(meta up)] 'ee-view-expansion-prev-sibling)
    (define-key map [(meta down)] 'ee-view-expansion-next-sibling)
    (define-key map [(meta right)] 'ee-view-expansion-up)
    (define-key map [(meta left)] 'ee-view-expansion-down)
    (define-key map [(control ?+)] 'ee-view-expansion-show-all)
    (define-key map [(control ?-)] 'ee-view-expansion-hide-all)
    map))

(if moccur-ee-mode-map
    ()
  (setq moccur-ee-mode-map (make-sparse-keymap))
  (setq moccur-ee-mode-map (moccur-set-key-ee)))

;;;; utility
(defun moccur-outline-level ()
  (if (looking-at "\\(^Buffer: \\)")
      0
    (if (looking-at "\\(^[ ]*[0-9]+ \\)")
        1)))

;;;; re-search function
(defun moccur-narrow-down-get-targets (target-regexp target-type)
  (let ((case-fold-search t)
        (targets nil) target-name)
    (save-excursion
      (set-buffer (get-buffer "*Moccur*"))
      (goto-char (point-min))
      (while (re-search-forward target-regexp nil t)
        (setq target-name (buffer-substring-no-properties
                           (match-beginning 1)
                           (match-end 1)))
        (if (equal target-type 'file)
            (setq targets (cons target-name targets))
          (if (get-buffer target-name)
              (setq targets (cons
                             (get-buffer target-name) targets)))))
        targets)))

(defun moccur-narrow-down-get-buffers()
  (moccur-narrow-down-get-targets moccur-buffer-heading-regexp 'buffer))

(defun moccur-narrow-down-get-files()
  (moccur-narrow-down-get-targets moccur-grep-buffer-heading-regexp 'file))

;;;; functions
(defun moccur-narrow-down (regexp arg)
  "Show all lines of all buffers containing a match for REGEXP.
The lines are shown in a buffer named *Moccur*.
It serves as a menu to find any of the occurrences in this buffer.
\\[describe-mode] in that buffer will explain how."
  (interactive (list (moccur-regexp-read-from-minibuf)
                     current-prefix-arg))

  (setq moccur-mocur-buffer (current-buffer))
  (setq moccur-last-command 'moccur-narrow-down)
  (if (equal major-mode 'moccur-grep-mode)
      (let ((files (reverse (moccur-narrow-down-get-files))))
        (moccur-setup)
        (moccur-search-files regexp files))
    (let ((buffers (reverse (moccur-narrow-down-get-buffers))))
      (moccur-setup)
      (moccur-search regexp arg buffers))))

(defun moccur-mode-goto-occurrence ()
  "Go to the line this occurrence was found in, in the buffer it was found in."
  (interactive)
  ;;    (if (not (and moccur-view-other-window
  ;;            moccur-view-other-window-nobuf))
  ;;        (moccur-view-file)
  (setq moccur-mocur-buffer (current-buffer))
  (if (not (eq major-mode 'moccur-mode))
      (error "This is no moccur buffer")
    (let ((beg nil)
          (line nil)
          (lineno nil)
          (dstbuf nil))
      (moccur-remove-overlays-on-all-buffers)
      (save-excursion
        (beginning-of-line 1)
        (setq beg (point))
        (end-of-line 1)
        (setq line (buffer-substring beg (point)))
        (if (or (string-match "^[ ]*[0-9]* " line)
                (string-match "^[-+ ]*Buffer: " line))
            (progn
              (if (string-match "^[-+ ]*Buffer: " line)
                  (setq lineno nil)
                (setq lineno (car (read-from-string line))))
              (if (re-search-backward "^[-+ ]*Buffer: ")
                  (progn
                    (search-forward "Buffer: ")
                    (setq beg (point))
                    (search-forward " File:")
                    (setq line (buffer-substring beg (- (point) 6)))
                    (setq dstbuf (get-buffer line))
                    (if (not dstbuf)
                        (message "buffer: <%s> doesn't exist anymore" line)))
                (error "What did you do with the header?!")))
          (error "This is no occurrence line!")))
      (if dstbuf
          (progn
            (if lineno
                (message "selecting <%s> line %d" line lineno)
              (message "selecting <%s>" line))
            (pop-to-buffer dstbuf)
            (if lineno
                (goto-line lineno))
            (if moccur-kill-buffer-after-goto
                (moccur-kill-buffer nil))
            (delete-other-windows))))))

(defun moccur-toggle-buffer ()
  (interactive)
  (when (and moccur-use-ee (not (featurep 'allout)))
    (let ((str
           (progn
             (save-excursion
               (if (and (not (and (boundp 'running-xemacs) running-xemacs))
                        transient-mark-mode mark-active)
                   (goto-char (region-beginning)))
               (beginning-of-line)
               (re-search-forward "[^-+ ]" nil t)
               (regexp-quote
                (buffer-substring-no-properties
                 (- (point) 1) (line-end-position)))))))
      (if (string-match "ee" (buffer-name (current-buffer)))
          (if (buffer-live-p (get-buffer "*Moccur*"))
              (switch-to-buffer (get-buffer "*Moccur*")))
        (if (buffer-live-p (get-buffer "*ee-outline*/*Moccur*"))
            (switch-to-buffer (get-buffer "*ee-outline*/*Moccur*"))))
      (goto-char (point-min))
      (condition-case err
          (re-search-forward str)
        (error
         nil))
      )))

(defun moccur-mouse-select1 (e)
  (interactive "e")
  (mouse-set-point e)
  (save-excursion
    (beginning-of-line)
    (moccur-next 0)))

(defun moccur-mouse-goto-occurrence (e)
  (interactive "e")
  (mouse-set-point e)
  (save-excursion
    (beginning-of-line)
    (moccur-mode-goto-occurrence)))

(defun moccur-next (arg)
  (interactive "p")
  (setq moccur-mocur-buffer (current-buffer))
  (if arg
      (forward-line arg)
    (forward-line 1))
  (beginning-of-line)

  (if (and moccur-use-ee (not (featurep 'allout))
           (let (end)
             (save-excursion
               (if (re-search-backward "^\\([-+ ]*\\)Buffer:" nil t)
                   (if (string-match "+"
                                     (buffer-substring-no-properties
                                      (match-beginning 1) (match-end 1)))
                       t
                     nil)
                 t))))
      (progn
        (re-search-forward "^\\([-+ ]*\\)Buffer:" nil t)
        (beginning-of-line))
    (when (re-search-forward moccur-line-number-regexp nil t)
      (save-restriction
        (narrow-to-region (point) (line-end-position))
        (re-search-forward (car moccur-regexp-list) nil t))))
  (moccur-get-info)
  (if (and moccur-view-other-window
           moccur-view-other-window-nobuf
           moccur-following-mode-toggle)
      (moccur-view-file)))

(defun moccur-prev (arg)
  (interactive "p")
  (setq moccur-mocur-buffer (current-buffer))
  (if arg
      (forward-line (* -1 arg))
    (forward-line -1))
  (end-of-line)

  (if (and moccur-use-ee
           (not (featurep 'allout))
           (let (end)
             (save-excursion
               (if (re-search-backward "^\\([-+ ]*\\)Buffer:" nil t)
                   (if (string-match "+"
                                     (buffer-substring-no-properties
                                      (match-beginning 1) (match-end 1)))
                       t
                     nil)
                 nil))))
      (re-search-backward "^\\([-+ ]*\\)Buffer:" nil t)
    (end-of-line)
    (if (re-search-backward moccur-line-number-regexp nil t)
      (save-restriction
        (re-search-forward moccur-line-number-regexp nil t)
        (narrow-to-region (point) (line-end-position))
        (re-search-forward (car moccur-regexp-list) nil t))
      (beginning-of-line)))
  (moccur-get-info)
  (if (and moccur-view-other-window
           moccur-view-other-window-nobuf
           moccur-following-mode-toggle)
      (moccur-view-file)))

(defun moccur-file-scroll-up ()
  (interactive)
  (setq moccur-mocur-buffer (current-buffer))
  (moccur-get-info)
  (if (and moccur-view-other-window
           moccur-view-other-window-nobuf)
      (moccur-scroll-file nil)))

(defun moccur-file-scroll-down ()
  (interactive)
  (setq moccur-mocur-buffer (current-buffer))
  (moccur-get-info)
  (if (and moccur-view-other-window
           moccur-view-other-window-nobuf)
      (moccur-scroll-file t)))

(defun moccur-file-beginning-of-buffer ()
  (interactive)
  (setq moccur-mocur-buffer (current-buffer))
  (moccur-get-info)
  (if (and moccur-view-other-window
           moccur-view-other-window-nobuf)
      (moccur-internal-beginning-of-buffer nil)))

(defun moccur-file-end-of-buffer ()
  (interactive)
  (setq moccur-mocur-buffer (current-buffer))
  (moccur-get-info)
  (if (and moccur-view-other-window
           moccur-view-other-window-nobuf)
      (moccur-internal-beginning-of-buffer t)))

(defun moccur-scroll-up ()
  (interactive)
  (scroll-up)
  (if (boundp 'forward-visible-line)
      (forward-visible-line -1)
    (forward-line -1))
  (end-of-line)
  (moccur-next 1))

(defun moccur-scroll-down ()
  (interactive)
  (scroll-down)
  (if (boundp 'forward-visible-line)
      (forward-visible-line 1)
    (forward-line 1))
  (beginning-of-line)
  (moccur-prev 1))

(defun moccur-next-file ()
  (interactive)
  (if (re-search-forward "^[-+ ]*Buffer: " nil t)
      (moccur-next 1)
    (goto-char (point-min))
    (moccur-next 1)))

(defun moccur-prev-file ()
  (interactive)
  (if (re-search-backward "^[-+ ]*Buffer: " nil t 2)
      (moccur-next 1)
    (goto-char (point-max))
    (if (re-search-backward "^[-+ ]*Buffer: " nil t)
        (moccur-next 1))))

(defun moccur-mode-kill-file-internal ()
  (let ((start-pt (progn
                    (re-search-backward "^[-+ ]*Buffer: " nil t)
                    (line-beginning-position)))
        (end-pt nil))

    (forward-line 1)
    (if (re-search-forward moccur-buffer-heading-regexp nil t)
        (setq end-pt (line-beginning-position))
      (setq end-pt (point-max)))
    (delete-region start-pt end-pt)))

(defun moccur-mode-kill-line-internal ()
  (delete-region (line-beginning-position)
                 (+ (line-end-position) 1))

  (moccur-get-info)
  (when (= 0 moccur-buffer-match-count)
    (moccur-mode-kill-file)))

(defun moccur-mode-start-ee-switch-before-buffer (ee line)
  (moccur-ee-start)

  (if (and ee
           (string-match "ee" (buffer-name (current-buffer))))
      (moccur-switch-buffer 'ee)
    (moccur-switch-buffer 'normal))
  (goto-line line))

(defun moccur-mode-kill-ee ()
  (when (and (string-match "ee" (buffer-name (current-buffer)))
             (buffer-live-p (get-buffer "*ee-outline*/*Moccur*")))
    (kill-buffer (get-buffer "*ee-outline*/*Moccur*"))))

(defun moccur-kill-line ()
  (interactive)
  (let* ((line (progn (end-of-line) (count-lines 1 (point))))
         (moccur-current-ee
          (if (string-match "ee" (buffer-name (current-buffer)))
              t
            nil))
         (str
          (regexp-quote
           (progn
             (save-excursion
               (beginning-of-line)
               (re-search-forward "[^ ]" (line-end-position) t)
               (buffer-substring-no-properties
                (- (point) 1) (line-end-position)))))))

    (moccur-mode-kill-ee)
    (moccur-switch-buffer 'normal)
    (goto-char (point-min))
    (if (string-match "^[+-]" str)
        (setq str (substring str 2)))
    (let ((buffer-read-only nil)
          (inhibit-read-only nil))
      (when (re-search-forward str nil t)
        (line-beginning-position)
        (cond
         ((string-match "^[ ]*$" str)
          ())
         ((string-match moccur-buffer-heading-regexp str)
          (moccur-mode-kill-file-internal))

         ((string-match moccur-line-number-regexp str)
          (moccur-mode-kill-line-internal))
         (t
          ()))))

    ;; highlight but slow..., so comment...
    ;;(moccur-buffer-color)
    (moccur-mode-start-ee-switch-before-buffer moccur-current-ee line)))

(defun moccur-mode-kill-file ()
  (interactive)
  (let* ((line (progn (end-of-line) (count-lines 1 (point))))
         (moccur-current-ee
          (if (string-match "ee" (buffer-name (current-buffer)))
              t
            nil))
         (str
          (regexp-quote
           (progn
             (save-excursion
               (end-of-line)
               (re-search-backward "^[-+ ]*Buffer: " nil t)
               (buffer-substring-no-properties
                (point) (line-end-position)))))))

    (moccur-mode-kill-ee)
    (moccur-switch-buffer 'normal)
    (goto-char (point-min))
    (if (string-match "^[+-]" str)
        (setq str (substring str 2)))
    (let ((buffer-read-only nil)
          (inhibit-read-only nil))
      (when (re-search-forward (regexp-quote str) nil t)
        (line-beginning-position)
        (moccur-mode-kill-file-internal)))

    ;; highlight but slow..., so comment...
    ;;(moccur-buffer-color)

    (moccur-mode-start-ee-switch-before-buffer moccur-current-ee line)))

(defun moccur-mode-undo ()
  (interactive)
  (let* ((line (progn (end-of-line) (count-lines 1 (point))))
         (moccur-current-ee
          (if (string-match "ee" (buffer-name (current-buffer)))
              t
            nil))
         (str
          (regexp-quote
           (progn
             (save-excursion
               (end-of-line)
               (re-search-backward "^[-+ ]*Buffer: " nil t)
               (buffer-substring-no-properties
                (point) (line-end-position)))))))

    (moccur-mode-kill-ee)
    (moccur-switch-buffer 'normal)
    (if (string-match "^[+-]" str)
        (setq str (substring str 2)))
    (let ((buffer-read-only nil)
          (inhibit-read-only nil))
      (condition-case err
          (undo)
        (error
         ()))
      (goto-char (point-min))
      (re-search-forward (regexp-quote str) nil t))

    ;; highlight but slow..., so comment...
    ;;(moccur-buffer-color)

    (moccur-mode-start-ee-switch-before-buffer moccur-current-ee line)))

(defun moccur-flush-lines ()
  (interactive)
  (let ((str
         (progn
           (save-excursion
             (if (and (not (and (boundp 'running-xemacs) running-xemacs))
                      transient-mark-mode mark-active)
                 (goto-char (region-beginning)))
             (beginning-of-line)
             (re-search-forward "[^ ]" nil t)
             (regexp-quote
              (buffer-substring-no-properties
               (- (point) 1) (line-end-position))))))
        (rend-str (if (and (not (and (boundp 'running-xemacs) running-xemacs))
                           transient-mark-mode mark-active)
                      (progn
                        (save-excursion
                          (goto-char (region-end))
                          (beginning-of-line)
                          (re-search-forward "[^ ]" (line-end-position) t)
                          (regexp-quote
                           (buffer-substring-no-properties
                            (- (point) 1) (line-end-position)))))
                    nil))
        (line (progn (save-excursion (end-of-line) (count-lines 1 (point)))))
        (moccur-current-ee
         (if (string-match "ee" (buffer-name (current-buffer)))
             t
           nil))
        (regexp
         (read-from-minibuffer
          "Flush lines (containing match for regexp): " nil nil nil
          'regexp-history nil t)))

    (moccur-mode-kill-ee)
    (moccur-switch-buffer 'normal)

    (goto-char (point-min))
    (if (string-match "^[+-]" str)
        (setq str (substring str 2)))
    (if (and rend-str
             (string-match "^[+-]" rend-str))
        (setq rend-str (substring rend-str 2)))

    (re-search-forward (regexp-quote str) nil t)
    (beginning-of-line)
    (let (rstart rend
                 (buffer-read-only nil)
                 (inhibit-read-only nil))
      (setq rstart (point))
      (if rend-str
          (setq rend (copy-marker
                      (save-excursion
                        (goto-char (point-min))
                        (re-search-forward (regexp-quote rend-str) nil t)
                        (end-of-line)
                        (point))))
        (setq rend (point-max-marker)))
      (goto-char rstart)
      (let ((case-fold-search case-fold-search))
        (save-excursion
          (while (and (< (point) rend)
                      (re-search-forward regexp rend t))
            (goto-char (line-beginning-position))
            (unless (re-search-forward
                     moccur-buffer-heading-regexp (line-end-position) t)
              (line-beginning-position)
              (moccur-mode-kill-line-internal))))))
    (moccur-mode-start-ee-switch-before-buffer moccur-current-ee line)))

(defun moccur-keep-lines ()
  (interactive)
  (let ((str
         (progn
           (save-excursion
             (if (and (not (and (boundp 'running-xemacs) running-xemacs))
                      transient-mark-mode mark-active)
                 (goto-char (region-beginning)))
             (beginning-of-line)
             (re-search-forward "[^ ]" nil t)
             (regexp-quote
              (buffer-substring-no-properties
               (- (point) 1) (line-end-position))))))
        (rend-str (if (and (not (and (boundp 'running-xemacs) running-xemacs))
                           transient-mark-mode mark-active)
                      (progn
                        (save-excursion
                          (goto-char (region-end))
                          (beginning-of-line)
                          (re-search-forward "[^ ]" (line-end-position) t)
                          (regexp-quote
                           (buffer-substring-no-properties
                            (- (point) 1) (line-end-position)))))
                    nil))
        (line (progn (save-excursion (end-of-line) (count-lines 1 (point)))))
        (moccur-current-ee
         (if (string-match "ee" (buffer-name (current-buffer)))
             t
           nil))
        (regexp (read-from-minibuffer
                 "Flush lines (containing match for regexp): " nil nil nil
                 'regexp-history nil t)))

    (moccur-mode-kill-ee)
    (moccur-switch-buffer 'normal)

    (goto-char (point-min))
    (if (string-match "^[+-]" str)
        (setq str (substring str 2)))
    (if (and rend-str
             (string-match "^[+-]" rend-str))
        (setq rend-str (substring rend-str 2)))

    (re-search-forward (regexp-quote str) nil t)
    (beginning-of-line)
    (let (rstart rend
                 (buffer-read-only nil)
                 (inhibit-read-only nil))
      (setq rstart (point))
      (if rend-str
          (setq rend (copy-marker
                      (save-excursion
                        (goto-char (point-min))
                        (re-search-forward (regexp-quote rend-str) nil t)
                        (end-of-line)
                        (point))))
        (setq rend (point-max-marker)))
      (goto-char rstart)
      (let ((case-fold-search case-fold-search))
        (save-excursion
          (while (< (point) rend)
            (goto-char (beginning-of-line))
            (unless (or (string=
                         (buffer-substring-no-properties
                          (line-beginning-position) (line-end-position)) "")
                        (save-excursion
                          (re-search-forward regexp (line-end-position) t)))
              (unless
                  (re-search-forward
                   moccur-buffer-heading-regexp (line-end-position) t)
                (beginning-of-line)
                (moccur-mode-kill-line-internal)
                (forward-line -1)))
            (forward-line 1)))))
    (moccur-mode-start-ee-switch-before-buffer moccur-current-ee line)))

(defun moccur-quit ()
  (interactive)
  (while moccur-xdoc2txt-buffers
    (when (buffer-live-p
           (car (car moccur-xdoc2txt-buffers)))
      (kill-buffer (car (car moccur-xdoc2txt-buffers))))
    (setq moccur-xdoc2txt-buffers (cdr moccur-xdoc2txt-buffers)))
  (setq buffer-menu-moccur nil)
  (moccur-kill-buffer nil)

  (when (buffer-live-p moccur-current-buffer)
    (switch-to-buffer moccur-current-buffer)
    (when moccur-windows-conf
      (set-window-configuration moccur-windows-conf)))

  ;; this is needed as "save-excursion" is used in
  ;; "moccur-remove-overlays-on-all-buffers", so we have to make sure the point in current
  ;; buffer is already restored before calling "moccur-remove-overlays-on-all-buffers"
  (when moccur-buffer-position
    (goto-char moccur-buffer-position)
    (setq moccur-buffer-position nil))

  (moccur-remove-overlays-on-all-buffers))

(defun moccur-toggle-view ()
  (interactive)
  (setq moccur-view-other-window (not moccur-view-other-window)))

;;;; body
(defun moccur-mode (&optional ee)
  "Major mode for output from \\[moccur].
Move point to one of the occurrences in this buffer,
then use \\[moccur-mode-goto-occurrence] to move to the buffer and
line where it was found.
\\{occur-mode-map}"
  (kill-all-local-variables)
  (setq buffer-read-only t)
  (setq major-mode 'moccur-mode)
  (setq mode-name "Moccur")
  (if ee
      (progn
        (setq mode-name "Moccur-ee")
        (use-local-map moccur-ee-mode-map)
        (setq moccur-ee-mode-map (moccur-set-key-ee)))
    (use-local-map moccur-mode-map)
    (setq moccur-mode-map (moccur-set-key)))
  (make-local-variable 'line-move-ignore-invisible)
  (setq line-move-ignore-invisible t)
  (if (not (and (boundp 'running-xemacs) running-xemacs))
      (add-to-invisibility-spec '(moccur . t)))
  (make-local-variable 'outline-regexp)
  (setq outline-regexp "\\(^Buffer: \\|^[ ]*[0-9]+ \\)")
  (make-local-variable 'outline-level)
  (setq outline-level 'moccur-outline-level))

(defun moccur-grep-mode ()
  "Major mode for output from \\[moccur-grep].
Move point to one of the occurrences in this buffer,
then use \\[moccur-grep-goto] to move to the buffer and
line where it was found.
\\{occur-mode-map}"
  (kill-all-local-variables)
  (setq buffer-read-only t)
  (setq major-mode 'moccur-grep-mode)
  (setq mode-name "Moccur-grep")
  (use-local-map moccur-mode-map)
  (setq moccur-mode-map (moccur-set-key))
  ;; Commented out by <WL> (who should we disable moccur-toggle-view here?)
  ;; (local-unset-key "t")
  (local-set-key "\C-m" 'moccur-grep-goto)
  (local-set-key "\C-c\C-c" 'moccur-grep-goto)
  (make-local-variable 'line-move-ignore-invisible)
  (setq line-move-ignore-invisible t)
  (if (not (and (boundp 'running-xemacs) running-xemacs))
      (add-to-invisibility-spec '(moccur . t)))

  (turn-on-font-lock)

  (make-local-variable 'outline-regexp)
  (setq outline-regexp "\\(^Buffer: File (grep): \\)")
  (make-local-variable 'outline-level)
  (setq outline-level 'moccur-outline-level))

;;; grep-buffers
;;(require 'compile)
(defun grep-buffers ()
  "*Run `grep` PROGRAM to match EXPRESSION (with optional OPTIONS) \
on all visited files."
  (interactive)
  (save-excursion
    (let*  ((regexp (read-from-minibuffer "grep all-buffer : "))
            (buffers (moccur-filter-buffers (buffer-list)))
            com)
      (setq com (concat
                 grep-command "\"" regexp "\" "))
      (while buffers
        (if (not (buffer-file-name (car buffers)))
            (setq buffers (cdr buffers))
          (let ((currfile (buffer-file-name (car buffers))))
            (setq buffers (cdr buffers))
            (setq com (concat
                       com " "
                       currfile)))))
      (grep com))))

;;; junk:search-buffers
;;;; variables
(defface search-buffers-face
  '((((class color)
      (background dark))
     (:background "SkyBlue" :bold t :foreground "Black"))
    (((class color)
      (background light))
     (:background "ForestGreen" :bold t))
    (t
     ()))
  "face."
  :group 'color-moccur
  )

(defface search-buffers-header-face
  '((((class color)
      (background dark))
     (:background "gray20" :bold t :foreground "azure3"))
    (((class color)
      (background light))
     (:background "ForestGreen" :bold t))
    (t
     ()))
  "face."
  :group 'color-moccur
  )

;;;; read minibuffer
(defun search-buffers-regexp-read-from-minibuf ()
  (let (default input)
    (setq default
          (if (thing-at-point 'word)
              (thing-at-point 'word)
            (car regexp-history)))
    (setq input
          (read-from-minibuffer
           (if default
               (format "Search buffers regexp (default `%s'): "
                       default)
             "Search buffers regexp: ")
           nil nil nil
           'regexp-history default
           color-moccur-default-ime-status))
    (if (and (equal input "") default)
        (setq input default))
    input))

;;;; body
(defvar search-buffers-current-buffer nil)
(defvar search-buffers-windows-conf nil)
(defvar search-buffers-regexp-list nil)
(defvar search-buffers-regexp nil)
(defvar search-buffers-regexp-for-moccur nil)

(defun search-buffers (regexp arg)
  "*Search string of all buffers."
  (interactive (list (search-buffers-regexp-read-from-minibuf)
                     current-prefix-arg))
  (setq search-buffers-current-buffer (current-buffer))
  (setq search-buffers-windows-conf (current-window-configuration))
  (save-excursion
    (if (get-buffer "*Search*")  ; there ought to be just one of these
        (kill-buffer (get-buffer "*Search*")))
    (let*  ((buffers (moccur-filter-buffers (buffer-list)))
            (occbuf (generate-new-buffer "*Search*"))
            (regexp-lst nil) str cur-lst match
            match-text beg end lst)

      (setq buffers (sort buffers moccur-buffer-sort-method))

      (set-buffer occbuf)
      (insert "Search " regexp "\n")

      (setq str regexp)
      (setq search-buffers-regexp regexp)
      (setq search-buffers-regexp-list (moccur-word-split regexp t))
      (setq regexp-lst search-buffers-regexp-list)
      (search-buffers-set-regexp-for-moccur)
      (setq lst nil)

      (while buffers
        (if (and (not arg) (not (buffer-file-name (car buffers))))
            (setq buffers (cdr buffers))
          (let ((currbuf (car buffers)))
            (setq cur-lst regexp-lst)
            (setq buffers (cdr buffers))
            (set-buffer currbuf)
            (setq match t)
            (setq match-text nil)
            (save-excursion
              (while (and cur-lst match)
                (goto-char (point-min))
                (setq regexp (car cur-lst))
                (setq cur-lst (cdr cur-lst))
                (if (re-search-forward regexp nil t)
                    (progn
                      (if (> (- (match-beginning 0) 30) 0)
                          (setq beg (- (match-beginning 0) 30))
                        (setq beg 1))
                      (if (< (+ 30 (match-end 0)) (point-max))
                          (setq end (+ 30 (match-end 0)))
                        (setq end (point-max)))
                      (setq match-text
                            (cons
                             (buffer-substring beg end)
                             match-text)))
                  (setq match nil))))
            (if match
                (progn
                  (let* ((linenum (count-lines (point-min)(point)))
                         (tag (format "\n%3d " linenum))
                         fname)
                    (save-excursion
                      (set-buffer occbuf)
                      (if (buffer-file-name currbuf)
                          (setq fname (buffer-file-name currbuf))
                        (setq fname "Not file"))
                      (insert (concat "Buffer: " (buffer-name currbuf)
                                      " File: " fname "\n"))
                      (while match-text
                        (insert (car match-text))
                        (setq match-text (cdr match-text))
                        (insert " ... \n"))
                      (goto-char (point-max))
                      (insert "\n\n"))))))))
      (switch-to-buffer occbuf)
      (goto-char (point-min))
      (search-buffers-color regexp-lst)
      (setq buffer-read-only t)
      (search-buffers-view-mode 1)
      (search-buffers-next))))

;;;; mode
(defvar search-buffers-view-mode nil
  "*Non-nil means in an search-buffers-view-mode.")
(make-variable-buffer-local 'search-buffers-view-mode)
(defvar search-buffers-view-mode-map nil "")

(setq search-buffers-view-mode-map nil)

(or search-buffers-view-mode-map
    (let ((map (make-sparse-keymap)))
      (define-key map " "
        (function search-buffers-scroll-up))
      (define-key map "b"
        (function search-buffers-scroll-down))
      (define-key map "q"
        (function search-buffers-exit))
      (define-key map "\C-m"
        (function search-buffers-call-moccur))
      ;;(function search-buffers-goto))
      (define-key map "p"
        (function search-buffers-prev))
      (define-key map "n"
        (function search-buffers-next))
      (define-key map "k"
        (function search-buffers-prev))
      (define-key map "j"
        (function search-buffers-next))
      (define-key map '[up]
        (function search-buffers-prev))
      (define-key map '[down]
        (function search-buffers-next))
      (setq search-buffers-view-mode-map map)))

(when (boundp 'minor-mode-map-alist)
  (or (assq 'search-buffers-view-mode-map minor-mode-map-alist)
      (setq minor-mode-map-alist
            (cons (cons 'search-buffers-view-mode
                        search-buffers-view-mode-map)
                  minor-mode-map-alist))))

(defun search-buffers-view-mode (&optional arg)
  (interactive "P")
  (setq search-buffers-view-mode
        (if (null arg)
            (not search-buffers-view-mode)
          (> (prefix-numeric-value arg) 0))))

;;;; function of mode
(defun search-buffers-exit ()
  (interactive)
  (kill-buffer (get-buffer "*Search*"))
  (switch-to-buffer search-buffers-current-buffer)
  (set-window-configuration search-buffers-windows-conf))

(defun search-buffers-set-regexp-for-moccur ()
  "Make regexp for coloring up."
  (let ((list (cdr search-buffers-regexp-list)))
    (if moccur-split-word
        (progn
          (setq search-buffers-regexp-for-moccur
                (concat
                 "\\(" (car search-buffers-regexp-list)))
          (while list
            (setq search-buffers-regexp-for-moccur
                  (concat search-buffers-regexp-for-moccur
                          "\\|"
                          (car list)))
            (setq list (cdr list)))
          (setq search-buffers-regexp-for-moccur
                (concat search-buffers-regexp-for-moccur "\\)")))
      (setq search-buffers-regexp-for-moccur
            (car search-buffers-regexp-list)))))

(defun search-buffers-call-moccur ()
  (interactive)
  (let (bufname
        (windows-conf (current-window-configuration))
        (pos (point)))
    (save-excursion
      (end-of-line)
      (if (re-search-backward moccur-buffer-heading-regexp nil t)
          (setq bufname (buffer-substring
                         (match-beginning 1)
                         (match-end 1)))
        (if (re-search-forward moccur-buffer-heading-regexp nil t)
            (setq bufname (buffer-substring
                           (match-beginning 1)
                           (match-end 1))))))
    (switch-to-buffer (get-buffer bufname))
    (occur-by-moccur search-buffers-regexp-for-moccur t)
    (set-buffer (get-buffer bufname))
    (setq moccur-current-buffer (get-buffer "*Search*"))
    (setq moccur-windows-conf windows-conf)))

(defun search-buffers-goto ()
  (interactive)
  (let (bufname)
    (save-excursion
      (beginning-of-line)
      (if (re-search-forward moccur-buffer-heading-regexp nil t)
          (setq bufname (buffer-substring
                         (match-beginning 1)
                         (match-end 1)))
        (if (re-search-backward moccur-buffer-heading-regexp nil t)
            (setq bufname (buffer-substring
                           (match-beginning 1)
                           (match-end 1)))))
      (switch-to-buffer (get-buffer bufname))
      (delete-other-windows))))

(defun search-buffers-next ()
  (interactive)
  (let (bufname)
    (end-of-line)
    (if (re-search-forward moccur-buffer-heading-regexp nil t)
        (progn
          (switch-to-buffer-other-window
           (get-buffer (buffer-substring-no-properties
                        (match-beginning 1) (match-end 1))))
          (switch-to-buffer-other-window (get-buffer "*Search*"))
          (beginning-of-line)))
    (recenter)))

(defun search-buffers-prev ()
  (interactive)
  (let (bufname)
    (beginning-of-line)
    (if (re-search-backward moccur-buffer-heading-regexp nil t)
        (progn
          (switch-to-buffer-other-window
           (get-buffer (buffer-substring-no-properties
                        (match-beginning 1) (match-end 1))))
          (switch-to-buffer-other-window (get-buffer "*Search*"))
          (beginning-of-line)))))

(defun search-buffers-scroll-up ()
  (interactive)
  (let (bufname)
    (scroll-up)
    (end-of-line)
    (if (re-search-forward moccur-buffer-heading-regexp nil t)
        (progn
          (switch-to-buffer-other-window
           (get-buffer (buffer-substring-no-properties
                        (match-beginning 1) (match-end 1))))
          (switch-to-buffer-other-window (get-buffer "*Search*"))
          (beginning-of-line)))))

(defun search-buffers-scroll-down ()
  (interactive)
  (let (bufname)
    (scroll-down)
    (beginning-of-line)
    (if (re-search-backward moccur-buffer-heading-regexp nil t)
        (progn
          (switch-to-buffer-other-window
           (get-buffer (buffer-substring-no-properties
                        (match-beginning 1) (match-end 1))))
          (switch-to-buffer-other-window (get-buffer "*Search*"))
          (beginning-of-line)))))

;;; color
(defun search-buffers-color (regexp-lst)
  (save-excursion
    (let (ov lst)
      (setq lst regexp-lst)
      (while lst
        (goto-char (point-min))
        (while (re-search-forward
                (car lst) nil t)
          (progn
            (setq ov (make-overlay (match-beginning 0)
                                   (match-end 0)))
            (overlay-put ov 'face 'search-buffers-face)
            (overlay-put ov 'priority 0)))
        (setq lst (cdr lst)))

      (goto-char (point-min))
      (while (re-search-forward
              "^Buffer: " nil t)
        (progn
          (setq ov (make-overlay (match-beginning 0)
                                 (line-end-position)))
          (overlay-put ov 'face 'search-buffers-header-face)
          (overlay-put ov 'priority 0))))))

(provide 'color-moccur)
;;; end
;;; color-moccur.el ends here
