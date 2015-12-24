;;; navi-mode.el --- major-mode for easy buffer-navigation

;; Author: Thorsten Jolitz <tjolitz AT gmail DOT com>
;; Version: 2.0
;; URL: https://github.com/tj64/navi
;; Package-Requires: ((outshine "2.0") (outorg "2.0"))

;;;; MetaData
;;   :PROPERTIES:
;;   :copyright: Thorsten Jolitz
;;   :copyright-years: 2013+
;;   :version:  2.0
;;   :licence:  GPL 2 or later (free software)
;;   :licence-url: http://www.gnu.org/licenses/
;;   :part-of-emacs: no
;;   :author: Thorsten Jolitz
;;   :author_email: tjolitz AT gmail DOT com
;;   :git-repo: https://github.com/tj64/navi.git
;;   :git-clone: git://github.com/tj64/navi.git
;;   :inspiration:  occur-mode org-mode 
;;   :keywords: emacs navigation remote-buffer-control
;;   :END:

;;;; Commentary

;;;;; About navi-mode

;; Navi-mode, as its name suggests, enables super-fast navigation and
;; easy structure-editing in Outshine or Org buffers via one-key
;; bindings in associated read-only *Navi* buffers.

;; You can think of a navi-buffer as a kind of 'remote-control' for an
;; (adecuately) outline-structured original-buffer. Besides navigation
;; and structure-editing, many common commands can be executed in the
;; original-buffer without (necessarily) leaving the navi-buffer. When
;; switching to the original-buffer and coming back after some
;; modifications, the navi-buffer is always reverted (thus
;; up-to-date).

;; Besides the many things that can be done from a navi-buffer, its
;; main benefit is to offer a flexible but persistent and rock-solid
;; overview side-by-side to the details of the original buffer. There
;; can be many different navi-buffers alive at the same time, each one
;; of them firmly connected to its associated original
;; buffer. Switching between the 'twin-buffers' is easy and
;; fast. Typically, an outline-structured original buffer in
;; 'show-all' visibility state shares a splitted window with its
;; associated navi-buffer that either shows headlines, keywords, or a
;; combination of both. Instead of cycling visibility in the original
;; buffer itself it is often more convenient to quickly switch to its
;; navi-buffer and use its many different (over-)views.

;; Navi-mode is implemented on top of occur-mode and thus uses occur
;; as its 'search-engine'. It does not aim to replace occur-mode or to
;; compete with it, it rather specializes occur-mode for a certain
;; use-case. Using navi-mode for remotely controlling Outshine and Org
;; buffers does in no way interfere with occasionally calling 'M-x
;; occur' on these buffers.

;; Navi-mode is part of the Outshine project, consisting of the three
;; libraries outshine.el, outorg.el and navi-mode.el. For navi-mode to
;; work, the original buffer must be either an org-mode buffer or have
;; outline-minor-mode with outshine extensions activated (and be
;; structured with outshine headers, i.e. outcommented Org headers).

;;;;; Usage

;; Navi-mode is a special read-only mode (line e.g. occur-mode and
;; dired-mode), thus all its core commands have one-key
;; bindings. However, the command `navi-edit-mode' makes the
;; navi-buffer editable. The edits are directly applied in the
;; associated original buffer. With command `navi-cease-edit' the
;; default read-only mode is turned on again.

;; Navi-mode's functionality can be divided into the following
;; categories:

;;  - headline searches :: keys '1' to '8' show all headlines up to that level

;;  - keyword searches :: e.g. key 'f' shows functions in many major-modes

;;  - combined headline and keyword searches :: e.g. 'C-3 v' shows
;;       variables and headlines up to level 3

;;  - navigation commands :: e.g. keys 'n' and 'p' move to the
;;       next/previous line in the navi-buffer. These commands are
;;       especially useful in combination with keys 'd', 'o' and 's' that
;;       show the current position in the original buffer (or switch to
;;       it).

;;  - action commands :: call functions on the thing-at-point in the
;;       navi-buffer, to be executed in the 'twin-buffer'. 

;; Besides the mentioned fundamental outline-heading-searches (8
;; outline-levels) and the 5 basic keyword-searches (:FUN, :VAR, :DB,
;; :OBJ and :ALL), all languages can have their own set of searches
;; and keybindings (see customizable variables `navi-key-mappings' and
;; `navi-keywords').

;; Use 'M-s n' (`navi-search-and-switch') to open a navi-buffer and
;; immediately switch to it. The new navi-buffer will show the
;; first-level headings of the original-buffer, with point at the
;; first entry. Here is an overview over the available commands in the
;; navi-buffer:

;; - Show headlines (up-to) different levels:

;; | key     | command            | function-name        |
;; |---------+--------------------+----------------------|
;; | 1 ... 8 | show levels 1 to 8 | navi-generic-command |

;;  - Navigate up and down in the search results shown in the navi-buffer:

;; | key | command   | function-name       |
;; |-----+-----------+---------------------|
;; | p   | previous  | occur-prev          |
;; | n   | next      | occur-next          |
;; | DEL | down page | scroll-down-command |
;; | SPC | up page   | scroll-up-command   |

;; - Revert the navi-buffer (seldom necessary), show help for the
;;    user-defined keyword-searches, and quit the navi-buffer and switch-back
;;    to the original-buffer:

;; | key | command                   | function-name        |
;; |-----+---------------------------+----------------------|
;; | g   | revert buffer             | navi-revert-function |
;; | h   | show help                 | navi-show-help       |
;; | q   | quit navi-mode and switch | navi-quit-and-switch |

;; - Switch to the original-buffer and back to the navi-buffer, display an
;;    occurence in the original-buffer or go to the occurence:

;; | key     | command                | function-name                     |
;; |---------+------------------------+-----------------------------------|
;; | M-s n   | launch navi-buffer     | navi-search-and-switch            |
;; | M-s s   | switch to other buffer | navi-switch-to-twin-buffer        |
;; | M-s M-s |                        |                                   |
;; | s       |                        |                                   |
;; | d       | display occurrence     | occur-mode-display-occurrence     |
;; | o       | goto occurrence        | navi-goto-occurrence-other-window |

;; - Structure editing on subtrees and visibility cycling

;; | key       | command                        | function-name          |
;; |-----------+--------------------------------+------------------------|
;; | TAB       | cycle subtrees                 | navi-cycle-subtree     |
;; | <backtab> | cycle buffer                   | navi-cycle-buffer      |
;; | +         | Demote Subtree                 | navi-demote-subtree    |
;; | -         | promote subtree                | navi-promote-subtree   |
;; | ^         | move up subtree (same level)   | navi-move-up-subtree   |
;; | <         | move down subtree (same level) | navi-move-down-subtree |

;; - Miscancellous actions on subtrees (there are more ...)

;; | key | command                    | function-name                            |
;; |-----+----------------------------+------------------------------------------|
;; | m   | mark thing at point        | navi-mark-thing-at-point-and-switch      |
;; | c   | copy thing at point        | navi-copy-thing-at-point-to-register-s   |
;; | k   | kill thing at point        | navi-kill-thing-at-point                 |
;; | y   | yank killed/copied thing   | navi-yank-thing-at-point-from-register-s |
;; | u   | undo last change           | navi-undo                                |
;; | r   | narrow to thing at point   | navi-narrow-to-thing-at-point            |
;; | w   | widen                      | navi-widen                               |
;; | l   | query-replace              | navi-query-replace                       |
;; | i   | isearch                    | navi-isearch                             |
;; | e   | edit as org (outorg)       | navi-edit-as-org                         |
;; | .   | call fun on thing at point | navi-act-on-thing-at-point               |

;; - Furthermore, there are five (semantically) predefined keyword-searches:

;; | key | keyword-symbol | searches for               |
;; |-----+----------------+----------------------------|
;; | f   | :FUN           | functions, macros etc.     |
;; | v   | :VAR           | vars, consts, customs etc. |
;; | x   | :OBJ           | OOP (classes, methods etc) |
;; | b   | :DB            | DB (store and select)      |
;; | a   | :ALL           | all                        |


;; - And (potentially) many more user-defined keyword-searches
;; (example Emacs Lisp):

;; #+begin_example
;; [KEY] : [SEARCH]
;; ================
;;                 	a : ALL
;;                 	f : FUN
;;                 	v : VAR
;;                 	x : OBJ
;;                 	b : DB
;;                 	F : defun
;;                 	V : defvar
;;                 	C : defconst
;;                 	G : defgroup
;;                 	U : defcustom
;;                 	A : defadvice
;;                 	W : defalias
;;                 	M : defmarcro
;;                 	D : defface
;;                 	S : defstruct
;;                 	B : defsubst
;;                 	L : defclass
;;                 	I : define
;;                 	J : declare
;;                 	K : global-set-key
;;                 	T : add-to-list
;;                 	Q : setq
;;                 	H : add-hook
;;                 	O : hook
;;                 	X : lambda
;;                 	Z : ert
;;                 	R : require

;; #+end_example

;; - Headline-searches and keyword-searches can be combined, e.g.

;; #+begin_example
;;  C-2 f
;; #+end_example

;; in an Emacs Lisp (outshine-)buffer shows all headlines up-to level 2 as
;; well as all function, macro and advice definitions in the original-buffer,

;; #+begin_example
;;  C-5 a
;; #+end_example

;; shows all headlines up-to level 5 as well as all functions, variables,
;; classes, methods, objects, and database-related definitions. The exact
;; meaning of the standard keyword-searches 'f' and 'a' must be defined with a
;; regexp in the customizable variable `navi-keywords' (just like the
;; user-defined keyword-searches).

;; When exploring a (potentially big) original buffer via navi-mode, a common
;; usage pattern is the following:

;;  1. type e.g '2'  and go to the relevant headline
;;  2. type 'r' and e.g. '3' in sequence to narrow buffers to the subtree at
;;     point and show one deeper level of headlines
;;  3. do your thing in the narrowed subtree
;;  4. type e.g. '2' and 'w' to first reduce the headline levels shown and
;;     then widen the buffers again.

;;;;; Installation

;; Install the three required libraries:

;; | navi-mode.el | [[https://github.com/tj64/navi][navi-mode]] |
;; | outshine.el  | [[https://github.com/tj64/outshine][outshine]]  |
;; | outorg.el    | [[https://github.com/tj64/outorg][outorg]]    |

;; from the package-manager via MELPA or clone their github-repos. Follow
;; the installation instructions in `outshine.el' and `outorg.el'.

;; Then install `navi-mode.el' by adding

;; #+begin_example
;;   (require 'navi-mode)
;; #+end_example

;; to your .emacs file.

;;;;; Emacs Version

;; `navi-mode.el' works with [GNU Emacs 24.2.1 (x86_64-unknown-linux-gnu,
;; GTK+ Version 3.6.4) of 2013-01-20 on eric]. No attempts of testing
;; with older versions or other types of Emacs have been made (yet).

;;;; ChangeLog

;; | date            | author(s)       | version |
;; |-----------------+-----------------+---------|
;; | <2014-09-20 Sa> | Thorsten Jolitz |     2.0 |
;; | <2013-05-03 Fr> | Thorsten Jolitz |     1.0 |
;; | <2013-03-11 Mo> | Thorsten Jolitz |     0.9 |

;;; Requires

(require 'outshine)
(require 'outorg)
(require 'thingatpt)

;;; Mode Definitions

(define-derived-mode navi-mode
  occur-mode "Navi"
  "Major mode for easy buffer-navigation.
In this mode (derived from `occur-mode') you can easily navigate
in an associated original-buffer via one-key commands in the
navi-buffer. You can alter the displayed document structure in
the navi-buffer by sending one-key commands that execute
predefined occur searches in the original buffer. `navi-mode' is
especially useful in buffers with outline structure, e.g. buffers
with `outline-minor-mode' activated and `outshine' extensions
loaded.
\\{navi-mode-map}"
  (set (make-local-variable 'revert-buffer-function) 'navi-revert-function)
  ;; (setq case-fold-search nil)
  )

(define-derived-mode navi-edit-mode navi-mode "Navi-Edit"
  "Major mode for editing *Navi* buffers.
In this mode, changes to the *Navi* buffer are also applied to
the originating buffer.

To return to ordinary Navi mode, use \\[navi-cease-edit].
\\{navi-edit-mode-map}"
  (setq buffer-read-only nil)
  (add-hook 'after-change-functions 'occur-after-change-function nil t)
  (message (substitute-command-keys
            "Editing: Type \\[navi-cease-edit] to return to Occur mode.")))


;;; Variables
;;;; Consts
;;;; Vars

(defvar navi-mode-version 2.0
  "Version number of `navi-mode.el'")

(defvar navi "navi"
  "Symbol that holds pairs of buffer-marker names in its plist.
Keys are buffernames as keyword-symbols, values are markers that
point to original-buffers")

(defvar navi-regexp-quoted-line-at-point ""
  "Regexp that matches the line at point in navi-buffer.")

(defvar navi-regexp-quoted-line-before-narrowing ""
  "Regexp that matched the line at point in navi-buffer before narrowing.")

(defvar navi-tmp-buffer-marker (make-marker)
  "Marker for navi-tmp-buffer.")

;;;; Hooks

;; (defvar navi-mode-hook nil
;;   "Hook run after navi-mode is called.")

;;;; Fonts
;;;; Customs
;;;;; Custom Groups

(defgroup navi-mode nil
  "Library for outline navigation and Org-mode editing in Lisp buffers."
  :prefix "navi-"
  :group 'lisp)

;;;;; Custom Vars

(defcustom navi-key-mappings
  '(("emacs-lisp" . ((:ALL . "a")
                     (:FUN . "f")
                     (:VAR . "v")
                     (:OBJ . "x")
                     (:DB . "b")
                     (:defun . "F")
                     (:defvar . "V")
                     (:defconst . "C")
                     (:defgroup . "G")
                     (:defcustom . "U")
                     (:defadvice . "A")
                     (:defalias . "W")
                     (:defmarcro . "M")
                     (:defface . "D")
                     (:defstruct . "S")
                     (:defsubst . "B")
                     (:defclass . "L")
                     (:define . "I")
                     (:declare . "J")
                     (:global-set-key . "K")
                     (:add-to-list . "T")
                     (:setq . "Q")
                     (:add-hook . "H")
                     (:hook . "O")
                     (:lambda . "X")
                     (:ert . "Z")
                     (:marker . "P")
                     (:require . "R")
		     (:eval-after-load . "N")))
    ("ess" . ((:ALL . "a")
              (:FUN . "f")
              (:VAR . "v")
              (:OBJ . "x")
              (:DB . "b")
              (:objects . "X")
              (:methods . "Y")
              (:inout . "R")
              (:datacreation . "C")
              (:slicing . "[")
              (:varconversion . "A")
              (:varinfo . "I")
              (:dataselection . "W")
              (:math . "M")
              (:matrices . "]")
              (:advdataprocessing . "O")
              (:strings . "_")
              (:datestimes . ":")
              (:plotting . "P")
              (:lowlevelplotting . "L")
              (:trellisgraphics . "T")
              (:modelfitting . "~")
              (:statistics . "S")
              (:distributions . "D")
              (:programming . "{")
              (:assignment . "=")
              (:environment . "U")))
    ("picolisp" . ((:ALL . "a")
                   (:FUN . "f")
                   (:VAR . "v")
                   (:OBJ . "x")
                   (:DB . "b")
                   (:de . "D")
                   (:def . "F")
                   (:class . "C")
                   (:dm . "M")
                   (:rel . "R")
                   (:var . "V")
                   (:extend . "X")
                   (:obj . "O")
                   (:object . "J")
                   (:new . "N")
                   (:symbols . "S")
                   (:pool . "L")
                   (:tree . "T")
                   (:clause . "U")
                   (:goal . "K")
                   (:be . "B")
                   (:prove . "P")
                   (:gui . "G")
                   (:grid . "I")
                   (:table . "A")
                   (:spread . "Z")
                   (:form . "Y")
                   (:action . "W")
                   (:html . "H")))
    ("org" . (;; (:ALL . "a")
              ;; (:FUN . "f")
              ;; (:VAR . "v")
              ;; (:OBJ . "x")

              (:srcblock . "b")
              (:time . "x")
              (:inline-srcblock . "I")
              ;; (:affkeywords . "k")
              ;; (:table . "t")
              (:srcname-w-name . "W")
              (:multilineheader . "M")
              (:priority . "Y")
              (:target . "T")
              (:radiotarget . "R")
              (:drawer . "D")
              (:timestamp . "S")
              (:srcname . "N")
              (:result . "U")
              (:result-w-name . "Z")
              (:options . "O")
              (:propertydrawer . "P")
              (:deadline . "A")
              (:scheduled-time-hour . "H")
              ;; (:checkbox . "B")
              ;; (:list . "L")
              ;; (:propertydrawer . "P")
              ;; (:attr . "A")
              ;; (:caption . "C")
              ;; (:header . "H")
              ;; (:plot . "O")
              ;; (:footnotedef . "F")
              ;; (:latex . "X")
              ))
    ("latex" . ((:ALL . "a")
		(:FUN . "f")
		(:VAR . "v")
		(:OBJ . "x")
		(:figure . "F")
		(:table . "T")
		(:listing . "L")
		(:index . "I")
		(:ref . "R")
		(:refrange . "A")
		(:refall . "V"))))

  "Mappings between keybindings and keyword-symbols used in `navi-keywords'.

All ASCII printing characters (see
http://www.csgnetwork.com/asciiset.html) are available as keys,
except those used for the core commands of 'navi-mode' itself:

| key | command                        |
|-----+--------------------------------|
| p   | previous                       |
| n   | next                           |
| DEL | page up                        |
| SPC | page down                      |
| g   | revert buffer                  |
| d   | display occurrence             |
| o   | goto occurrence                |
| c   | copy subtree                   |
| e   | edit subtree as org            |
| E   | make navi-buffer editable      |
| m   | mark subtree                   |
| u   | undo last change               |
| z   | mail subtree                   |
| r   | narrow to subtree              |
| w   | widen                          |
| s   | switch (to original buffer)    |
| k   | kill subtree                   |
| i   | isearch in subtree             |
| l   | query-replace in subtree       |
| y   | yank killed/copied subtree     |
| q   | quit navi-mode and switch      |
| h   | show help                      |
| +   | demote subtree                 |
| -   | promote subtree                |
| \^  | move up subtree (same level)   |
| <   | move down subtree (same level) |


And you should not use the following keys and (uppercase)
keyword-symbols for other than the (semantically) predefined
keywords-searches. They define the 5 standard occur-searches that
should be available for every programming language, with the same
keybindings and similar semantics:

| key | keyword-symbol | command                    |
|-----+----------------+----------------------------|
| f   | :FUN           | functions, macros etc.     |
| v   | :VAR           | vars, consts, customs etc. |
| x   | :OBJ           | OOP (classes, methods etc) |
| b   | :DB            | DB (store and select)      |
| a   | :ALL           | all                        |

All other ASCII printing characters are free and can be used as
one-key keybindings for occur-searches for a programming
language. The keybindings are independent for different
programming languages, so while it would be a good thing to have
similar bindings in different languages, it is by no means
necessary.

Defining occur-searches for a programming language is a two-step
process:

 1. Customize `navi-key-mappings', i.e. add a new language-alist
    and populate it with pairs of keyword-symbols (that should
    represent the language keywords searched for) and ASCII
    characters (as strings of length 1).

 2. Customize `navi-keywords', i.e. add a new language alist and
    populate it with pairs of keyword-symbols (that should
    represent the language keywords searched for) and regexps,
    using exactly the same keyword-symbols as in
    `navi-key-mappings'.

Thus, the following two entries together will map the keybinding
'a' to an occur-search with the regexp:

\"^[[:space:]]*(def[a-z]+\":

;; #+begin_src emacs-lisp
;; (defcustom navi-key-mappings
;;   '((\"emacs-lisp\" . ((:ALL . \"a\") ... ))))

;; (defcustom navi-keywords
;;   '((\"emacs-lisp\" . ((:ALL . \"^[[:space:]]*(def[a-z]+ \") ...))))
;; #+end_src

There is no need for a third step - defining the keybindings. In
`navi-mode', there are by default keybindings defined for all
ASCII printing characters. Conditional on the programming
language major-mode of the original-buffer, navi-mode checks the
customizable variables `navi-key-mappings' and `navi-keywords'
for an entry with a key pressed by the user. If it doesn't find
one, nothing happens, if it finds one, it looks up the associated
regexp and performs an occur-search with it."
  :group 'navi-mode
  :type '(alist :key-type string
                :value-type alist))

(defcustom navi-keywords
  '(("emacs-lisp" . ((:ALL . "^[[:space:]]*(def[a-z]+\\*? ")
                     (:OBJ . "^[[:space:]]*(def[smc][^auo][a-z]+ ")
                     (:VAR . "^[[:space:]]*(def[vcgf][^l][a-z]+ ")
                     (:FUN
                      . "^[[:space:]]*(def[maus][^eltu][a-z]*\\*? ")
                     (:defun . "^[[:space:]]*(defun\\*? ")
                     (:defvar . "^[[:space:]]*(defvar ")
                     (:defconst . "^[[:space:]]*(defconst ")
                     (:defgroup . "^[[:space:]]*(defgroup ")
                     (:defcustom . "^[[:space:]]*(defcustom ")
                     (:defadvice . "^[[:space:]]*(defadvice ")
                     (:defalias . "^[[:space:]]*(defalias ")
                     (:defmarcro . "^[[:space:]]*(defmacro\\*? ")
                     (:defface . "^[[:space:]]*(defface ")
                     (:defstruct . "^[[:space:]]*(defstruct ")
                     (:defsubst . "^[[:space:]]*(defsubst ")
                     (:defclass . "^[[:space:]]*(defclass ")
                     (:defmethod . "^[[:space:]]*(defmethod ")
                     (:declare . "^[[:space:]]*(declare-")
                     (:define . "^[[:space:]]*(define-")
                     (:global-set-key
		      . "^[[:space:]]*(global-set-key ")
                     (:add-to-list . "^[[:space:]]*(add-to-list ")
                     (:setq . "^[[:space:]]*(setq ")
                     (:add-hook . "^[[:space:]]*(add-hook ")
                     (:hook . "-hook-?")
                     (:lambda . "(lambda (")
                     (:ert . "^[[:space:]]*(ert-")
                     (:marker . "^[[:space:]]*([a-z]+-marker")
                     (:require . "^[[:space:]]*([a-z-]*require ")
		     (:eval-after-load
		      . "^[[:space:]]*(eval-after-load ")))
    ("ess" . ((:ALL . (concat
                       "\\("
                       "[^\s\t\n]* ?<?-? ?function("
                       "\\|"
                       "[^\s\t\n]+ <- [^\s\t\n]+"
                       "\\|"
                       "\\(setClass(\\|representation(\\|prototype(\\|"
                       "setIs(\\|setValidity(\\|extends(\\|setAs(\\|"
                       "setGeneric(\\|setMethod(\\|setOldClass(\\)"
                       "\\|"
                       "\\(sql\\(Tables\\|Columns\\|PrimaryKeys\\|Fetch\\|"
                       "Query\\|GetResults\\|Save\\|Update\\|FetchMore\\)"
                       "(\\|odbc\\(Close\\|CloseAll\\|Connect\\|GetInfo\\|"
                       "Query\\|Tables\\|Columns\\|PrimaryKeys\\|"
                       "FetchResults\\|GetErrMsg\\)(\\|db\\(Connect\\|"
                       "Driver\\|ListConnections\\|GetInfo\\|ListTables\\|"
                       "ListFields\\|GetQuery\\|SendQuery\\|GetException\\|"
                       "ReadTable\\|WriteTable\\|RemoveTable\\|Disconnect\\|"
                       "UnloadDriver\\)(\\)"
                       "\\)"))
              (:FUN . "[^\s\t\n]* ?<?-? ?function(")
              (:VAR . "[^\s\t\n]+ <- [^\s\t\n]+")
              (:OBJ . (concat
                       "\\(setClass(\\|representation(\\|prototype(\\|"
                       "setIs(\\|setValidity(\\|extends(\\|setAs(\\|"
                       "setGeneric(\\|setMethod(\\|setOldClass(\\)"))
              (:DB . (concat
                      "\\(sql\\(Tables\\|Columns\\|PrimaryKeys\\|Fetch\\|"
                      "Query\\|GetResults\\|Save\\|Update\\|FetchMore\\)"
                      "(\\|odbc\\(Close\\|CloseAll\\|Connect\\|GetInfo\\|"
                      "Query\\|Tables\\|Columns\\|PrimaryKeys\\|"
                      "FetchResults\\|GetErrMsg\\)(\\|db\\(Connect\\|"
                      "Driver\\|ListConnections\\|GetInfo\\|ListTables\\|"
                      "ListFields\\|GetQuery\\|SendQuery\\|GetException\\|"
                      "ReadTable\\|WriteTable\\|RemoveTable\\|Disconnect\\|"
                      "UnloadDriver\\)(\\)"))
              (:methods . (concat
                           "\\(\\(Use\\|set\\|dump\\|remove\\|get\\|select\\|"
                           "exists\\|has\\|find\\|show\\|getS3\\)?"
                           "[mM]ethods?(\\|\\(set\\|is\\|remove\\|get\\)"
                           "Generics?(\\|isGroup(\\|findFunction(\\|"
                           "signature(\\)"))
              (:objects . (concat
                           "\\(new(\\|initialize(\\|slot(\\|"
                           "[^[:space:]([{]+@[^[[:space:])}]+\\|"
                           "[[:space:]([{]is(\\|slotNames(\\|getSlots(\\|"
                           "[[:space:]([{]class(\\)"))
              (:inout . (concat
                         "\\(load(\\|read\\.[^[:space:])[(}{]+(\\|"
                         "library(\\|save[.(]\\|cat(\\|print(\\|format(\\|"
                         "write\.table(\\|sink(\\)"))
              (:datacreation . (concat
                                "\\(c(\\|[[:digit:]]+:[[:digit:]]+\\|"
                                "seq(\\|rep(\\|data\\.frame(\\|list(\\|"
                                "array(\\|matrix(\\|factor(\\|gl(\\|"
                                "expand\\.grid(\\|rbind(\\|cbind(\\)"))
              (:slicing . (concat
                           "\\([[:alpha:].:$@]+\\[[^]]+\\]\\|"
                           "[[:alpha:].:$@]+\\[\\[[^]]+\\]\\]\\|"
                           "[[:alpha:].:$@]+$[[:alpha:]][[:alpha:].:$@]+\\)"))
              (:varconversion . (concat
                                 "\\("
                                 "[ (\\[{]as[.(][^\s\t\n(]*(\\|"
                                 "^as[.(][^\s\t\n(]*(\\)"))
              (:varinfo . (concat
                           "\\("
                           "[ (\\[{]is[.(][^\s\t\n(]*(\\|"
                           "^is[.(][^\s\t\n(]*(\\|"
                           "length(\\|dim(\\|dimnames(\\|nrow(\\|"
                           "ncol(\\|NCOL(\\|class(\\|unclass(\\|"
                           "attr(\\|attributes(\\)"))
              (:dataselection . (concat
                                 "\\("
                                 "[ (\\[{]na[.(][^\s\t\n(]*(\\|"
                                 "^na[.(][^\s\t\n(]*(\\|"
                                 "which[.(]\\|rev(\\|sort(\\|cut(\\|"
                                 "choose(\\|unique(\\\|table(\\|subset(\\"
                                 "sample(\\|prop\\.table(\\]\\)"))
              (:math . (concat
                        "\\(sin(\\|cos(\\|tan(\\|asin(\\|acos(\\|atan(\\|"
                        "atan2(\\|log(\\|log10(\\|exp(\\|max(\\|min(\\|"
                        "range(\\|sum(\\|diff(\\|prod(\\|mean(\\|median(\\|"
                        "quantile(\\|weighted\\.mean(\\|rank(\\|var(\\|"
                        "sd(\\|cor(\\|round(\\|log(\\|scale(\\|pmin(\\|"
                        "pmax(\\|cumsum(\\|cumprod(\\|cummin(\\|cummax(\\|"
                        "union(\\\|intersect(\\|setdiff(\\|setequal(\\|"
                        "is\\.element(\\|Re(\\|Im(\\|Mod(\\|Arg(\\|Conj(\\|"
                        "convolve(\\|fft(\\|mvfft(\\|filter(\\)"))
              (:matrices . (concat
                            "\\("
                            "[ (\\[{]t(\\|^t(\\|diag(\\|solve(\\|rowsum(\\|"
                            "colsum(\\|rowMeans(\\|colMeans(\\|rowSums(\\|"
                            "%\\*%\\)"))
              (:advdataprocessing . (concat
                                     "\\([lstv]?apply(\\|by(\\|merge(\\|"
                                     "xtabs(\\|aggregate(\\|stack(\\|"
                                     "unstack(\\|reshape(\\)"))
              (:strings . (concat
                           "\\(paste(\\|substr(\\|strsplit(\||grep(\\|"
                           "gsub(\\|tolower(\\|toupper(\\|match(\\"
                           " %in% \\|pmatch(\\|nchar(\\)"))
              ;; 'format' here?
              (:datestimes . (concat
                              "\\(as\\.Date(\\|as\\.POSIXct(\\|"
                              "format(\\|difftime(\\)"))
              (:plotting . (concat
                            "\\([a-z.]*plot\\.?[a-z.]*(\\|hist(\\|"
                            "dotchart(\\|pie(\\|pairs(\\|qqnorm(\\|"
                            "[a-z.]*contour(\\|image(\\|persp(\\|"
                            "stars(\\|symbols(\\)"))
              (:lowlevelplotting . (concat
                                    "\\(points(\\|lines(\\|[m]?text(\\|"
                                    "segments(\\|arrows(\\|abline(\\|"
                                    "[\s\t(\\[{]rect(\\|polygon(\\|legend(\\|"
                                    "title(\\|axis(\\|rug(\\|locator(\\|"
                                    "^rect(\\|par(\\)"))
              (:trellisgraphics . (concat
                                   "\\(xyplot(\\|barchart(\\|dotplot(\\|"
                                   "densityplot(\\|histogram(\\|bwplot(\\|"
                                   "qqmath(\\|stripplot(\\|qq(\\|splom(\\|"
                                   "parallel(\\|levelplot(\\|wireframe(\\|"
                                   "cloud(\\|lattice[a-z.]*(\\|lset(\\)"))
              (:modelfitting . (concat
                                "\\(optim(\\|[ng]?lm(\\|nls(\\|approx(\\|"
                                "spline(\\|loess(\\|predict(\\|fitted(\\|"
                                "[a-z.]*residual[s]?(\\|coef(\\|AIC(\\|"
                                "deviance(\\|logLik(\\)"))
              (:statistics . "\\(aov(\\|anova(\\|density(\\|[a-z.]*test(\\)")
              (:distributions . (concat
                                 "\\([\s\t(\\[{][rdpq]\\|^[rdpq]\\)"
                                 "\\(norm(\\|exp(\\|gamma(\\|pois(\\|"
                                 "weibull(\\|cauchy(\\\|beta(\\|t(\\|f(\\|"
                                 "chisq(\\|binom(\\|geom(\\|hyper(\\|"
                                 "logis(\\|lnorm(\\|nbinom(\\|unif(\\|"
                                 "wilcox(\\)"))
              ;; makes no sense to search for ifs and loops
              (:programming . "\\(function(\\|return(\\)")
              (:assignment . " ?<- ?")
              (:environment . (concat
                               "\\(assign(\\|get(\\|exists(\\|objects(\\|"
                               "remove(\\|[\s\t(\\[{]rm(\\|search(\\|searchpaths(\\|"
                               "attach(\\|detach(\\|emptyenv(\\|parent\\.env(\\|"
                               "baseenv(\\|globalenv(\\|environment(\\|"
                               "new\\.env(\\|\\.GlobalEnv\\)"))))
    ("picolisp" . ((:de . "^[[:space:]]*(de ")
                   (:def . "^[[:space:]]*(def ")
                   (:class . "^[[:space:]]*(class ")
                   (:dm . "^[[:space:]]*(dm ")
                   (:rel . "^[[:space:]]*(rel ")
                   (:var . "^[[:space:]]*(var ")
                   (:extend . "^[[:space:]]*(extend ")
                   (:obj . "^[[:space:]]*(obj ")
                   (:object . "^[[:space:]]*(object ")
                   (:new . "^[[:space:]]*(new ")
                   (:symbols . "^[[:space:]]*(symbols ")
                   (:pool . "^[[:space:]]*(pool ")
                   (:tree . "^[[:space:]]*(tree ")
                   (:clause . "^[[:space:]]*(clause ")
                   (:goal . "^[[:space:]]*'?(goal ?")
                   (:be . "^[[:space:]]*(be ?")
                   (:prove . "^[[:space:]]*(prove ?")
                   (:gui . "^[[:space:]]*(gui ?")
                   (:grid . "^[[:space:]]*(<grid> ?")
                   (:table . "^[[:space:]]*(<table> ?")
                   (:spread . "^[[:space:]]*(<spread> ?")
                   (:form . "^[[:space:]]*([^ ]*form ?")
                   (:action . "^[[:space:]]*(action ?")
                   (:html . "^[[:space:]]*(html ?")
                   (:ALL . (concat
                            "^[[:space:]]*("
                            "\\(de \\|"
                            "def \\|"
                            "symbols \\|"
                            "var \\|"
                            "class \\|"
                            "extend \\|"
                            "dm \\|"
                            "var \\|"
                            "rel \\|"
                            "pool \\|"
                            "obj \\|"
                            "object \\|"
                            "tree \\|"
                            "new \\|"
                            "prove \\|"
                            "clause \\|"
                            "goal \\|"
                            "be \\)"))
                   (:VAR . (concat
                            "^[[:space:]]*("
                            "\\(var \\|"
                            "rel \\)"))
                   (:OBJ . (concat
                            "^[[:space:]]*("
                            "\\(class \\|"
                            "extend \\|"
                            "dm \\|"
                            "var \\|"
                            "rel \\)"))
                   (:DB . (concat
                           "^[[:space:]]*("
                           "\\(pool \\|"
                           "obj \\|"
                           "object \\|"
                           "tree \\|"
                           "new \\|"
                           "prove \\|"
                           "clause \\|"
                           "goal \\|"
                           "be \\)"))
                   (:FUN . (concat
                            "^[[:space:]]*("
                            "\\(de \\|"
                            "def \\|"
                            "symbols \\)"))))
    ("org" . ((:srcblock
               . (concat
                  ;; (1) indentation                 (2) lang
                  "^\\([ \t]*\\)#\\+begin_src[ \t]+\\([^ \f\t\n\r\v]+\\)[ \t]*"
                  ;; (3) switches
                  "\\([^\":\n]*\"[^\"\n*]*\"[^\":\n]*\\|[^\":\n]*\\)"
                  ;; (4) header arguments
                  "\\([^\n]*\\)"))
              ;; ;; (5) body
              ;; "\n\\([^\000]*?\n\\)?[ \t]*#\\+end_src")
              (:inline-srcblock
               .   (concat
                    ;; (1) replacement target (2) lang
                    "\\(?:^\\|[^-[:alnum:]]\\)\\(src_\\([^ \f\t\n\r\v]+\\)"
                    ;; (3,4) (unused, headers)
                    "\\(\\|\\[\\(.*?\\)\\]\\)"
                    ;; (5) body
                    "{\\([^\f\n\r\v]+?\\)}\\)"))
              ;; (:affkeywords . "k")
              ;; (:table . "t")
              (:srcname-w-name
               . (concat "^[ \t]*#\\+name:[ \t]*"
                         "\\("
                         "^[ \t]*#\\+headers?:[ \t]*\\([^\n]*\\)$"
                         "\\)*"
                         "\\([^ ()\f\t\n\r\v]+\\)\\(\(\\(.*\\)\)\\|\\)"))
              (:multilineheader
               . "^[ \t]*#\\+headers?:[ \t]*\\([^\n]*\\)$")
              (:srcname . "^[ \t]*#\\+name:[ \t]*")
              (:priority . ".*?\\(\\[#\\([A-Z0-9]\\)\\] ?\\)")
              (:radiotarget . "<<<\\([^<>\n\r]+\\)>>>")
              (:target . "<<\\([^<>\n\r]+\\)>>")
              (:propertydrawer
               . (concat "\\(^[ \\t]*:PROPERTIES:[ \\t]*$\\)[^\\000]*?"
                         "\\(^[ \\t]*:END:[ \\t]*$\\)\\n?"))
              (:timestamp
               . (concat "<\\([0-9]\\{4\\}-[0-9]\\{2\\}"
                         "-[0-9]\\{2\\} ?[^\r\n>]*?\\)>"))
              (:result
               .   (concat "^[ \t]*#\\+"
                           (regexp-opt org-babel-data-names t)
                           "\\(\\[\\("
                           ;; FIXME The string below is `org-ts-regexp'
                           "<\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} ?"
                           "[^\r\n>]*?\\)>"
                           " \\)?\\([[:alnum:]]+\\)\\]\\)?\\:[ \t]*"))

              (:result-w-name
               .   (concat "\\("
                           "^[ \t]*#\\+"
                           (regexp-opt org-babel-data-names t)
                           "\\(\\[\\("
                           ;; FIXME The string below is `org-ts-regexp'
                           "<\\([0-9]\\{4\\}-[0-9]\\{2\\}-[0-9]\\{2\\} ?"
                           "[^\r\n>]*?\\)>"
                           " \\)?\\([[:alnum:]]+\\)\\]\\)?\\:[ \t]*"
                           "\\([^ ()\f\t\n\r\v]+\\)\\(\(\\(.*\\)\)\\|\\)"
                           "\\)"))
              (:options
               . (concat
                  "^#\\+\\(CATEGORY\\|TODO\\|COLUMNS\\|STARTUP\\|ARCHIVE\\|"
                  "LINK\\|PRIORITIES\\|CONSTANTS\\|PROPERTY\\|DRAWERS\\|"
                  "SETUPFILE\\|OPTIONS\\|\\(?:[a-zA-Z][0-9a-zA-Z_]*_TODO\\)"
                  "\\):[        ]*\\(.*\\)"))
              (:drawer . "^[    ]*:\\(PROPERTIES\\|LOGBOOK\\):[         ]*$")
              (:deadline . "\\<\\(DEADLINE:\\).*")
              (:scheduled-time-hour
               . "\\<SCHEDULED: *<\\(.+[0-9]\\{1,2\\}:[0-9]\\{2\\}[^>]*\\)>")
              (:time
               . (conat "\\(\\<\\(SCHEDULED:\\|DEADLINE:\\|CLOSED:\\|"
                        "CLOCK:\\)\\)? *\\([[<][0-9]\\{4\\}-[0-9]\\{2\\}"
                        "-[0-9]\\{2\\} ?[^]\r\n>]*?[]>]\\|<%%([^\r\n>]*>\\)"))
              ;; (:checkbox . "B")
              ;; (:list . "L")

              ;; (:attr . "A")
              ;; (:caption . "C")
              ;; (:header . "H")
              ;; (:name . "N")
              ;; (:plot . "O")
              ;; (:footnotedef . "F")
              ;; (:latex . "X")
              ))
    ("latex" . ((:ALL . (concat
		      "^[[:space:]]*\\\\[[:word:]]+"
		      "\\(?:\\[.*]\\)?\\(?:{.+}\\)?"))
		(:FUN . (concat
		      "^[[:space:]]*\\\\[[:word:]]+"
		      "\\(?:\\[.*]\\)[^{]"))
		(:VAR . (concat
		       "^[[:space:]]*\\\\[[:word:]]+"
		       "\\(?:\\[.*]\\)\\(?:{.+}\\)"))
		(:OBJ . (concat
		      "^[[:space:]]*\\\\[[:word:]]+"
		      "\\(?:{.*}\\)"))
		(:figure . (concat
		       "^[[:space:]]*\\\\begin{figure}"
		       "[^^\000]+?\\\\end{figure}"))
		(:table . (concat
		       "^[[:space:]]*\\\\begin{table}"
		       "[^^\000]+?\\\\end{table}"))
		(:listing . (concat
		       "^[[:space:]]*\\\\begin{listing}"
		       "[^^\000]+?\\\\end{listing}"))
		(:index . "\\\\index{[^^\000]+?}")
		(:ref . "\\\\v?ref{[^^\000]+?}")
		(:refrange . (concat
			      "\\\\vrefrange{[^^\000]+?}"
			      "{[^^\000]+?}"))
		(:refall . "\\\\v?ref"))))

  "Alist of language-specific keywords for occur-searches in
  navi-mode.

This customization variable holds a nested alist with 2 levels:

1st level:

The name of the language (key-string) should be the associated
major-mode name without the '-mode' suffix. Run 'M-x major-mode'
in a buffer to find out about the name, in an Emacs Lisp buffer
you get 'emacs-lisp-mode', in a PicoLisp buffer you get
'picolisp-mode', thus the alist keys for these two languages
should be 'emacs-lisp' and 'picolisp'.

2nd level:

The keys of each language-alist are keywords-symbols used for
selecting the regexp, the value is the regexp itself"
  :group 'navi-mode
  :type '(alist :key-type string
                :value-type alist))

;;; Defuns
;;;; Functions
;;;;; Hook Function

;; (defun navi-mode-hook-function ()
;;   "Function to be run after `navi-mode' is loaded.")

;;;;; Utility Functions

;; copied from http://www.emacswiki.org/emacs/basic-edit-toolkit.el
(defun navi-underline-line-with (char)
  "Insert some char below at current line."
  (interactive "cType one char: ")
  (save-excursion
    (let ((length (- (point-at-eol) (point-at-bol))))
      (end-of-line)
      (insert "\n")
      (insert (make-string length char)))))

(defun navi-non-empty-string-p (str)
  "Return t if function argument STR is a string of length > 0, nil otherwise."
  (if (and (stringp str) (> (length str) 0))
      str
    nil))

;;;;; Navi Generic Command

(defun navi-map-keyboard-to-key (language kbd-key)
  "Map pressed keyboard-key KBD-KEY to key in `navi-keywords'."
  (let ((mappings (navi-get-language-alist language 'MAPPINGS)))
    (and (rassoc kbd-key mappings)
         (car (rassoc kbd-key mappings)))))

(defun navi-msg (key language)
  "Tell user that key is not defined for language."
  (message "Key %s is not defined for language %s" key language))

;;;;; Occur Search

;; modified `occur-1' from `replace.el'
(defun navi-1 (regexp nlines bufs &optional buf-name)
  (unless (and regexp (not (equal regexp "")))
    (error "Occur doesn't work with the empty regexp"))
  (unless buf-name
    (setq buf-name "*Navi*"))
  (let (occur-buf
        (active-bufs (delq nil (mapcar #'(lambda (buf)
                                           (when (buffer-live-p buf) buf))
                                       bufs))))
    ;; Handle the case where one of the buffers we're searching is the
    ;; output buffer.  Just rename it.
    (when (member buf-name (mapcar 'buffer-name active-bufs))
      (with-current-buffer (get-buffer buf-name)
        (rename-uniquely)))

    ;; Now find or create the output buffer.
    ;; If we just renamed that buffer, we will make a new one here.
    (setq occur-buf (get-buffer-create buf-name))

    (with-temp-buffer
      (move-marker navi-tmp-buffer-marker (point))
      (if (stringp nlines)
          (fundamental-mode) ;; This is for collect operation.
        (navi-mode))
      (let ((inhibit-read-only t)
            ;; Don't generate undo entries for creation of the initial contents.
            (buffer-undo-list t))
        (let ((count
               (if (stringp nlines)
                   ;; Treat nlines as a regexp to collect.
                   (let ((bufs active-bufs)
                         (count 0))
                     (while bufs
                       (with-current-buffer (car bufs)
                         (save-excursion
                           (goto-char (point-min))
                           (while (re-search-forward regexp nil t)
                             ;; Insert the replacement regexp.
                             (let ((str (match-substitute-replacement nlines)))
                               (if str
                                   (with-current-buffer
                                       (marker-buffer navi-tmp-buffer-marker)
                                     (insert str)
                                     (setq count (1+ count))
                                     (or (zerop (current-column))
                                         (insert "\n"))))))))
                       (setq bufs (cdr bufs)))
                     count)
                 ;; Perform normal occur.
                 (occur-engine
                  regexp active-bufs (marker-buffer navi-tmp-buffer-marker)
                  (or nlines list-matching-lines-default-context-lines)
                  (if (and case-fold-search search-upper-case)
                      (isearch-no-upper-case-p regexp t)
                    case-fold-search)
                  list-matching-lines-buffer-name-face
                  nil list-matching-lines-face
                  (not (eq occur-excluded-properties t))))))
          (let* ((bufcount (length active-bufs))
                 (diff (- (length bufs) bufcount)))
            (message "Searched %d buffer%s%s; %s match%s%s"
                     bufcount (if (= bufcount 1) "" "s")
                     (if (zerop diff) "" (format " (%d killed)" diff))
                     (if (zerop count) "no" (format "%d" count))
                     (if (= count 1) "" "es")
                     ;; Don't display regexp if with remaining text
                     ;; it is longer than window-width.
                     (if (> (+ (length regexp) 42) (window-width))
                         "" (format " for `%s'" (query-replace-descr regexp)))))
          (if (= count 0)
              nil
            (with-current-buffer occur-buf
              (setq occur-revert-arguments (list regexp nlines bufs))
              (erase-buffer)
              (insert-buffer-substring
               (marker-buffer navi-tmp-buffer-marker))
              (display-buffer occur-buf)
              (setq next-error-last-buffer occur-buf)
              (setq buffer-read-only t)
              (set-buffer-modified-p nil)
              (run-hooks 'occur-hook)))))
      (set-marker navi-tmp-buffer-marker nil))))

(defun navi-show-headers (level &optional args)
  "Show headers up-to level LEVEL."
  (let ((org-promo-headers
         (and (eq major-mode 'navi-mode)
              (with-current-buffer
                  (marker-buffer
                   (cadr (navi-get-twin-buffer-markers)))
                (and
                 (eq major-mode 'org-mode)
                 outline-promotion-headings)))))
    (if args
        (navi-revert-function
         (if org-promo-headers
             (navi-calc-org-mode-headline-regexp
              level
              org-promo-headers
              'NO-PARENT-LEVELS)
           (navi-calc-headline-regexp level 'NO-PARENT-LEVELS)))
      (navi-revert-function
       (if org-promo-headers
           (navi-calc-org-mode-headline-regexp
            level
            org-promo-headers)
         (navi-calc-headline-regexp level))))))


(defun navi-show-keywords (key)
  "Show matches of occur-search with KEY.
Language is derived from major-mode."
  (let ((language (navi-get-language-name)))
    (navi-revert-function
     (navi-get-regexp language
                      (navi-map-keyboard-to-key language key)))))

(defun navi-show-headers-and-keywords (level key &optional args)
  "Show headers up-to level LEVEL and matches of occur-search with KEY.
Language is derived from major-mode."
  (let* ((language (navi-get-language-name))
         (org-promo-headers
          (and (eq major-mode 'navi-mode)
               (with-current-buffer
                   (marker-buffer
                    (cadr (navi-get-twin-buffer-markers)))
                 (and
                  (eq major-mode 'org-mode)
                  outline-promotion-headings))))
         (rgxp
          (navi-make-regexp-alternatives
           (if args
               (if org-promo-headers
                   (navi-calc-org-mode-headline-regexp
                    level
                    org-promo-headers
                    'NO-PARENT-LEVELS)
                 (navi-calc-headline-regexp level 'NO-PARENT-LEVELS))
             (if org-promo-headers
                 (navi-calc-org-mode-headline-regexp
                  level
                  org-promo-headers)
               (navi-calc-headline-regexp level)))
           (navi-get-regexp language
                            (navi-map-keyboard-to-key language key)))))
    (navi-revert-function rgxp)))

;;;;; Regexps

(defun navi-get-regexp (language key)
  "Return the value of KEY for LANGUAGE in `navi-keywords'."
  (if (not (and (navi-non-empty-string-p language)
                (assoc language navi-keywords)))
      (progn
        (message
         (format "%s%s%s"
                 "Language "
                 language
                 " not registered in 'navi-keywords'"))
        nil)
    (let* ((result (assoc key (cdr (assoc language navi-keywords))))
           (rgxp  (and result (cdr result))))
      (cond
       ((stringp rgxp) rgxp)
       ((and (listp rgxp) (functionp (car rgxp)) (eval rgxp)))
       (t nil)))))

;; TODO deeper test of the results
(defun navi-make-regexp-alternatives (&rest rgxps)
  "Enclose the set of regexp alternatives.
The regexps are given as the list of strings RGXPS."
  (and rgxps
       (replace-regexp-in-string
        (regexp-quote "\\|\\)")
        (regexp-quote "\\)")
        (concat
         "\\("
         (mapconcat
          'identity rgxps "\\|")
         "\\)"))))

(defun navi-calc-headline-regexp (level &optional NO-PARENT-LEVELS)
  "Calculate regexp to show headers of original-buffer.
Regexp should result in an occur-search showing up to
outline-level LEVEL headlines in navi-buffer. If NO-PARENT-LEVELS
in non-nil, only headers of level LEVEL are shown."
  (let* ((orig-buf (marker-buffer
                    (cadr (navi-get-twin-buffer-markers))))
         (outline-base-string
          (with-current-buffer orig-buf
            (outshine-transform-normalized-outline-regexp-base-to-string)))
         (rgxp-string
          (regexp-quote
           (outshine-chomp
            (format
             "%s" (car (rassoc 1 (with-current-buffer orig-buf
                                   outline-promotion-headings)))))))
         (rgxp (if (not (and level
                             (integer-or-marker-p level)
                             (>= level 1)
                             (<= level 8)))
                   (error "Level must be an integer between 1 and 8")
                 (if NO-PARENT-LEVELS
                     (regexp-quote
                      (format
                       "%s"
                       (car
                        (rassoc level
                                (with-current-buffer orig-buf
                                  outline-promotion-headings)))))
                   (concat
                    (dotimes (i (1- level) rgxp-string)
                      (setq rgxp-string
                            (concat rgxp-string
                                    (regexp-quote
                                     outline-base-string)
                                    "?")))
                    " ")))))
    (concat "^" rgxp)))

;;;;; Keyword Searches

(defun navi-get-language-alist (language &optional MAPPINGS)
  "Return the alist with keys and regexps for LANGUAGE from `navi-keywords'.
If MAPPINGS is non-nil, return the alist with key-mappings from
`navi-key-mappings' instead."
  (let ((custom-alist (if MAPPINGS navi-key-mappings navi-keywords)))
    (if (not (and (navi-non-empty-string-p language)
                  (assoc language custom-alist)))
        (message "Language not registered in customizable variable `%s'"
                 (symbol-name custom-alist))
      (cdr (assoc language custom-alist)))))

;;;;; Navi Buffer

(defun navi-set-regexp-quoted-line-at-point ()
  "Set `navi-regexp-quoted-line-at-point' to the value calculated by
`navi-regexp-quote-line-at-point'."
  (setq navi-regexp-quoted-line-at-point
        (navi-regexp-quote-line-at-point))
  (format "%s" navi-regexp-quoted-line-at-point))

(defun navi-regexp-quote-line-at-point ()
  "Store a quoted regexp for line at point.
Leading and trailing whitespace is deleted."
  ;; (setq navi-regexp-quoted-line-at-point
  (regexp-quote
   (outshine-chomp
    (substring-no-properties
     (buffer-string) (point-at-bol) (point-at-eol)))))
;; (format "%s" navi-regexp-quoted-line-at-point))

(defun navi-get-line-number-from-regexp-quoted-line-at-point (rgxp)
  "Return as Integer the line number in regexp-quoted-line-at-point."
  (string-to-number
   (car (split-string rgxp ":" 'OMIT-NULLS))))

(defun navi-in-buffer-headline-p ()
  "Return `line-number-at-position' if in first line, nil otherwise."
  (and (eq major-mode 'navi-mode)
       (if (eq (line-number-at-pos) 1) 1 nil)))

(defun navi-search-less-or-equal-line-number (&optional num)
  "Search closest result-line to given line-number.
This function searches a result-line in a navi-buffer with
line-number less-or-equal to line-number of
`navi-regexp-quoted-line-at-point' or NUM. Its not about
line-numbers in the navi-buffer, but about the line-numbers in
the original-buffer shown in the occur-search results."
  (let* ((line-num (or
                    (and num (integer-or-marker-p num) (>= num 1) num)
                    (navi-get-line-number-from-regexp-quoted-line-at-point
                     navi-regexp-quoted-line-at-point)))
         (line-num-str (int-to-string line-num))
         (match-point))
    (save-excursion
      (goto-char (point-min))
      (forward-line)
      (unless (< line-num
                 (navi-get-line-number-from-regexp-quoted-line-at-point
                  (navi-regexp-quote-line-at-point)))
        (forward-line -1)
        (while (and (>= line-num 1)
                    (not
                     (setq match-point
                           (re-search-forward
                            (concat "^[[:space:]]*"
                                    line-num-str
                                    ":")
                            nil 'NO-ERROR))))
          (goto-char (point-min))
          (setq line-num (1- line-num))
          (setq line-num-str (int-to-string line-num)))
        (if match-point
            (goto-char match-point)
          (forward-line)))
      (forward-line)
      (occur-prev)
      (point))))


;; modified `occur-rename-buffer' from `replace.el'
(defun navi-rename-buffer (&optional unique-p)
  "Rename the current *Occur* buffer to *Navi:original-buffer-name*.
Here `original-buffer-name' is the buffer name where Occur was
originally run. When given the prefix argument, the renaming will
not clobber the existing buffer(s) of that name, but use
`generate-new-buffer-name' instead. You can add this to
`occur-hook' if you always want a separate *Occur* buffer for
each buffer where you invoke `occur'."
  (let ((orig-buffer-name ""))
    (with-current-buffer
        (if (eq major-mode 'occur-mode) (current-buffer) (get-buffer "*Occur*"))
      (setq orig-buffer-name
            (mapconcat
             #'buffer-name
             (car (cddr occur-revert-arguments)) "/"))
      (rename-buffer (concat "*Navi:" orig-buffer-name "*") unique-p)
      ;; make marker for this navi-buffer
      ;; and store it in `navi''s plist
      (put 'navi
           (navi-make-buffer-key)
           (set
            (intern
             (navi-make-marker-name
              (cadr (split-string (buffer-name) "[*:]" 'OMIT-NULLS))))
            (point-marker))))))

;; (add-to-list 'occur-hook 'navi-rename-buffer)

(defun navi-clean-up ()
  "Clean up `navi' plist and left-over markers after killing navi-buffer."
  (setq navi-revert-arguments nil)	; FIXME
  (setq navi-regexp-quoted-line-at-point nil)
  (mapc
   (lambda (marker) (set-marker marker nil))
   (navi-get-twin-buffer-markers)))


;;;;; Twin Buffers

(defun navi-make-buffer-key (&optional buf)
  "Return the (current) buffer-name or string BUF as interned keyword-symbol"
  (let* ((split-str (split-string (or buf (buffer-name)) "[*]" 'OMIT-NULLS))
         (buf-name
          (if (> (length split-str) 1)
              (file-name-sans-extension
               (mapconcat 'identity split-str ""))
            (file-name-sans-extension (car split-str)))))
    (intern (concat ":" buf-name))))

(defun navi-make-marker-name (&optional buf)
  "Return marker-name by expansion of (current) buffer-name or string BUF."
  (let ((buf-name
         (file-name-sans-extension
          (car (split-string (or buf (buffer-name))
			     "[*]" 'OMIT-NULLS)))))
    (concat buf-name "-marker")))

(defun navi-get-twin-buffer-markers ()
  "Return list with two markers pointing to buffer-twins or nil.
CAR of the return-list is always the marker pointing to
 current-buffer, CADR the marker pointing to its twin-buffer."
  (let* ((curr-buf-split
          (split-string (buffer-name) "[*:]" 'OMIT-NULLS))
         (is-navi-buffer-p
          (string-equal (car curr-buf-split) "Navi"))
         (twin-of-navi
          (and is-navi-buffer-p
               (get 'navi (navi-make-buffer-key (cadr curr-buf-split)))))
         (self-navi
          (and is-navi-buffer-p
               (get 'navi (navi-make-buffer-key
                           (concat
                            (car curr-buf-split)
                            ":"
                            (cadr curr-buf-split))))))
         (twin-of-orig
          (unless is-navi-buffer-p
            (get 'navi (navi-make-buffer-key
                        (concat "Navi:" (car curr-buf-split))))))
         (self-orig
          (unless is-navi-buffer-p
            (get 'navi (navi-make-buffer-key (car curr-buf-split))))))
    (if is-navi-buffer-p
        (and self-navi twin-of-navi
             (list self-navi twin-of-navi))
      (and self-orig twin-of-orig
           (list self-orig twin-of-orig)))))

(defun navi-get-language-name ()
  "Return language name for major-mode of original-buffer."
  (with-current-buffer
      (marker-buffer
       (cadr (navi-get-twin-buffer-markers)))
    (car
     (split-string
      (symbol-name major-mode)
      "-mode" 'OMIT-NULLS))))

;;;;; Special Case Org-mode

;; special treatment for Org-mode buffers
(defun navi-make-org-mode-promotion-headings-list ()
  "Make a sorted list of headings used for promotion/demotion commands.
Set this to a list of MAX-LEVEL headings as they are matched by
`outline-regexp', top-level heading first."
  (setq outline-promotion-headings
        '(("* " . 1)
          ("** " . 2)
          ("*** " . 3)
          ("**** " . 4)
          ("***** " . 5)
          ("****** " . 6)
          ("******* " . 7)
          ("******** " . 8)))
  (make-variable-buffer-local 'outline-promotion-headings))
(org-add-hook 'org-mode-hook 'navi-make-org-mode-promotion-headings-list)

;; special treatment for Org-mode buffers
(defun navi-calc-org-mode-headline-regexp
  (level &optional org-promo-headers NO-PARENT-LEVELS)
  "Calculate regexp to show headers of original Org-mode buffer.
Regexp should result in an occur-search showing up to
outline-level LEVEL headlines in navi-buffer. If NO-PARENT-LEVELS
in non-nil, only headers of level LEVEL are shown."
  (if (not (and level
                (integer-or-marker-p level)
                (>= level 1)
                (<= level 8)))
      (error "Level must be an integer between 1 and 8")
    (let ((headline-string
           (car
            (rassoc
             level
             (or org-promo-headers
                 outline-promotion-headings)))))
      (concat
       "^"
       (if NO-PARENT-LEVELS
           (regexp-quote headline-string)
         (replace-regexp-in-string
          "\\*" "\\\\*"
          (replace-regexp-in-string
           "\\(\\*\\?\\).*\\'" "*"
           (mapconcat 'identity (split-string headline-string "" t) "?")
           nil nil 1)))))))

;; (add-to-list 'occur-hook 'navi-rename-buffer)

;;;;; Use Outorg

(defun navi-use-outorg (fun-no-prefix)
  "Call prefixed FUN-NO-PREFIX from navi-mode.
If the associated original (twin-) buffer is an Org-mode buffer,
call the relevant Org command directly, i.e. add `org-' prefix to
FUN-NO-PREFIX, otherwise add `outshine-' prefix and thus call the
'outshine-use-outorg' function."
  (let ((fun (intern
	      (format "%s%s"
		      (with-current-buffer
			  (marker-buffer
			   (cadr (navi-get-twin-buffer-markers)))
		      (if (eq major-mode 'org-mode)
			  "org-"
			"outshine-"))
		      fun-no-prefix))))
    (navi-goto-occurrence-other-window)
    (call-interactively fun)
    (navi-switch-to-twin-buffer)))

;;;; Commands

;;;;; Navi Edit Mode

(defun navi-cease-edit ()
  "Switch from Navi Edit mode to Navi mode."
  (interactive)
  (when (derived-mode-p 'navi-edit-mode)
    (navi-mode)
    (message "Switching to Navi mode.")))


;;;;; Twin Buffers

(defun navi-goto-occurrence-other-window ()
  "Moves navi-buffer marker to point before switching buffers."
  (interactive)
  (move-marker
   (car (navi-get-twin-buffer-markers)) (point))
  (navi-set-regexp-quoted-line-at-point)
  (occur-mode-goto-occurrence-other-window))

(defun navi-search-and-switch ()
  "Call `occur' and immediatley switch to `*Navi:original-buffer-name*' buffer"
  (interactive)
  (let ((buf-markers (navi-get-twin-buffer-markers))
        (orig-buffer-mode major-mode))
    ;; (with-current-buffer (marker-buffer (car buf-markers)) major-mode)))
    (if (and
         buf-markers
         (buffer-live-p (marker-buffer (car buf-markers)))
         (buffer-live-p (marker-buffer (cadr buf-markers))))
        (navi-switch-to-twin-buffer)
      (let* ((1st-level-headers
              (if (eq orig-buffer-mode 'org-mode)
                  (navi-calc-org-mode-headline-regexp 1)
                (if outshine-enforce-no-comment-padding-p
                    "^;;; "
                  (regexp-quote
                   (car (rassoc 1 outline-promotion-headings)))))))
        ;; (regexp-quote
        ;;  (outshine-calc-outline-string-at-level 1))))
        (put 'navi (navi-make-buffer-key (buffer-name))
             (set (intern (navi-make-marker-name)) (point-marker)))
        (occur 1st-level-headers)
        (navi-rename-buffer)
        (navi-switch-to-twin-buffer)
        (navi-mode)
        (occur-next)
        (move-marker
         (car (navi-get-twin-buffer-markers)) (point))
        (navi-set-regexp-quoted-line-at-point)))
    (make-variable-buffer-local 'kill-buffer-hook)
    (add-to-list 'kill-buffer-hook 'navi-clean-up)))

(defun navi-quit-and-switch ()
  "Quit navi-buffer and immediatley switch back to original-buffer"
  (interactive)
  (navi-goto-occurrence-other-window)
  (kill-buffer (marker-buffer (cadr (navi-get-twin-buffer-markers))))
  (navi-clean-up))

(defun navi-switch-to-twin-buffer ()
  "Switch to associated twin-buffer of current buffer or do nothing."
  (interactive)
  (let* ((marker-list (navi-get-twin-buffer-markers))
         (self-marker (car marker-list))
         (twin-marker (cadr marker-list)))
    (and marker-list
         (buffer-live-p (marker-buffer self-marker))
         (buffer-live-p (marker-buffer twin-marker))
         (move-marker self-marker (point) (marker-buffer self-marker))
         (if (eq major-mode 'navi-mode)
             (navi-set-regexp-quoted-line-at-point) t)
         (switch-to-buffer-other-window (marker-buffer twin-marker))
         (goto-char (marker-position twin-marker))
         (and (eq major-mode 'navi-mode)
              (navi-revert-function)))))

;;;;; Navi Buffer

;; adapted from 'replace.el'
(defun navi-revert-function (&optional regexp)
  "Handle `revert-buffer' for navi-buffers."
  (interactive)
  (let ((navi-revert-arguments
         (if regexp
             (append
              (list regexp) (cdr occur-revert-arguments))
           occur-revert-arguments)))
    (navi-set-regexp-quoted-line-at-point)
    (apply 'navi-1 (append navi-revert-arguments (list (buffer-name))))
    ;; FIXME redundant with navi-1 instead of occur-1?
    (unless
        (eq major-mode 'navi-mode) (navi-mode))
    (goto-char
     (navi-search-less-or-equal-line-number))))

;;;;; Navi Generic Command

;; this command executes all user-defined occur-searches
(defun navi-generic-command (key prefix)
  "One size fits all (user-defined header and keyword searches)."
  (interactive (list last-command-event current-prefix-arg))
  (let ((keystrg (format "%c" key))
        (numval-prefix (and prefix (prefix-numeric-value prefix))))
    (if prefix
        (cond
         ((memq numval-prefix (number-sequence 1 8))
          (navi-show-headers-and-keywords numval-prefix keystrg))
         ((and
           (not (memq numval-prefix (number-sequence 1 8)))
	   (not (memq key (number-sequence 49 56))))
          (navi-show-headers keystrg prefix))
         (t nil))
      (cond
       ((memq key (number-sequence 49 56))
        (navi-show-headers (string-to-number (format "%c" key))))
       ((memq key (number-sequence 57 126))
        (navi-show-keywords keystrg))
       (t nil)))))

;;;;; Act on thing-at-point

;; (defun navi-mark-subtree-and-switch()
;;   "Mark subtree at point in original-buffer."
;;   (interactive)
;;   (navi-goto-occurrence-other-window)
;;   (if (outline-on-heading-p)
;;       (outline-mark-subtree)
;;       (message "Only subtrees may be marked via navi-mode")))

;; ;; FIXME deactivates region - workaround?
;; ;; (navi-switch-to-twin-buffer))

(defun navi-mark-thing-at-point-and-switch ()
  "Mark thing at point in original-buffer."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-mark-subtree)
    (mark-sexp)))

;; (defun navi-copy-subtree-to-register-s ()
;;   "Copy subtree at point in original-buffer."
;;   (interactive)
;;   (navi-goto-occurrence-other-window)
;;   (if (outline-on-heading-p)
;;       (progn
;;         (outline-mark-subtree)
;;         (and
;;          (use-region-p)
;;          (copy-to-register ?s (region-beginning) (region-end)))
;;         (deactivate-mark))
;;     (message "Only subtrees may be copied via navi-mode"))
;;   (navi-switch-to-twin-buffer))

(defun navi-act-on-thing-at-point (&optional arg)
  "Call a function with function arguments on thing-at-point.

Makes sense only for functions that don't need an active region
\(ARG is nil\) or that take start and end region markers as first
arguments \(ARG is non-nil\). In both cases, a list of
more \(optional\) function arguments can be given \(see
`navi-act-on-thing'\)."
  (interactive "P")
  (navi-goto-occurrence-other-window)
  (if arg
      (progn
	(deactivate-mark)
	(call-interactively 'navi-act-on-thing))
    (if (outline-on-heading-p)
	(outline-mark-subtree)
      (mark-sexp))
    (if (not (use-region-p))
	(error "No active region")
      (call-interactively 'navi-act-on-thing)
      (deactivate-mark)))
  (navi-switch-to-twin-buffer))

(defun navi-act-on-thing (fun &optional funargs start end)
  "Call FUN with FUNARGS on thing or region \(from START to END\)."
  (interactive "aFunction: \nxArgument List (arg1 ... argN): \nr")
  (if (and start end (use-region-p))
      (if funargs
	  (funcall fun start end funargs)
	(funcall fun start end))	
    (if funargs
	(funcall fun funargs)
      (funcall fun))))
  

(defun navi-copy-thing-at-point-to-register-s ()
  "Copy thing at point in original-buffer."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-mark-subtree)
    (mark-sexp))
  (and
   (use-region-p)
   (progn
     (copy-to-register ?s (region-beginning) (region-end))
     (deactivate-mark)))
  (navi-switch-to-twin-buffer))

;; (defun navi-narrow-to-subtree ()
;;   "Narrow original buffer to subtree at point."
;;   (interactive)
;;   (navi-goto-occurrence-other-window)
;;   (if (outline-on-heading-p)
;;       (progn
;;         (outline-mark-subtree)
;;         (and
;;          (use-region-p)
;;          (narrow-to-region (region-beginning) (region-end)))
;;         (deactivate-mark))
;;     (message "Navi-mode can only narrow to subtrees"))
;;   (setq navi-regexp-quoted-line-before-narrowing
;;         navi-regexp-quoted-line-at-point)
;;   (navi-switch-to-twin-buffer))

(defun navi-narrow-to-thing-at-point ()
  "Narrow original buffer to thing at point."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-mark-subtree)
    (mark-sexp))
  (and
   (use-region-p)
   (progn
     (narrow-to-region (region-beginning) (region-end))
     (deactivate-mark)))
  (setq navi-regexp-quoted-line-before-narrowing
        navi-regexp-quoted-line-at-point)
  (navi-switch-to-twin-buffer))

(defun navi-widen ()
  "Widen original buffer."
  (interactive)
  (navi-goto-occurrence-other-window)
  (widen)
  (navi-switch-to-twin-buffer)
  (setq navi-regexp-quoted-line-at-point
        navi-regexp-quoted-line-before-narrowing)
  (goto-char
   (navi-search-less-or-equal-line-number)))

(defun navi-kill-thing-at-point ()
  "Kill thing at point in original-buffer."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-mark-subtree)
    (mark-sexp))
  (and
   (use-region-p)
   (and (y-or-n-p
         "Really kill the marked region in the original-buffer ")
        (copy-to-register
         ?s (region-beginning) (region-end) 'DELETE-FLAG)))
  (deactivate-mark)
  (navi-switch-to-twin-buffer))

;; (defun navi-yank-subtree-from-register-s ()
;;   "Yank in original-buffer."
;;   (interactive)
;;   (navi-goto-occurrence-other-window)
;;   (if (and
;;        (outline-on-heading-p)
;;        (get-register ?s))
;;       (progn
;;         (newline)
;;         (forward-line -1)
;;         (insert-register ?s))
;;     (message "Not on subtree-heading or no subtree to yank."))
;;   (navi-switch-to-twin-buffer))

(defun navi-yank-thing-from-register-s ()
  "Yank in original-buffer."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (and
       (or
        (outline-on-heading-p)
        (progn
          (end-of-sexp)
          (beginning-of-sexp)
          (sexp-at-point)))
       (get-register ?s))
      (progn
        (newline)
        (forward-line -1)
        (insert-register ?s))
    (message "Not on subtree/sexp or nothing to yank."))
  (navi-switch-to-twin-buffer))

;; (defun navi-query-replace ()
;;   "Call `query-replace' interactively on subtree at point."
;;   (interactive)
;;   (navi-goto-occurrence-other-window)
;;   (if (outline-on-heading-p)
;;       (progn
;;         (outline-mark-subtree)
;;         (and
;;          (use-region-p)
;;          (call-interactively 'query-replace))
;;         (deactivate-mark))
;;     (message "Navi-mode can perform query-replace only on subtrees"))
;;   (navi-switch-to-twin-buffer))

;;;;; Search and Replace

(defun navi-query-replace ()
  "Call `query-replace' interactively on thing at point."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-mark-subtree)
    (mark-sexp))
  (and
   (use-region-p)
   (progn
     (call-interactively 'query-replace)
     (deactivate-mark)))
  (navi-switch-to-twin-buffer))

;; (defun navi-isearch ()
;;   "Call `isearch' interactively on subtree at point."
;;   (interactive)
;;   (navi-goto-occurrence-other-window)
;;   (if (outline-on-heading-p)
;;       (save-restriction
;;         (outline-mark-subtree)
;;         (and
;;          (use-region-p)
;;          (narrow-to-region (region-beginning) (region-end)))
;;         (deactivate-mark)
;;         (isearch-mode t nil nil t nil))
;;     (message "Navi-mode can perform isearches only on subtrees"))
;;   (navi-switch-to-twin-buffer))


(defun navi-isearch ()
  "Call `isearch' interactively on thing at point."
  (interactive)
  (navi-goto-occurrence-other-window)
  (save-restriction
    (if (outline-on-heading-p)
        (outline-mark-subtree)
      (mark-sexp))
    (and
     (use-region-p)
     (progn
       (narrow-to-region (region-beginning) (region-end))
       (deactivate-mark)))
    (isearch-mode t nil nil t nil))
  (navi-switch-to-twin-buffer))

(defun navi-demote-subtree ()
  "Demote subtree at point."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-demote 1)
    (message "Navi-mode can only demote subtrees"))
  (navi-switch-to-twin-buffer))

(defun navi-promote-subtree ()
  "Promote subtree at point."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-promote 1)
    (message "Navi-mode can only promote subtrees"))
  (navi-switch-to-twin-buffer))

(defun navi-move-up-subtree ()
  "Move subtree at point one position up."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-move-subtree-up 1)
    (message "Navi-mode can only move subtrees"))
  (navi-switch-to-twin-buffer))

(defun navi-move-down-subtree ()
  "Move subtree at point one position down."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-move-subtree-down 1)
    (message "Navi-mode can only move subtrees"))
  (navi-switch-to-twin-buffer))

;;;;; Visibility Cycling

(defun navi-cycle-subtree ()
  "Cycle the visibility state of subtree at point in the original-buffer."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outline-cycle 1)
    (message "Not on subtree - can't cycle subtree visibility state."))
  (navi-switch-to-twin-buffer))

(defun navi-cycle-buffer ()
  "Cycle the visibility state of the original-buffer."
  (interactive)
  (navi-goto-occurrence-other-window)
  (outline-cycle '(4))
  (navi-switch-to-twin-buffer))

;;;;; Undo

(defun navi-undo ()
  "Undo last (undoable) action in original-buffer."
  (interactive)
  (navi-goto-occurrence-other-window)
  (undo)
  (navi-switch-to-twin-buffer))

;;;;; Show Help

(defun navi-show-help ()
  "Show navi-keybindings for major-mode of original-buffer."
  (interactive)
  (let ((mappings
         (navi-get-language-alist (navi-get-language-name) 'MAPPINGS))
        (navi-buf-marker (car (navi-get-twin-buffer-markers))))
    (switch-to-buffer-other-window
     (get-buffer-create
      (concat "*Navi:" (navi-get-language-name) ":HELP")))
    (save-restriction
      (widen)
      (when (string-equal
             (buffer-substring-no-properties (point-min) (point-max)) "")
        (insert "[KEY] : [SEARCH]\n")
        (forward-line -1)
        (navi-underline-line-with ?=)
        (forward-line 2)
        (mapc
         (lambda (association)
           (insert
            (format "\s\s\s\s\s\s\s\s\s\s\s\s\s\s\s\s\t%s : %s\n"
                    (cdr association)
                    (car
                     (split-string
                      (symbol-name (car association))
                      ":" 'OMIT-NULLS)))))
         mappings))
      (goto-char (point-min))
      (view-buffer (current-buffer)))))

;;;;; Use Outorg

(defun navi-edit-as-org (&optional args)
  "Edit subtree at point with `outorg'.

Edit whole buffer if ARGS are given. Editing takes place in a
separate temporary Org-mode edit-buffer."
  (interactive "P")
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (if args
	  (outorg-edit-as-org args)
	(outorg-edit-as-org))
    (message "Only subtrees (or the whole buffer) may be edited via navi-mode"))
  (navi-switch-to-twin-buffer))

;; TODO improve orderly exit from `message' buffer via `outorg' buffer and
;; `original-buffer' to `navi-buffer', best without showing `outorg'
;; and `original' buffer to the user (not critical).
(defun navi-mail-subtree ()
  "Send subtree at point as email."
  (interactive)
  (navi-goto-occurrence-other-window)
  (if (outline-on-heading-p)
      (outorg-edit-as-org)
    (message "Only subtrees be send as email via navi-mode"))
  (with-current-buffer
      (get-buffer "*outorg-edit-buffer*")
    (org-mark-subtree)
    (if (require 'org-mime nil t)
      (org-mime-subtree)
      (user-error "%s" "Library `org-mime-subtree' not found"))))

;;;;; Call outshine-use-outorg functions

(defun navi-deadline ()
  "Call `outshine-deadline' from navi-mode."
  (interactive)
  (navi-use-outorg 'deadline))

(defun navi-export-dispatch ()
  "Call `outshine-export-dispatch' from navi-mode."
  (interactive)
  (navi-use-outorg 'export-dispatch))

(defun navi-insert-link ()
"Call `outshine-insert-link' from navi-mode."
(interactive)
(navi-use-outorg 'insert-link))

(defun navi-open-at-point ()
  "Call `outshine-open-at-point' from navi-mode."
  (interactive)
  (navi-use-outorg 'open-at-point))

(defun navi-set-tags-command ()
  "Call `outshine-set-tags-command' from navi-mode."
  (interactive)
  (navi-use-outorg 'set-tags-command))

(defun navi-schedule ()
  "Call `outshine-schedule' from navi-mode."
  (interactive)
  (navi-use-outorg 'schedule))
  
(defun navi-todo ()
  "Call `outshine-todo' from navi-mode."
  (interactive)
  (navi-use-outorg 'todo))

(defun navi-time-stamp-inactive ()
  "Call `outshine-time-stamp-inactive' from navi-mode."
  (interactive)
  (navi-use-outorg 'time-stamp-inactive))

(defun navi-priority ()
  "Call `outshine-priority' from navi-mode."
  (interactive)
  (navi-use-outorg 'priority))

(defun navi-time-stamp ()
  "Call `outshine-time-stamp' from navi-mode."
  (interactive)
  (navi-use-outorg 'time-stamp))

(defun navi-toggle-fixed-width ()
  "Call `outshine-toggle-fixed-width' from navi-mode."
  (interactive)
  (navi-use-outorg 'toggle-fixed-width))

(defun navi-toggle-comment ()
  "Call `outshine-toggle-comment' from navi-mode."
  (interactive)
  (navi-use-outorg 'toggle-comment))

(defun navi-sort-entries ()
  "Call `outshine-sort-entries' from navi-mode."
  (interactive)
  (navi-use-outorg 'sort-entries))

(defun navi-previous-block ()
  "Call `outshine-previous-block' from navi-mode."
  (interactive)
  (navi-use-outorg 'previous-block))

(defun navi-next-block ()
  "Call `outshine-next-block' from navi-mode."
  (interactive)
  (navi-use-outorg 'next-block))

(defun navi-insert-last-stored-link ()
  "Call `outshine-insert-last-stored-link' from navi-mode."
  (interactive)
  (navi-use-outorg 'insert-last-stored-link))

(defun navi-toggle-checkbox ()
  "Call `outshine-toggle-checkbox' from navi-mode."
  (interactive)
  (navi-use-outorg 'toggle-checkbox))

(defun navi-clock-in ()
  "Call `outshine-clock-in' from navi-mode."
  (interactive)
  (navi-use-outorg 'clock-in))

(defun navi-clock-goto ()
  "Call `outshine-clock-goto' from navi-mode."
  (interactive)
  (navi-use-outorg 'clock-goto))

(defun navi-next-link ()
  "Call `outshine-next-link' from navi-mode."
  (interactive)
  (navi-use-outorg 'next-link))

(defun navi-clock-out ()
  "Call `outshine-clock-out' from navi-mode."
  (interactive)
  (navi-use-outorg 'clock-out))

(defun navi-previous-link ()
  "Call `outshine-previous-link' from navi-mode."
  (interactive)
  (navi-use-outorg 'previous-link))

(defun navi-clock-cancel ()
  "Call `outshine-clock-cancel' from navi-mode."
  (interactive)
  (navi-use-outorg 'clock-cancel))

(defun navi-clock-report ()
  "Call `outshine-clock-report' from navi-mode."
  (interactive)
  (navi-use-outorg 'clock-report))

(defun navi-timer-pause-or-continue ()
  "Call `outshine-timer-pause-or-continue' from navi-mode."
  (interactive)
  (navi-use-outorg 'timer-pause-or-continue))

(defun navi-timer-item ()
  "Call `outshine-timer-item' from navi-mode."
  (interactive)
  (navi-use-outorg 'timer-item))

(defun navi-timer ()
  "Call `outshine-timer' from navi-mode."
  (interactive)
  (navi-use-outorg 'timer))

(defun navi-timer-start ()
  "Call `outshine-timer-start' from navi-mode."
  (interactive)
  (navi-use-outorg 'timer-start))

(defun navi-timer-cancel-timer ()
  "Call `outshine-timer-cancel-timer' from navi-mode."
  (interactive)
  (navi-use-outorg 'timer-cancel-timer))

(defun navi-timer-set-timer ()
  "Call `outshine-timer-set-timer' from navi-mode."
  (interactive)
  (navi-use-outorg 'timer-set-timer))

(defun navi-agenda-set-restriction-lock ()
  "Call `outshine-agenda-set-restriction-lock' from navi-mode."
  (interactive)
  (navi-use-outorg 'agenda-set-restriction-lock))

(defun navi-agenda-remove-restriction-lock ()
  "Call `outshine-agenda-remove-restriction-lock' from navi-mode."
  (interactive)
  (navi-use-outorg 'agenda-remove-restriction-lock))

(defun navi-inc-effort ()
  "Call `outshine-inc-effort' from navi-mode."
  (interactive)
  (navi-use-outorg 'inc-effort))

(defun navi-set-property-and-value ()
  "Call `outshine-set-property-and-value' from navi-mode."
  (interactive)
  (navi-use-outorg 'set-property-and-value))

(defun navi-toggle-archive-tag ()
  "Call `outshine-toggle-archive-tag' from navi-mode."
  (interactive)
  (navi-use-outorg 'toggle-archive-tag))

(defun navi-insert-drawer ()
  "Call `outshine-insert-drawer' from navi-mode."
  (interactive)
  (navi-use-outorg 'insert-drawer))

(defun navi-set-effort ()
  "Call `outshine-set-effort' from navi-mode."
  (interactive)
  (navi-use-outorg 'set-effort))

(defun navi-footnote-action ()
  "Call `outshine-footnote-action' from navi-mode."
  (interactive)
  (navi-use-outorg 'footnote-action))

(defun navi-set-property ()
  "Call `outshine-set-property' from navi-mode."
  (interactive)
  (navi-use-outorg 'set-property))

;;; Menus and Keys
;;;; Menus

;; menu map for navi-mode
(defvar navi-menu-map
  (let ((map (make-sparse-keymap)))
    (define-key map [next-error-follow-minor-mode]
      `(menu-item ,(purecopy "Auto Occurrence Display")
                  next-error-follow-minor-mode
                  :help ,(purecopy
                          "Display another occurrence when moving the cursor")
                  :button (:toggle . (and (boundp 'next-error-follow-minor-mode)
                                          next-error-follow-minor-mode))))

    (define-key map [separator-11] menu-bar-separator)
    (define-key map [navi-quit-and-switch]
      `(menu-item ,(purecopy "Quit")
                  navi-quit-and-switch :help ,(purecopy "Quit navi-buffer and switch to
    original-buffer")))

    (define-key map [separator-10] menu-bar-separator)
    (define-key map [kill-this-buffer]
      `(menu-item ,(purecopy "Kill Navi Buffer") kill-this-buffer
                  :help ,(purecopy "Kill the current *Navi* buffer")))
    (define-key map [clone-buffer]
      `(menu-item ,(purecopy "Clone Navi Buffer") clone-buffer
                  :help ,(purecopy "Create and return a twin copy
                  of the current *Navi* buffer")))

    (define-key map [separator-9] menu-bar-separator)
    (define-key map [navi-show-help]
      `(menu-item ,(purecopy "Show Help")
                  navi-show-help :help ,(purecopy "Show help for keyword queries. Use
      \\[describe-mode] to see all navi-mode keybindings.")))
    (define-key map [navi-revert-function]
      `(menu-item ,(purecopy "Revert Navi Buffer")
                  navi-revert-function :help ,(purecopy "Revert
      navi-buffer (seldom necessary)")))
    (define-key map [navi-undo]
      `(menu-item ,(purecopy "Undo Last Change")
                  navi-undo :help ,(purecopy "Undo last change in original-buffer")))

    (define-key map [separator-8] menu-bar-separator)
    (define-key map [navi-edit-mode]
      `(menu-item ,(purecopy "Make Navi-Buffer Editable")
                  navi-edit-mode :help ,(purecopy "Make navi-buffer editable and apply
     changes to original-buffer")))
    (define-key map [navi-edit-as-org]
      `(menu-item ,(purecopy "Edit Subtree in Org-mode")
                  navi-edit-as-org :help ,(purecopy "Edit Subtree at point in temporary
     Org-mode edit buffer")))

    (define-key map [separator-7] menu-bar-separator)
    (define-key map [navi-query-replace]
      `(menu-item ,(purecopy "Query-Replace in thing-at-point")
                  navi-query-replace :help ,(purecopy "Do a query-replace in
      thing at point")))
    (define-key map [navi-isearch]
      `(menu-item ,(purecopy "iSearch in thing-at-point")
                  navi-isearch :help ,(purecopy "Do an isearch in thing at point")))

    (define-key map [separator-6] menu-bar-separator)
    (define-key map [navi-widen]
      `(menu-item ,(purecopy "Widen Original Buffer")
                  navi-widen  :help ,(purecopy "Widen original-buffer")))
    (define-key map [navi-narrow-to-thing-at-point]
      `(menu-item ,(purecopy "Narrow to thing-at-point")
                  navi-narrow-to-thing-at-point
                  :help ,(purecopy "Narrow original-buffer to
                  thing at point")))

    (define-key map [separator-5] menu-bar-separator)
    (define-key map [navi-mail-subtree]
      `(menu-item ,(purecopy "Mail Subtree")
                  navi-mail-subtree
                  :help ,(purecopy "Mail subtree at point")))
    (define-key map [navi-yank-thing-from-register-s]
      `(menu-item ,(purecopy "Yank killed/copied thing")
                  navi-yank-thing-from-register-s
                  :help ,(purecopy "Yank (killed/copied) thing
                  from register s")))
    (define-key map [navi-kill-thing-at-point]
      `(menu-item ,(purecopy "Kill thing-at-point")
                  navi-kill-thing-at-point
                  :help ,(purecopy "Kill thing at point (y-or-n-p)")))
    (define-key map [navi-copy-thing-at-point-to-register-s]
      `(menu-item ,(purecopy "Copy thing-at-point")
                  navi-copy-thing-at-point-to-register-s
                  :help ,(purecopy "Copy thing at point to register s")))
    (define-key map [navi-act-on-thing-at-point]
      `(menu-item ,(purecopy "Act on thing-at-point")
                  navi-act-on-thing-at-point
                  :help ,(purecopy "Act on thing at point")))
    (define-key map [navi-mark-thing-at-point-and-switch]
      `(menu-item ,(purecopy "Mark thing-at-point")
                  navi-mark-thing-at-point-and-switch
                  :help ,(purecopy "Mark thing at point and switch to
     original buffer")))

    (define-key map [separator-4] menu-bar-separator)
    (define-key map [navi-move-up-subtree]
      `(menu-item ,(purecopy "Move Up Subtree")
                  navi-move-up-subtree
                  :help ,(purecopy "Move subtree at point up 1 position")))
    (define-key map [navi-move-down-subtree]
      `(menu-item ,(purecopy "Move Down Subtree")
                  navi-move-down-subtree
                  :help ,(purecopy "Move subtree at point down 1 position")))
    (define-key map [navi-demote-subtree]
      `(menu-item ,(purecopy "Demote Subtree")
                  navi-demote-subtree
                  :help ,(purecopy "Demote subtree at point")))
    (define-key map [navi-promote-subtree]
      `(menu-item ,(purecopy "Promote Subtree")
                  navi-promote-subtree
                  :help ,(purecopy "Promote subtree at point")))
    (define-key map [navi-cycle-buffer]
      `(menu-item ,(purecopy "Cycle Buffer")
                  navi-cycle-buffer
                  :help ,(purecopy "Cycle visibility of original buffer")))
    (define-key map [navi-cycle-subtree]
      `(menu-item ,(purecopy "Cycle Subtree")
                  navi-cycle-subtree
                  :help ,(purecopy "Cycle visibility of subtree at point")))


    (define-key map [separator-3] menu-bar-separator)
    (define-key map [navi-switch-to-twin-buffer]
      `(menu-item ,(purecopy "Switch to Twin Buffer")
                  navi-switch-to-twin-buffer
                  :help ,(purecopy "Go to the associated twin buffer")))
    (define-key map [navi-goto-occurrence-other-window]
      `(menu-item ,(purecopy "Go To Occurrence Other Window")
                  navi-goto-occurrence-other-window
                  :help ,(purecopy "Go to the occurrence the
                  current line describes, in another window")))
    (define-key map [occur-mode-display-occurrence]
      `(menu-item ,(purecopy "Display Occurrence")
                  occur-mode-display-occurrence
                  :help ,(purecopy "Display in another window the
                  occurrence the current line describes")))

    (define-key map [separator-2] menu-bar-separator)
    (define-key map [scroll-up-command]
      `(menu-item ,(purecopy "Move Page up") scroll-up-command
                  :help ,(purecopy "Move 1 page up in buffer")))
    (define-key map [scroll-down-command]
      `(menu-item ,(purecopy "Move Page down") scroll-down-command
                  :help ,(purecopy "Move 1 page down in buffer")))
    (define-key map [occur-next]
      `(menu-item ,(purecopy "Move to Next Match") occur-next
                  :help ,(purecopy "Move to the Nth (default 1)
                  next match in a Navi-mode buffer")))
    (define-key map [occur-prev]
      `(menu-item ,(purecopy "Move to Previous Match") occur-prev
                  :help ,(purecopy "Move to the Nth (default 1)
    previous match in a Navi-mode buffer"))) map)
  "Menu keymap for `navi-mode'.")


;; menu map for navi-edit-mode
(defvar navi-edit-menu-map
  (let ((map (make-sparse-keymap)))
    (define-key map [next-error-follow-minor-mode]
      `(menu-item ,(purecopy "Auto Occurrence Display")
                  next-error-follow-minor-mode
                  :help ,(purecopy
                          "Display another occurrence when moving the cursor")
                  :button (:toggle . (and (boundp 'next-error-follow-minor-mode)
                                          next-error-follow-minor-mode))))

    (define-key map [separator-4] menu-bar-separator)
    (define-key map [navi-cease-edit]
      `(menu-item ,(purecopy "Cease Edit")
                  navi-cease-edit :help ,(purecopy "Cease editing in navi-edit-mode and
    return to (read-only) navi-mode")))

    (define-key map [separator-3] menu-bar-separator)
    (define-key map [occur-mode-display-occurrence]
      `(menu-item ,(purecopy "Display Occurrence")
                  occur-mode-display-occurrence
                  :help ,(purecopy "Display in another window the
                  occurrence the current line describes")))

    (define-key map [separator-2] menu-bar-separator)
    (define-key map [scroll-up-command]
      `(menu-item ,(purecopy "Move Page up") scroll-up-command
                  :help ,(purecopy "Move 1 page up in buffer")))
    (define-key map [scroll-down-command]
      `(menu-item ,(purecopy "Move Page down") scroll-down-command
                  :help ,(purecopy "Move 1 page down in buffer")))
    (define-key map [scroll-other-window-up]
      `(menu-item ,(purecopy "Move Page up (other window)")
                  scroll-other-window-up
                  :help
                  ,(purecopy "Move 1 page up in other window")))
    (define-key map [scroll-other-window]
      `(menu-item ,(purecopy "Move Page down (other window)")
                  scroll-other-window
                  :help
                  ,(purecopy "Move 1 page down in other window")))
    (define-key map [occur-next]
      `(menu-item ,(purecopy "Move to Next Match") occur-next
                  :help ,(purecopy "Move to the Nth (default 1)
                  next match in a Navi-mode buffer")))
    (define-key map [occur-prev]
      `(menu-item ,(purecopy "Move to Previous Match") occur-prev
                  :help ,(purecopy "Move to the Nth (default 1)
    previous match in a Navi-mode buffer"))) map)
  "Menu keymap for `navi-edit-mode'.")


;;;; Keys

;; key-bindings for user-defined occur-searches
;; see `navi-key-mappings' and `navi-keywords'.
;; reserved keys to be removed from num-seq:
;; | ?\s |  32 |
;; | ?\+ |  43 |
;; | ?\- |  45 |
;; | ?\^ |  60 |
;; | ?E  |  69 |
;; | ?\< |  94 |
;; | ?c  |  99 |
;; | ?d  | 100 |
;; | ?e  | 101 |
;; | ?g  | 103 |
;; | ?h  | 104 |
;; | ?k  | 107 |
;; | ?l  | 108 |
;; | ?m  | 109 |
;; | ?n  | 110 |
;; | ?o  | 111 |
;; | ?p  | 112 |
;; | ?q  | 113 |
;; | ?r  | 114 |
;; | ?s  | 115 |
;; | ?u  | 117 |
;; | ?w  | 119 |
;; | ?y  | 121 |
;; | ?z  | 122 |
;; | ?\d | 127 |
(mapc #'(lambda (key)
          (define-key navi-mode-map (format "%c" key)
            'navi-generic-command))
      ;; all ascii printing chars
      (let ((num-seq (number-sequence 32 127)))
        (mapc #'(lambda (num)
                  (setq num-seq (delq num num-seq)))
              ;; reserved keys defined elsewhere
              '(32 43 45 60 69 94 99 100 101 103 104 107 108 109
                   110 111 112 113 114 115 117 119 121 122 127)) num-seq))

;; global keys for (original) twin-buffer of navi-buffer
(global-set-key (kbd "M-s n") 'navi-search-and-switch)
(global-set-key (kbd "M-s s") 'navi-switch-to-twin-buffer)
(global-set-key (kbd "M-s M-s") 'navi-switch-to-twin-buffer)
;; keys for navi-mode
(define-key navi-mode-map (kbd "s") 'navi-switch-to-twin-buffer)
(define-key navi-mode-map (kbd "d") 'occur-mode-display-occurrence)
(define-key navi-mode-map (kbd "o") 'navi-goto-occurrence-other-window)
(define-key navi-mode-map (kbd "n") 'occur-next)
(define-key navi-mode-map (kbd "p") 'occur-prev)
(define-key navi-mode-map (kbd "SPC") 'scroll-up-command)
(define-key navi-mode-map (kbd "DEL") 'scroll-down-command)
(define-key navi-mode-map (kbd "TAB") 'navi-cycle-subtree)
(define-key navi-mode-map (kbd "M-TAB") 'navi-cycle-buffer)
;; (define-key navi-mode-map (kbd "<backtab>") 'navi-cycle-buffer)
(define-key navi-mode-map (kbd "m")
  'navi-mark-thing-at-point-and-switch)
(define-key navi-mode-map (kbd "c")
  'navi-copy-thing-at-point-to-register-s)
(define-key navi-mode-map (kbd ",")
  'navi-act-on-thing-at-point)
(define-key navi-mode-map (kbd "z") 'navi-mail-subtree)
(define-key navi-mode-map (kbd "r") 'navi-narrow-to-thing-at-point)
(define-key navi-mode-map (kbd "w") 'navi-widen)
(define-key navi-mode-map (kbd "l") 'navi-query-replace)
(define-key navi-mode-map (kbd "i") 'navi-isearch)
(define-key navi-mode-map (kbd "k") 'navi-kill-thing-at-point)
(define-key navi-mode-map (kbd "y") 'navi-yank-thing-from-register-s)
(define-key navi-mode-map (kbd "u") 'navi-undo)
(define-key navi-mode-map (kbd "e") 'navi-edit-as-org)
(define-key navi-mode-map (kbd "E") 'navi-edit-mode)
(define-key navi-mode-map (kbd "h") 'navi-show-help)
(define-key navi-mode-map (kbd "+") 'navi-demote-subtree)
(define-key navi-mode-map (kbd "-") 'navi-promote-subtree)
(define-key navi-mode-map (kbd "^") 'navi-move-up-subtree)
(define-key navi-mode-map (kbd "<") 'navi-move-down-subtree)
(define-key navi-mode-map (kbd "g") 'navi-revert-function)
(define-key navi-mode-map (kbd "q") 'navi-quit-and-switch)
;; TODO define navi command that scrolls twin-buffer
(define-key navi-mode-map (kbd ":") 'scroll-other-window-down)
(define-key navi-mode-map (kbd ".") 'scroll-other-window)
;; ;; original Org-mode keys for `navi-use-outorg' functions
(define-key navi-mode-map (kbd "C-c C-d") 'navi-deadline)
(define-key navi-mode-map (kbd "C-c C-e") 'navi-export-dispatch)
(define-key navi-mode-map (kbd "C-c C-l") 'navi-insert-link)
(define-key navi-mode-map (kbd "C-c C-o") 'navi-open-at-point)
(define-key navi-mode-map (kbd "C-c C-q") 'navi-set-tags-command)
(define-key navi-mode-map (kbd "C-c C-s") 'navi-schedule)
(define-key navi-mode-map (kbd "C-c C-t") 'navi-todo)
(define-key navi-mode-map (kbd "C-c !") 'navi-time-stamp-inactive)
(define-key navi-mode-map (kbd "C-c ,") 'navi-priority)
(define-key navi-mode-map (kbd "C-c .") 'navi-time-stamp)
(define-key navi-mode-map (kbd "C-c :") 'navi-toggle-fixed-width)
(define-key navi-mode-map (kbd "C-c ;") 'navi-toggle-comment)
(define-key navi-mode-map (kbd "C-c ^") 'navi-sort-entries)
(define-key navi-mode-map (kbd "C-c M-b") 'navi-previous-block)
(define-key navi-mode-map (kbd "C-c M-f") 'navi-next-block)
(define-key navi-mode-map (kbd "C-c C-x C-b") 'navi-toggle-checkbox)
(define-key navi-mode-map (kbd "C-c C-x TAB") 'navi-clock-in)
(define-key navi-mode-map (kbd "C-c C-x C-j") 'navi-clock-goto)
(define-key navi-mode-map (kbd "C-c C-x C-o") 'navi-clock-out)
(define-key navi-mode-map (kbd "C-c C-x C-q") 'navi-clock-cancel)
(define-key navi-mode-map (kbd "C-c C-x C-r") 'navi-clock-report)
(define-key navi-mode-map (kbd "C-c C-x C-n") 'navi-next-link)
(define-key navi-mode-map (kbd "C-c M-l")
  'navi-insert-last-stored-link)
(define-key navi-mode-map (kbd "C-c C-x C-p") 'navi-previous-link)
(define-key navi-mode-map (kbd "C-c C-x ,") 'navi-timer-pause-or-continue)
(define-key navi-mode-map (kbd "C-c C-x -") 'navi-timer-item)
(define-key navi-mode-map (kbd "C-c C-x .") 'navi-timer)
(define-key navi-mode-map (kbd "C-c C-x 0") 'navi-timer-start)
(define-key navi-mode-map (kbd "C-c C-x :")
  'navi-timer-cancel-timer)
(define-key navi-mode-map (kbd "C-c C-x ;") 'navi-timer-set-timer)
(define-key navi-mode-map (kbd "C-c C-x <")
  'navi-agenda-set-restriction-lock)
(define-key navi-mode-map (kbd "C-c C-x >")
  'navi-agenda-remove-restriction-lock)
(define-key navi-mode-map (kbd "C-c C-x E") 'navi-inc-effort)
(define-key navi-mode-map (kbd "C-c C-x P")
  'navi-set-property-and-value)
(define-key navi-mode-map (kbd "C-c C-x a")
  'navi-toggle-archive-tag)
(define-key navi-mode-map (kbd "C-c C-x d") 'navi-insert-drawer)
(define-key navi-mode-map (kbd "C-c C-x e") 'navi-set-effort)
(define-key navi-mode-map (kbd "C-c C-x f") 'navi-footnote-action)
(define-key navi-mode-map (kbd "C-c C-x p") 'navi-set-property)

;; menu for navi-mode
(define-key navi-mode-map [menu-bar navi]
  (cons (purecopy "Navi") navi-menu-map))
(define-key navi-mode-map [menu-bar occur] nil)

;; keys for navi-edit-mode
(set-keymap-parent navi-edit-mode-map text-mode-map)
(define-key navi-edit-mode-map [mouse-2] 'occur-mode-mouse-goto)
(define-key navi-edit-mode-map "\M-n" 'occur-next)
(define-key navi-edit-mode-map "\M-p" 'occur-prev)
(define-key navi-edit-mode-map "\M-o" 'occur-mode-display-occurrence)
(define-key navi-edit-mode-map "\C-c\C-f" 'next-error-follow-minor-mode)
(define-key navi-edit-mode-map "\C-c\C-c" 'navi-cease-edit)
;; menu for navi-edit-mode
(define-key navi-edit-mode-map [menu-bar navi] nil)
(define-key navi-edit-mode-map [menu-bar occur] nil)
(define-key navi-edit-mode-map [menu-bar navi-edit]
  (cons (purecopy "Navi-Edit") navi-edit-menu-map))

;;; Run Hooks and Provide

;; (add-to-list 'navi-mode-hook 'navi-mode-hook-function)
;; (run-mode-hooks)

(provide 'navi-mode)

;;; navi-mode.el ends here
