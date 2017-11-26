;;; outshine.el --- outline with outshine outshines outline

;; Maintainer: Adam Porter <adam@alphapapa.net>
;; Version: 2.0
;; URL: http://github.com/alphapapa/outshine
;; Package-Requires: ((outorg "2.0") (cl-lib "0.5"))

;;;; MetaData
;;   :PROPERTIES:
;;   :copyright: Thorsten_Jolitz
;;   :copyright-from: 2013+
;;   :version:  2.0
;;   :licence:  GPL 2 or later (free software)
;;   :licence-url: http://www.gnu.org/licenses/
;;   :part-of-emacs: no
;;   :authors: Thorsten_Jolitz Carsten_Dominik Per_Abrahamsen
;;   :credits:  Fabrice_Niessen Alexander_Vorobiev Jonas_Bernoulli
;;   :inspiration: outline-magic outxxtra out-xtra
;;   :keywords: emacs outlines file_structuring
;;   :git-repo: https://github.com/alphapapa/outshine.git
;;   :git-clone: git://github.com/alphapapa/outshine.git
;;   :END:

;;;; Commentary

;;;;; About outshine

;; Outshine attempts to bring the look&feel of Org-mode to the (GNU
;; Emacs) world outside of the Org major-mode. It is an extension of
;; outline-minor-mode (Org-mode itself derives from outline-mode), so
;; there is no such thing like an 'outshine mode', only
;; `outline-minor-mode' with outshine extensions loaded.

;; Outshine is major-mode agnostic. At least in theory, it should work
;; out-of-the-box with all major-modes, even those not yet written, as
;; long as these modes have comment syntax defined. In real life there
;; are some major-modes where outshine just works, others that need
;; some minor tweaks to make outshine work, and a few that need
;; special handling.

;; An outshine file is structured just like an org file, only that the
;; headlines are outcommented with the current major-mode's comment
;; syntax. We call these outcommented org headers 'outshine
;; headers'. The different headline levels are fontified like in
;; Org-mode, and many of the outline-navigation, visibility cycling
;; and structure editing commands known from Org-mode work in outshine
;; too. An Org-mode user will feel right at home in an outshine
;; buffer, the look&feel should be pretty similar, only the
;; keybindings differ. Since outshine extends a minor-mode it has to
;; avoid conflicts with major-mode keymaps by using a rather unusual
;; prefix that is still easy to type (M-#). But the Org-mode
;; speed-commands have been ported to outshine too, and they use
;; exactly the same (one-key) bindings like in Org-mode.

;; There is a distinction between the library 'outshine.el' and the
;; 'Outshine Project' (or 'Outshine Suite') which contains 3
;; libraries:

;;  - outshine.el :: The core library. The `outshine-hook-function'
;;                   must be added to the `outline-minor-mode-hook' to
;;                   activate its extensions when outline-minor-mode
;;                   is loaded.

;;  - outorg.el :: Major-mode for toggling between the
;;                 programming-mode view and the org-mode view of
;;                 outshine buffers, i.e. buffers structured with
;;                 outshine headers that have outline-minor-mode with
;;                 outshine extensions activated.

;;  - navi-mode.el :: Occur-based major-mode for super-fast
;;                    buffer-navigation and buffer-remote-control with
;;                    one-key-bindings from an associated read-only
;;                    *Navi* buffer. Navi-mode allows to have the
;;                    (outshine- or org-) buffer overview side by side
;;                    with the buffer details, and it gives many
;;                    different kinds of overviews (these views are
;;                    actually customizable). With point in the *Navi*
;;                    overview buffer, many actions in the associated
;;                    original (outshine- or org-) buffer can be
;;                    triggered without leaving the *Navi* buffer.


;; Note that there is a fourth library 'poporg.el' from François
;; Pinard, which allows to edit function docstrings in temporary
;; Org-mode buffers and thus nicely complements 'outorg.el'.

;; Together these libraries enable a lightweight kind of 'literate
;; programming' that turns the usual implementation of the concept
;; upside-down: instead of using a text-mode as default and taking
;; extra action to edit and execute source-code, with Outshine the
;; programming-mode is the default mode and the text-mode
;; (i.e. Org-mode) only called when needed. This is much simpler, it
;; treats Org-mode and Programming-mode simply as two different views
;; on the same (outshine) file while making it easy to switch between
;; these views.

;;;;; History and Credits

;; The outshine.el library merges, modifies and extends two existing
;; extension-libraries for `outline' (minor) mode: `outline-magic' (by
;; Carsten Dominik) and `out-xtra' (by Per Abrahamsen). It offers all the
;; functionality of `outline-magic' (with some tiny changes and fixes)
;; and parts of the functionality of `out-xtra', together with many new
;; features and ideas.

;; See `outline-magic.el' (https://github.com/tj64/outline-magic) for
;; detailled instructions on the usage of the additional outline
;; functions introduced by `outline-magic'.

;; Furthermore, `outshine.el' includes some functions and keybindings
;; from `outline-mode-easy-bindings'
;; (http://emacswiki.org/emacs/OutlineMinorMode).  Unfortunately, no
;; author is given for that library, so I cannot credit the person who
;; wrote it.

;;;;; Installation

;; There are three ways to get outshine.el (and the other Outshine
;; libraries):

;;  1. Clone the git repos or fork them on github
;;     (https://github.com/alphapapa)

;;  2. Use the package manager to install them (from MELPA).

;;  3. Simply download the raw .el files from github and copy them to a
;;     location where Emacs can find. This is not really recommended,
;;     since easy updating is not possible this way.

;; Note that since version 2.0, outshine.el depends on outorg.el and
;; navi-mode.el depends on both, outshine.el and outorg.el. So the order
;; of installation should be

;;  1. outorg
;;  2. outshine
;;  3. navi-mode (optional)

;; Put this in your init.el or '.emacs' to get started:

;; : #+begin_src emacs-lisp
;; :   (require 'outshine)
;; :   (add-hook 'outline-minor-mode-hook 'outshine-hook-function)
;; : #+end_src

;; Add this to your init file if you always want outshine for emacs-lisp
;; buffers (recommended):

;; : #+begin_src emacs-lisp
;; :   (add-hook 'emacs-lisp-mode-hook 'outline-minor-mode)
;; : #+end_src

;; It makes sense to add 'outline-minor-mode' to the hooks of other
;; major-modes too, e.g.

;; : #+begin_src emacs-lisp
;; :  (add-hook 'LaTeX-mode-hook 'outline-minor-mode)
;; :  (add-hook 'picolisp-mode-hook 'outline-minor-mode)
;; :  (add-hook 'clojure-mode-hook 'outline-minor-mode)
;; :  (add-hook 'ess-mode-hook 'outline-minor-mode)
;; :  (add-hook 'ledger-mode-hook 'outline-minor-mode)
;; :  (add-hook 'message-mode-hook 'outline-minor-mode)
;; : #+end_src

;; or whatever your favorite Emacs modes are. Then you can structure and
;; handle all your source-files just like Org files, allowing for a
;; uniform approach to file structuring independent from the (text or
;; programming) mode.

;; Outline(-minor)-mode comes with a rather unusable prefix key
;; out-of-the-box. You need to set the outshine prefix (M-#) in your init
;; file before (!) outline-mode is loaded to enable the outshine
;; keybindings:

;; : #+begin_src emacs-lisp
;; :  (defvar outline-minor-mode-prefix "\M-#")
;; : #+end_src

;;;;; Usage

;;;;;; Basic Usage

;; The outshine.el extensions to outline-minor-mode aim to make its
;; use more similar to Org-mode. Given a correctly structured outshine
;; buffer, outline-navigation, structure-editing and visibility
;; cycling with outshine should make an Org-mode user feel right at
;; home.

;; Try C-h m (describe-mode) and C-h b (describe-bindings) in an
;; outshine buffer to find out more about the available functions and
;; their keybindings.

;; The very useful Org speed-commands have been ported to outshine,
;; here a quote from the
;; [[http://orgmode.org/manual/Speed-keys.html][Org-mode manual]] that
;; describes what they do:

;; #+BEGIN_QUOTE
;;  Single keys can be made to execute commands when the cursor is at
;;  the beginning of a headline, i.e., before the first star.
;; #+END_QUOTE

;; To activate speed-keys, put this in your init-file:

;; : #+BEGIN_SRC emacs-lisp
;; :  (setq outshine-use-speed-commands t)
;; : #+END_SRC

;; Call `outshine-speed-command-help' to get an overview over the
;; available functionality and the keybindings.

;; Note that outshine works with 'imenu' (`outshine-imenu') and has
;; extra functionality to show the number of hidden lines in folded
;; headlines (`outshine-show-hidden-lines-cookies'). There are a few
;; utility commands for latex-mode too
;; (`outshine-latex-insert-header',
;; `outshine-latex-insert-headers-in-buffer' and
;; `outshine-TeX-command-region-on-subtree')

;;;;;; Extended Usage (outshine-use-outorg)

;; Outshine's basic usage is mostly based on its own implementation,
;; i.e. code from existing extensions to outline-minor-mode, new code
;; written for outshine, as well as code ported from Org-mode to
;; outshine.

;; Its extended use aims to make outshine headers more 'intelligent',
;; i.e. make them know about TODO items, tags, properties, dates and
;; times. This is done via the `outshine-use-outorg' function that
;; uses outorg to first convert an outshine buffer/subtree to
;; org-mode, then call an Org function on it, and finally convert the
;; edited buffer/subtree back to outshine. The outshine-use-outorg
;; concept turns outshine into a kind of org-minor-mode without
;; actually reimplementing Org functionality, just by reusing it with
;; the help of outorg.

;; This is still work in progress. Not all Org commands make sense in
;; an outshine buffer. Not all work out-of-the-box. Since there are
;; many Org commands, it will take some time to check them one-by-one
;; and filter out those that make sense with outshine (and fix them if
;; neccessary).

;;;;; Emacs Version

;; Outshine works with GNU Emacs 24 or later. No attempts of testing
;; with older versions or other types of Emacs have been made (yet).

;;;; ChangeLog

;; | date            | author(s)       | version |
;; |-----------------+-----------------+---------|
;; | <2014-09-20 Sa> | Thorsten Jolitz |     2.0 |
;; | <2013-05-03 Fr> | Thorsten Jolitz |     1.0 |
;; | <2013-02-20 Mi> | Thorsten Jolitz |     0.9 |

;;; Requires

(eval-when-compile
  (require 'cl))
(require 'outline)
(require 'outorg)
(require 'outshine-org-cmds)
;; necessary before Emacs 24.3
(require 'newcomment)
;; (require 'easymenu)
(require 'cl-lib)

;;; Declarations

(declare-function outorg-edit-as-org "outorg")
(declare-function outorg-copy-edits-and-exit "outorg")
(declare-function navi-map-keyboard-to-key "navi-mode")
(declare-function navi-search-and-switch "navi-mode")
(declare-function navi-get-regexp "navi-mode")
(declare-function idomenu "idomenu")
(declare-function imenu-choose-buffer-index "imenu")
(declare-function org-agenda-remove-restriction-lock "org-agenda")

;;; Variables
;;;; Consts

(defconst outshine-version "2.0"
  "outshine version number.")

(defconst outshine-max-level 8
  "Maximal level of headlines recognized.")

;; copied from org-source.el
(defconst outshine-level-faces '(outshine-level-1
  outshine-level-2 outshine-level-3 outshine-level-4
  outshine-level-5 outshine-level-6 outshine-level-7
  outshine-level-8))

(defconst outshine-outline-heading-end-regexp "\n"
  "Global default value of `outline-heading-end-regexp'.
Used to override any major-mode specific file-local settings")

;; was "[;]+"
(defconst outshine-oldschool-elisp-outline-regexp-base
  (format "[;]\\{1,%d\\}" outshine-max-level)
  "Oldschool Emacs Lisp base for calculating the outline-regexp")

(defconst outshine-speed-commands-default
  '(
    ("Outline Navigation")
    ;; [X]
    ("n" . (outshine-speed-move-safe
            'outline-next-visible-heading))
    ;; [X]
    ("p" . (outshine-speed-move-safe
            'outline-previous-visible-heading))
    ;; [X]
    ("f" . (outshine-speed-move-safe
            'outline-forward-same-level))
    ;; [X]
    ("u" . (outshine-speed-move-safe
            'outline-up-heading))
    ;; [X]
    ("b" . (outshine-speed-move-safe
            'outline-backward-same-level))
    ;; [X] similar semantics
    ("F" . outshine-next-block)
    ;; [X] similar semantics
    ("B" . outshine-previous-block)
    ;; [X] similar semantics org-goto
    ("j" . outshine-navi)
    ;; [X] similar semantics org-goto
    ("J" . outshine-imenu)
    ;; [X] similar semantics (org-refile t)
    ;; ("g" . outshine-refile)
    ("g" . outshine-imenu)
    ("Outline Visibility")
    ;; [X]
    ("c" . outline-cycle)
    ;; [X]
    ("C" . outshine-cycle-buffer)
    ;; [X]
    (" " . (outshine-use-outorg
	    'org-display-outline-path
            'WHOLE-BUFFER-P))
    ;; [X]
    ("r" . outshine-narrow-to-subtree)
    ;; [X]
    ("w" . widen)
    ;; ;; [ ]
    ;; ("=" . outshine-columns)
    ("Outline Structure Editing")
    ;; [X] FIXME error with oldschool elisp headers
    ("U" . outline-move-subtree-up)
    ;; [X] FIXME error with oldschool elisp headers
    ("D" . outline-move-subtree-down)
    ;; [X]
    ("+" . outline-demote)
    ;; [X]
    ("-" . outline-promote)
    ;; [X]
    ("i" . outshine-insert-heading)
    ;; [X] FIXME handle markers, special cases
    ("^" . outshine-sort-entries)
    ;; ;; [ ]
    ;; ("a" . (outshine-use-outorg
    ;;      'org-archive-subtree-default-with-confirmation))
    ;; [X]
    ("m" . outline-mark-subtree)
    ;; [X]
    ("#" . outshine-toggle-comment)
    ("Clock Commands")
    ;; FIXME need improvements!
    ;; [X]
    ("I" . outshine-clock-in)
    ;; [X]
    ("O" . outshine-clock-out)
    ("Date & Time Commands")
    ;; [X]
    ("." . outshine-time-stamp)
    ;; [X]
    ("!" . outshine-time-stamp-inactive)
    ;; [X] TODO add up/down(day)
    ("d" . outshine-deadline)
    ;; [X]
    ("s" . outshine-schedule)
    ("Exporting")
    ;; [X]
    ("x" . outshine-export-dispatch)
    ("Meta Data Editing")
    ;; [X]
    ("t" . outshine-todo)
    ;; [X]
    ("," . outshine-priority)
    ;; [X]
    ("0" . (outshine-use-outorg
	    (lambda () (interactive) (org-priority ?\ ))))
    ;; [X]
    ("1" . (outshine-use-outorg
	    (lambda () (interactive) (org-priority ?A))))
    ;; [X]
    ("2" . (outshine-use-outorg
	    (lambda () (interactive) (org-priority ?B))))
    ;; [X]
    ("3" . (outshine-use-outorg
	    (lambda () (interactive) (org-priority ?C))))
    ;; [X]
    (":" . outshine-set-tags-command)
    ;; ;; [ ]
    ;; ("W" . (lambda(m) (interactive "sMinutes before warning: ")
    ;;       (outshine-entry-put (point) "APPT_WARNTIME" m)))
    ("Properties and Effort")
    ;; [X]
    ("y" . outshine-set-property)
    ;; [X]
    ("Y" . outshine-set-property-and-value)
    ;; [X]
    ("e" . outshine-set-effort)
    ;; [X]
    ("E" . outshine-inc-effort)
    ;; ("Agenda Views etc")
    ;; [X]
    ("v" . outshine-agenda)
    ;; [X]
    ("<" . (outshine-agenda-set-restriction-lock))
    ;; [X]
    (">" . (outshine-agenda-remove-restriction-lock))
    ;; ;; CANCELLED makes no sense
    ;; ("/" . outshine-sparse-tree)
    ("Misc")
    ;; [X]
    ("o" . outshine-open-at-point)
    ;; [X]
    ("?" . outshine-speed-command-help)
    )
  "The default speed commands.")


(defconst outshine-comment-tag "comment"
  "The tag that marks a subtree as comment.
A comment subtree does not open during visibility cycling.")

(defconst outshine-latex-documentclass-regexp
  "^[[:space:]]*\\\\documentclass\\(?:\\[.+]\\)?{\\(.+\\)}"
  "Regexp matching the document class in a latex doc (in submatch
  1)")

;;;; Vars

;; "\C-c" conflicts with other modes like e.g. ESS
(defvar outline-minor-mode-prefix "\M-#"
  "New outline-minor-mode prefix.
Does not really take effect when set in the `outshine' library.
Instead, it must be set in your init file *before* the `outline'
library is loaded, see the installation tips in the comment
section of `outshine'.")

;; from `outline-magic'
(defvar outline-promotion-headings nil
  "A sorted list of headings used for promotion/demotion commands.
Set this to a list of headings as they are matched by `outline-regexp',
top-level heading first.  If a mode or document needs several sets of
outline headings (for example numbered and unnumbered sections), list
them set by set, separated by a nil element.  See the example for
`texinfo-mode' in the file commentary.")
(make-variable-buffer-local 'outline-promotion-headings)

(defvar outshine-delete-leading-whitespace-from-outline-regexp-base-p nil
  "If non-nil, delete leading whitespace from outline-regexp-base.")
(make-variable-buffer-local
 'outshine-delete-leading-whitespace-from-outline-regexp-base-p)

(defvar outshine-enforce-no-comment-padding-p nil
  "If non-nil, make sure no comment-padding is used in heading.")
(make-variable-buffer-local
 'outshine-enforce-no-comment-padding-p)

(defvar outshine-outline-regexp-base ""
  "Actual base for calculating the outline-regexp")

(defvar outshine-normalized-comment-start ""
  "Comment-start regexp without leading and trailing whitespace")
(make-variable-buffer-local
 'outshine-normalized-comment-start)

(defvar outshine-normalized-comment-end ""
  "Comment-end regexp without leading and trailing whitespace")
(make-variable-buffer-local
 'outshine-normalized-comment-end)

(defvar outshine-normalized-outline-regexp-base ""
  "Outline-regex-base without leading and trailing whitespace")
(make-variable-buffer-local
 'outshine-normalized-outline-regexp-base)

;; show number of hidden lines in folded subtree
(defvar outshine-show-hidden-lines-cookies-p nil
  "If non-nil, commands for hidden-lines cookies are activated.")

;; remember if hidden-lines cookies are shown or hidden
(defvar outshine-hidden-lines-cookies-on-p nil
  "If non-nil, hidden-lines cookies are shown, otherwise hidden.")

(defvar outshine-imenu-default-generic-expression nil
  "Expression assigned by default to `imenu-generic-expression'.")
(make-variable-buffer-local
 'outshine-imenu-default-generic-expression)

(defvar outshine-imenu-generic-expression nil
  "Expression assigned to `imenu-generic-expression'.")
(make-variable-buffer-local
 'outshine-imenu-generic-expression)

(defvar outshine-self-insert-command-undo-counter 0
  "Used for outshine speed-commands.")

(defvar outshine-speed-command nil
  "Used for outshine speed-commands.")

(defvar outshine-open-comment-trees nil
  "Cycle comment-subtrees anyway when non-nil.")

(defvar outshine-current-buffer-visibility-state nil
  "Stores current visibility state of buffer.")

(defvar outshine-use-outorg-last-headline-marker (make-marker)
  "Marker for last headline edited with outorg.")
(make-variable-buffer-local
 'outshine-use-outorg-last-headline-marker)

(defvar outshine-imenu-preliminary-generic-expression nil
  "Imenu variable.")

(defvar outshine-agenda-files ()
  "List of absolute file names of outshine-agenda-files.")

(defvar outshine-agenda-include-org-agenda-p nil
  "Include Org Agenda files in Outshine Agenda when non-nil.")

(defvar outshine-agenda-old-org-agenda-files nil
  "Storage for old value of `org-agenda-files'")

;; copied and adapted from ob-core.el
;; (defvar outshine-temporary-directory)
;; (unless (or noninteractive (boundp 'outshine-temporary-directory))
;; ;; FIXME why this duplication?
;;   (defvar outshine-temporary-directory
;;     (or (and (boundp 'outshine-temporary-directory)
;; 	     (file-exists-p outshine-temporary-directory)
;; 	     outshine-temporary-directory)
;; 	(make-temp-file "outshine-" t))
;;     "Directory to hold outshine's temporary files."))

;;;; Hooks

(defvar outshine-hook nil
  "Functions to run after `outshine' is loaded.")

;;;; Faces

;; from `org-compat.el'
(defun outshine-compatible-face (inherits specs)
  "Make a compatible face specification.
If INHERITS is an existing face and if the Emacs version supports it,
just inherit the face.  If INHERITS is set and the Emacs version does
not support it, copy the face specification from the inheritance face.
If INHERITS is not given and SPECS is, use SPECS to define the face.
XEmacs and Emacs 21 do not know about the `min-colors' attribute.
For them we convert a (min-colors 8) entry to a `tty' entry and move it
to the top of the list.  The `min-colors' attribute will be removed from
any other entries, and any resulting duplicates will be removed entirely."
  (when (and inherits (facep inherits) (not specs))
    (setq specs (or specs
                    (get inherits 'saved-face)
                    (get inherits 'face-defface-spec))))
  (cond   ((and inherits (facep inherits)
         (not (featurep 'xemacs))
         (>= emacs-major-version 22)
         ;; do not inherit outline faces before Emacs 23
         (or (>= emacs-major-version 23)
             (not (string-match "\\`outline-[0-9]+"
                                (symbol-name inherits)))))
    (list (list t :inherit inherits)))
   ((or (featurep 'xemacs) (< emacs-major-version 22))
    ;; These do not understand the `min-colors' attribute.
    (let (r e a)
      (while (setq e (pop specs))
        (cond
         ((memq (car e) '(t default)) (push e r))
         ((setq a (member '(min-colors 8) (car e)))
          (nconc r (list (cons (cons '(type tty) (delq (car a) (car e)))
                               (cdr e)))))
         ((setq a (assq 'min-colors (car e)))
          (setq e (cons (delq a (car e)) (cdr e)))
          (or (assoc (car e) r) (push e r)))
         (t (or (assoc (car e) r) (push e r)))))
      (nreverse r)))
   (t specs)))
(put 'outshine-compatible-face 'lisp-indent-function 1)

;; The following face definitions are from `org-faces.el'
;; originally copied from font-lock-function-name-face
(defface outshine-level-1
  (outshine-compatible-face 'outline-1
    '((((class color) (min-colors 88)
        (background light)) (:foreground "Blue1"))
      (((class color) (min-colors 88)
        (background dark)) (:foreground "LightSkyBlue"))
      (((class color) (min-colors 16)
        (background light)) (:foreground "Blue"))
      (((class color) (min-colors 16)
        (background dark)) (:foreground "LightSkyBlue"))
      (((class color) (min-colors 8)) (:foreground "blue" :bold t))
      (t (:bold t))))
  "Face used for level 1 headlines."
  :group 'outshine-faces)

;; originally copied from font-lock-variable-name-face
(defface outshine-level-2
  (outshine-compatible-face 'outline-2
    '((((class color) (min-colors 16)
        (background light)) (:foreground "DarkGoldenrod"))
      (((class color) (min-colors 16)
        (background dark))  (:foreground "LightGoldenrod"))
      (((class color) (min-colors 8)
        (background light)) (:foreground "yellow"))
      (((class color) (min-colors 8)
        (background dark))  (:foreground "yellow" :bold t))
      (t (:bold t))))
  "Face used for level 2 headlines."
  :group 'outshine-faces)

;; originally copied from font-lock-keyword-face
(defface outshine-level-3
  (outshine-compatible-face 'outline-3
    '((((class color) (min-colors 88)
        (background light)) (:foreground "Purple"))
      (((class color) (min-colors 88)
        (background dark))  (:foreground "Cyan1"))
      (((class color) (min-colors 16)
        (background light)) (:foreground "Purple"))
      (((class color) (min-colors 16)
        (background dark))  (:foreground "Cyan"))
      (((class color) (min-colors 8)
        (background light)) (:foreground "purple" :bold t))
      (((class color) (min-colors 8)
        (background dark))  (:foreground "cyan" :bold t))
      (t (:bold t))))
  "Face used for level 3 headlines."
  :group 'outshine-faces)

   ;; originally copied from font-lock-comment-face
(defface outshine-level-4
  (outshine-compatible-face 'outline-4
    '((((class color) (min-colors 88)
        (background light)) (:foreground "Firebrick"))
      (((class color) (min-colors 88)
        (background dark))  (:foreground "chocolate1"))
      (((class color) (min-colors 16)
        (background light)) (:foreground "red"))
      (((class color) (min-colors 16)
        (background dark))  (:foreground "red1"))
      (((class color) (min-colors 8)
        (background light))  (:foreground "red" :bold t))
      (((class color) (min-colors 8)
        (background dark))   (:foreground "red" :bold t))
      (t (:bold t))))
  "Face used for level 4 headlines."
  :group 'outshine-faces)

 ;; originally copied from font-lock-type-face
(defface outshine-level-5
  (outshine-compatible-face 'outline-5
    '((((class color) (min-colors 16)
        (background light)) (:foreground "ForestGreen"))
      (((class color) (min-colors 16)
        (background dark)) (:foreground "PaleGreen"))
      (((class color) (min-colors 8)) (:foreground "green"))))
  "Face used for level 5 headlines."
  :group 'outshine-faces)

 ;; originally copied from font-lock-constant-face
(defface outshine-level-6
  (outshine-compatible-face 'outline-6
    '((((class color) (min-colors 16)
        (background light)) (:foreground "CadetBlue"))
      (((class color) (min-colors 16)
        (background dark)) (:foreground "Aquamarine"))
      (((class color) (min-colors 8)) (:foreground "magenta")))) "Face used for level 6 headlines."
  :group 'outshine-faces)

 ;; originally copied from font-lock-builtin-face
(defface outshine-level-7
  (outshine-compatible-face 'outline-7
    '((((class color) (min-colors 16)
        (background light)) (:foreground "Orchid"))
      (((class color) (min-colors 16)
        (background dark)) (:foreground "LightSteelBlue"))
      (((class color) (min-colors 8)) (:foreground "blue"))))
  "Face used for level 7 headlines."
  :group 'outshine-faces)

 ;; originally copied from font-lock-string-face
(defface outshine-level-8
  (outshine-compatible-face 'outline-8
    '((((class color) (min-colors 16)
        (background light)) (:foreground "RosyBrown"))
      (((class color) (min-colors 16)
        (background dark)) (:foreground "LightSalmon"))
      (((class color) (min-colors 8)) (:foreground "green"))))
  "Face used for level 8 headlines."
  :group 'outshine-faces)

;;;; Customs
;;;;; Custom Groups

(defgroup outshine nil
  "Enhanced library for outline navigation in source code buffers."
  :prefix "outshine-"
  :group 'lisp)

(defgroup outshine-faces nil
  "Faces in Outshine."
  :tag "Outshine Faces"
  :group 'outshine)


;;;;; Custom Vars

(defcustom outshine-imenu-show-headlines-p t
  "Non-nil means use calculated outline-regexp for imenu."
  :group 'outshine
  :type 'boolean)

(defcustom outshine-fontify t
  ;; `quote' instead of ' to avoid conversion of ' in for example C-h v
  ;; (`describe-variable').
  "When to fontify the outshine headings in a buffer.

Possible values are:

 `t'        Always (the default).
 `nil'      Never.
 function   A Lisp predicate function with no arguments. For example
            `(lambda () (not (derived-mode-p (quote prog-mode))))'
            fontifies only when not in a programming mode.

`t' and `nil' can be used for a file local variable to make an
exception for certain files or to be independent of the user's
customization."
  :group 'outshine
  :type '(choice :value ""
                 (const :tag "Always (the default)" t)
                 (const :tag "Never" nil)
                 (function :tag "Function"))
  :safe (lambda (v) (memq v '(t nil))))

;; from `org'
(defcustom outshine-fontify-whole-heading-line nil
  "Non-nil means fontify the whole line for headings.
This is useful when setting a background color for the
poutshine-level-* faces."
  :group 'outshine
  :type 'boolean)

(defcustom outshine-outline-regexp-outcommented-p t
  "Non-nil if regexp-base is outcommented to calculate outline-regexp."
  :group 'outshine
  :type 'boolean)

;; was "[][+]"
(defcustom outshine-outline-regexp-special-chars
  "[][}{,+[:digit:]\\]"
  "Regexp for detecting (special) characters in outline-regexp.
These special chars will be stripped when the outline-regexp is
transformed into a string, e.g. when the outline-string for a
certain level is calculated. "
  :group 'outshine
  :type 'regexp)

;; from `outline-magic'
(defcustom outline-cycle-emulate-tab nil
  "Where should `outline-cycle' emulate TAB.
nil    Never
white  Only in completely white lines
t      Everywhere except in headlines"
  :group 'outlines
  :type '(choice (const :tag "Never" nil)
                 (const :tag "Only in completely white lines" white)
                 (const :tag "Everywhere except in headlines" t)
                 ))

;; from `outline-magic'
(defcustom outline-structedit-modifiers '(meta)
  "List of modifiers for outline structure editing with the arrow keys."
  :group 'outlines
  :type '(repeat symbol))

;; startup options
(defcustom outshine-startup-folded-p nil
  "Non-nil means files will be opened with all but top level headers folded."
  :group 'outshine
  :type 'boolean)

(defcustom outshine-hidden-lines-cookie-left-delimiter "["
  "Left delimiter of cookie that shows number of hidden lines."
  :group 'outshine
  :type 'string)

(defcustom outshine-hidden-lines-cookie-right-delimiter "]"
  "Left delimiter of cookie that shows number of hidden lines."
  :group 'outshine
  :type 'string)

(defcustom outshine-hidden-lines-cookie-left-signal-char "#"
  "Left signal character of cookie that shows number of hidden lines."
  :group 'outshine
  :type 'string)

(defcustom outshine-hidden-lines-cookie-right-signal-char ""
  "Right signal character of cookie that shows number of hidden lines."
  :group 'outshine
  :type 'string)

(defcustom outshine-regexp-base-char "*"
  "Character used in outline-regexp base."
  :group 'outshine
  :type 'string)



;; old regexp: "[*]+"
(defvar outshine-default-outline-regexp-base
  (format "[%s]\\{1,%d\\}"
          outshine-regexp-base-char outshine-max-level)
  "Default base for calculating the outline-regexp")

;; TODO delete this line  "\\(\\[\\)\\([[:digit:]+]\\)\\( L\\]\\)"
(defvar outshine-hidden-lines-cookie-format-regexp
  (concat
   "\\( "
   (regexp-quote outshine-hidden-lines-cookie-left-delimiter)
   (regexp-quote outshine-hidden-lines-cookie-left-signal-char)
   "\\)"
   "\\([[:digit:]]+\\)"
   "\\("
   (regexp-quote outshine-hidden-lines-cookie-right-signal-char)
   ;; FIXME robust enough?
   (format "\\%s" outshine-hidden-lines-cookie-right-delimiter)
   "\\)")
  "Matches cookies that show number of hidden lines for folded subtrees.")

(defvar outshine-cycle-silently nil
  "Suppress visibility-state-change messages when non-nil.")

(defcustom outshine-org-style-global-cycling-at-bob-p nil
  "Cycle globally if cursor is at beginning of buffer and not at a headline.

This makes it possible to do global cycling without having to use
S-TAB or C-u TAB.  For this special case to work, the first line
of the buffer must not be a headline -- it may be empty or some
other text. When this option is nil, don't do anything special at
the beginning of the buffer."
  :group 'outshine
  :type 'boolean)

(defcustom outshine-use-speed-commands nil
  "Non-nil means activate single letter commands at beginning of a headline.
This may also be a function to test for appropriate locations
where speed commands should be active, e.g.:

    (setq outshine-use-speed-commands
      (lambda ()  ( ...your code here ... ))"
  :group 'outshine
  :type '(choice
          (const :tag "Never" nil)
          (const :tag "At beginning of headline stars" t)
          (function)))

(defcustom outshine-speed-commands-user nil
  "Alist of additional speed commands.
This list will be checked before `outshine-speed-commands-default'
when the variable `outshine-use-speed-commands' is non-nil
and when the cursor is at the beginning of a headline.
The car if each entry is a string with a single letter, which must
be assigned to `self-insert-command' in the global map.
The cdr is either a command to be called interactively, a function
to be called, or a form to be evaluated.
An entry that is just a list with a single string will be interpreted
as a descriptive headline that will be added when listing the speed
commands in the Help buffer using the `?' speed command."
  :group 'outshine
  :type '(repeat :value ("k" . ignore)
                 (choice :value ("k" . ignore)
                         (list :tag "Descriptive Headline" (string :tag "Headline"))
                         (cons :tag "Letter and Command"
                               (string :tag "Command letter")
                               (choice
                                (function)
                                (sexp))))))

(defcustom outshine-speed-command-hook
  '(outshine-speed-command-activate)
  "Hook for activating speed commands at strategic locations.
Hook functions are called in sequence until a valid handler is
found.

Each hook takes a single argument, a user-pressed command key
which is also a `self-insert-command' from the global map.

Within the hook, examine the cursor position and the command key
and return nil or a valid handler as appropriate.  Handler could
be one of an interactive command, a function, or a form.

Set `outshine-use-speed-commands' to non-nil value to enable this
hook.  The default setting is `outshine-speed-command-activate'."
  :group 'outshine
  :version "24.1"
  :type 'hook)

(defcustom outshine-self-insert-cluster-for-undo
  (or (featurep 'xemacs) (version<= emacs-version "24.1"))
  "Non-nil means cluster self-insert commands for undo when possible.
If this is set, then, like in the Emacs command loop, 20 consecutive
characters will be undone together.
This is configurable, because there is some impact on typing performance."
  :group 'outshine
  :type 'boolean)

(defcustom outshine-latex-classes
  '(("scrbook" . ((1 . "^[[:space:]]*\\\\part\\*?{\\(.+\\)}")
		  (2 . "^[[:space:]]*\\\\chapter\\*?{\\(.+\\)}")
		  (3 . "^[[:space:]]*\\\\section\\*?{\\(.+\\)}")
		  (4 . "^[[:space:]]*\\\\subsection\\*?{\\(.+\\)}")
		  (5 . "^[[:space:]]*\\\\subsubsection\\*?{\\(.+\\)}")
		  (6 . "^[[:space:]]*\\\\paragraph\\*?{\\(.+\\)}")
		  (7 . "^[[:space:]]*\\\\subparagraph\\*?{\\(.+\\)}")))
    ("book" . ((1 . "^[[:space:]]*\\\\part\\*?{\\(.+\\)}")
	       (2 . "^[[:space:]]*\\\\chapter\\*?{\\(.+\\)}")
	       (3 . "^[[:space:]]*\\\\section\\*?{\\(.+\\)}")
	       (4 . "^[[:space:]]*\\\\subsection\\*?{\\(.+\\)}")
	       (5 . "^[[:space:]]*\\\\subsubsection\\*?{\\(.+\\)}")))
    ("report" . ((1 . "^[[:space:]]*\\\\part\\*?{\\(.+\\)}")
		 (2 . "^[[:space:]]*\\\\chapter\\*?{\\(.+\\)}")
		 (3 . "^[[:space:]]*\\\\section\\*?{\\(.+\\)}")
		 (4 . "^[[:space:]]*\\\\subsection\\*?{\\(.+\\)}")
		 (5 . "^[[:space:]]*\\\\subsubsection\\*?{\\(.+\\)}")))
    ("scrartcl" . ((1 . "^[[:space:]]*\\\\section\\*?{\\(.+\\)}")
		   (2 . "^[[:space:]]*\\\\subsection\\*?{\\(.+\\)}")
		   (3 . "^[[:space:]]*\\\\subsubsection\\*?{\\(.+\\)}")
		   (4 . "^[[:space:]]*\\\\paragraph\\*?{\\(.+\\)}")
		   (5 . "^[[:space:]]*\\\\subparagraph\\*?{\\(.+\\)}")))
    ("article" . ((1 . "^[[:space:]]*\\\\section\\*?{\\(.+\\)}")
		  (2 . "^[[:space:]]*\\\\subsection\\*?{\\(.+\\)}")
		  (3 . "^[[:space:]]*\\\\subsubsection\\*?{\\(.+\\)}")
		  (4 . "^[[:space:]]*\\\\paragraph\\*?{\\(.+\\)}")
		  (5 . "^[[:space:]]*\\\\subparagraph\\*?{\\(.+\\)}"))))
  "Sectioning structure of LaTeX classes.
For each class, the outline level and a regexp matching the latex
section are given (with section title in submatch 1)."
  :group 'outshine
  :type '(alist :key-type string
                :value-type alist))

(defcustom outshine-preserve-delimiter-whitespace nil
  "Non-nil means that whitespace present at the start or end of
`comment-start' is preserved when matching headline syntax. By
default, such space is removed to support language modes which
erroneously include it in `comment-start', but for other
languages, such as Haskell, the trailing whitespace is
significant."
  :group 'outshine
  :type 'boolean)

;;; Defuns
;;;; Advices

(defun outshine-mimic-org-log-note-marker ()
  (if (version< (org-version) "8.3")
      ;; `org-log-beginning' added in Org 8.3
      org-log-note-marker
    (with-current-buffer (marker-buffer org-log-note-marker)
      (goto-char org-log-note-marker)
      (copy-marker (org-log-beginning)))))

(defadvice org-store-log-note (around org-store-log-note-around activate)
  "Outcomment inserted log-note in Outshine buffers."
  (let ((outshine-log-note-beg-marker
	 ;; stay before inserted text
	 ;; (copy-marker org-log-note-marker nil))
	 (copy-marker (outshine-mimic-org-log-note-marker) nil))
	(outshine-log-note-end-marker
	 ;; stay after inserted text
	 ;; (copy-marker org-log-note-marker t)))
	 (copy-marker (outshine-mimic-org-log-note-marker) t)))
    ad-do-it
    (unless (derived-mode-p 'org-mode 'org-agenda-mode)
      (outshine-comment-region outshine-log-note-beg-marker
		      outshine-log-note-end-marker))
    (move-marker outshine-log-note-beg-marker nil)
    (move-marker outshine-log-note-end-marker nil)))

;;;; Functions
;;;;; Define keys with fallback

;; copied and adapted from Alexander Vorobiev
;; http://www.mail-archive.com/emacs-orgmode@gnu.org/msg70648.html
(defmacro outshine-define-key-with-fallback
  (keymap key def condition &optional mode)
  "Define key with fallback.
Binds KEY to definition DEF in keymap KEYMAP, the binding is
active when the CONDITION is true. Otherwise turns MODE off and
re-enables previous definition for KEY. If MODE is nil, tries to
recover it by stripping off \"-map\" from KEYMAP name."
  `(define-key
     ,keymap
     ,key
     (lambda (&optional arg)
       (interactive "P")
       (if ,condition ,def
         (let* ((,(if mode mode
                    (let* ((keymap-str (symbol-name keymap))
                           (mode-name-end
                            (- (string-width keymap-str) 4)))
                      (if (string=
                           "-map"
                           (substring keymap-str mode-name-end))
                          (intern (substring keymap-str 0 mode-name-end))
                        (message
                         "Could not deduce mode name from keymap name")
                        (intern "dummy-sym"))
                      )) nil)
                ;; Check for `<tab>'.  It translates to `TAB' which
                ;; will prevent `(key-binding ...)' from finding the
                ;; original binding.
                (original-func (if (equal (kbd "<tab>") ,key)
                                   (or (key-binding ,key)
                                       (key-binding (kbd "TAB")))
                                 (key-binding ,key))))
           (condition-case nil
               (call-interactively original-func)
             (error nil)))))))

;;;;; Normalize regexps

;; from http://emacswiki.org/emacs/ElispCookbook#toc6
(defun outshine-chomp (str)
  "Chomp leading and trailing whitespace from STR."
  (save-excursion
    (save-match-data
      (while (string-match
              "\\`\n+\\|^\\s-+\\|\\s-+$\\|\n+\\'"
              str)
        (setq str (replace-match "" t t str)))
      str)))

(defun outshine-set-outline-regexp-base ()
  "Return the actual outline-regexp-base."
  (if (and
       (not (outshine-modern-header-style-in-elisp-p))
       (eq major-mode 'emacs-lisp-mode))
      (progn
        (setq outshine-enforce-no-comment-padding-p t)
        (setq outshine-outline-regexp-base
              outshine-oldschool-elisp-outline-regexp-base))
    (setq outshine-enforce-no-comment-padding-p nil)
    (setq outshine-outline-regexp-base
          outshine-default-outline-regexp-base)))

(defun outshine-normalize-regexps ()
  "Chomp leading and trailing whitespace from outline regexps."
  (and comment-start
       (setq outshine-normalized-comment-start
             (if outshine-preserve-delimiter-whitespace
                 comment-start
                 (outshine-chomp comment-start))))
  (and comment-end
       (setq outshine-normalized-comment-end
             (outshine-chomp comment-end)))
  (and outshine-outline-regexp-base
       (setq outshine-normalized-outline-regexp-base
             (outshine-chomp outshine-outline-regexp-base))))

;;;;; Calculate outline-regexp and outline-level

;; dealing with special case of oldschool headers in elisp (;;;+)
(defun outshine-modern-header-style-in-elisp-p (&optional buffer)
  "Return nil, if there is no match for a outshine-style header.
Searches in BUFFER if given, otherwise in current buffer."
  (let ((buf (or buffer (current-buffer))))
    (with-current-buffer buf
      (save-excursion
        (goto-char (point-min))
        (re-search-forward
         ;; (format "^;; [%s]+ " outshine-regexp-base-char)
         (format "^;; [%s]\\{1,%d\\} "
                 outshine-regexp-base-char outshine-max-level)
         nil 'NOERROR)))))

(defun outshine-calc-comment-region-starter ()
  "Return comment-region starter as string.
Based on `comment-start' and `comment-add'."
  (if (or (not comment-add) (eq comment-add 0))
      outshine-normalized-comment-start
    (let ((comment-add-string outshine-normalized-comment-start))
      (dotimes (i comment-add comment-add-string)
        (setq comment-add-string
              (concat comment-add-string outshine-normalized-comment-start))))))

(defun outshine-calc-comment-padding ()
  "Return comment-padding as string"
  (cond
   ;; comment-padding is nil
   ((not comment-padding) " ")
   ;; comment-padding is integer
   ((integer-or-marker-p comment-padding)
    (let ((comment-padding-string ""))
      (dotimes (i comment-padding comment-padding-string)
        (setq comment-padding-string
              (concat comment-padding-string " ")))))
   ;; comment-padding is string
   ((stringp comment-padding)
    comment-padding)
   (t (error "No valid comment-padding"))))

(defun outshine-calc-outline-regexp ()
  "Calculate the outline regexp for the current mode."
  (concat
   (and outshine-outline-regexp-outcommented-p
         ;; regexp-base outcommented, but no 'comment-start' defined
         (or comment-start
             (message (concat
                       "Cannot calculate outcommented outline-regexp\n"
                       "without 'comment-start' character defined!")))
         (concat
          ;; comment-start
          ;; (outshine-calc-comment-region-starter)
          (regexp-quote
           (outshine-calc-comment-region-starter))
          ;; comment-padding
          (if outshine-enforce-no-comment-padding-p
              ""
            (outshine-calc-comment-padding))))
   ;; regexp-base
   outshine-normalized-outline-regexp-base
   " "))

;; TODO how is this called (match-data?) 'looking-at' necessary?
(defun outshine-calc-outline-level ()
  "Calculate the right outline level for the
  outshine-outline-regexp"
  (save-excursion
    (save-match-data
      (and
       (looking-at (outshine-calc-outline-regexp))
       ;; ;; FIXME this works?
       ;; (looking-at outline-regexp)
       (let ((m-strg (match-string-no-properties 0)))
         (if outshine-enforce-no-comment-padding-p
             ;; deal with oldschool elisp headings (;;;+)
             (setq m-strg
                   (split-string
                    (substring m-strg 2)
                    nil
                    'OMIT-NULLS))
           ;; orgmode style elisp heading (;; *+)
           (setq m-strg
                 (split-string
                  m-strg
                  (format "%s" outshine-normalized-comment-start)
                  'OMIT-NULLS)))
         (length
          (mapconcat
           (lambda (str)
             (car
              (split-string
               str
               " "
               'OMIT-NULLS)))
           m-strg
           "")))
       ))))

;;;;; Set outline-regexp und outline-level

(defun outshine-set-local-outline-regexp-and-level
  (start-regexp &optional fun end-regexp)
   "Set `outline-regexp' locally to START-REGEXP.
Set optionally `outline-level' to FUN and
`outline-heading-end-regexp' to END-REGEXP."
        (make-local-variable 'outline-regexp)
        (setq outline-regexp start-regexp)
        (and fun
             (make-local-variable 'outline-level)
             (setq outline-level fun))
        (and end-regexp
             (make-local-variable 'outline-heading-end-regexp)
             (setq outline-heading-end-regexp end-regexp)))

;;;;; Show number of lines in hidden body

;; Calc and show line number of hidden body for all visible headlines
(defun outshine-write-hidden-lines-cookies ()
  "Show line number of hidden lines in folded headline."
  (and outshine-show-hidden-lines-cookies-p
       (save-excursion
         (goto-char (point-min))
         (and (outline-on-heading-p)
              (outshine-hidden-lines-cookie-status-changed-p)
              (outshine-set-hidden-lines-cookie))
         (while (not (eobp))
           (outline-next-visible-heading 1)
           (and (outline-on-heading-p)
                (outshine-hidden-lines-cookie-status-changed-p)
                (outshine-set-hidden-lines-cookie))))))

(defun outshine-hidden-lines-cookie-status-changed-p ()
  "Return non-nil if hidden-lines cookie needs modification."
  (save-excursion
    (save-match-data
      (or (not (outline-body-visible-p))
          (re-search-forward
           outshine-hidden-lines-cookie-format-regexp
           (line-end-position)
           'NO-ERROR)))))

(defun outshine-set-hidden-lines-cookie ()
  "Calculate and set number of hidden lines in folded headline."
  (let* ((folded-p (not (outline-body-visible-p)))
         (line-num-current-header (line-number-at-pos))
         (line-num-next-visible-header
          (save-excursion
            (outline-next-visible-heading 1)
            (line-number-at-pos)))
         (body-lines
          (1- (- line-num-next-visible-header line-num-current-header))))
    (if (re-search-forward
         outshine-hidden-lines-cookie-format-regexp
         (line-end-position)
         'NO-ERROR)
        (cond
         ((not folded-p) (replace-match ""))
         (folded-p (replace-match (format "%s" body-lines) nil nil nil 2)))
      (show-entry)
      (save-excursion
        (end-of-line)
        (insert
         (format
          " %s%s%s%s%s"
          outshine-hidden-lines-cookie-left-delimiter
          outshine-hidden-lines-cookie-left-signal-char
          body-lines
          outshine-hidden-lines-cookie-right-signal-char
          outshine-hidden-lines-cookie-right-delimiter)))
      (hide-entry))))

;; ;; FIXME
;; ;; outline-flag-region: Variable binding depth exceeds max-specpdl-size
;; (add-hook 'outline-view-change-hook
;;           'outshine-write-hidden-lines-cookies)

;;;;; Return outline-string at given level

(defun outshine-calc-outline-string-at-level (level)
  "Return outline-string at level LEVEL."
  (let ((base-string (outshine-calc-outline-base-string-at-level level)))
    (if (not outshine-outline-regexp-outcommented-p)
        base-string
      (concat (outshine-calc-comment-region-starter)
              (if outshine-enforce-no-comment-padding-p
                  ""
                (outshine-calc-comment-padding))
              base-string
              " "))))

(defun outshine-calc-outline-base-string-at-level (level)
  "Return outline-base-string at level LEVEL."
  (let* ((star (outshine-transform-normalized-outline-regexp-base-to-string))
         (stars star))
       (dotimes (i (1- level) stars)
         (setq stars (concat stars star)))))

(defun outshine-transform-normalized-outline-regexp-base-to-string ()
  "Transform 'outline-regexp-base' to string by stripping off special chars."
  (replace-regexp-in-string
   outshine-outline-regexp-special-chars
   ""
   outshine-normalized-outline-regexp-base))

;; make demote/promote from `outline-magic' work
(defun outshine-make-promotion-headings-list (max-level)
  "Make a sorted list of headings used for promotion/demotion commands.
Set this to a list of MAX-LEVEL headings as they are matched by `outline-regexp',
top-level heading first."
  (let ((list-of-heading-levels
         `((,(outshine-calc-outline-string-at-level 1) . 1))))
    (dotimes (i (1- max-level) list-of-heading-levels)
            (add-to-list
             'list-of-heading-levels
             `(,(outshine-calc-outline-string-at-level (+ i 2)) . ,(+ i 2))
             'APPEND))))

;;;;; Fontify the headlines

(defsubst outshine-font-lock-flush ()
  "Calls `font-lock-flush' or equivalent.
Compatibility with Emacs versions <25."
  (if (fboundp #'font-lock-flush)
      (font-lock-flush)
    ;; Copied from Emacs 25 font-lock.el, changed to call
    ;; `jit-lock-refontify' directly
    (and font-lock-mode
         font-lock-fontified
         (jit-lock-refontify))))

(defun outshine-fontify-headlines (outline-regexp)
  "Calculate heading regexps for font-lock mode."
  (let* ((outline-rgxp (substring outline-regexp 0 -8))
         (heading-1-regexp
         (format "%s%s%s%s"
                 outline-rgxp
                 "\\{1\\} \\(.*"
                 (if outshine-fontify-whole-heading-line "\n?" "")
                 "\\)"))
        (heading-2-regexp
         (format "%s%s%s%s"
                 outline-rgxp
                 "\\{2\\} \\(.*"
                 (if outshine-fontify-whole-heading-line "\n?" "")
                 "\\)"))
        (heading-3-regexp
         (format "%s%s%s%s"
                 outline-rgxp
                 "\\{3\\} \\(.*"
                 (if outshine-fontify-whole-heading-line "\n?" "")
                 "\\)"))
        (heading-4-regexp
         (format "%s%s%s%s"
                 outline-rgxp
                 "\\{4\\} \\(.*"
                 (if outshine-fontify-whole-heading-line "\n?" "")
                 "\\)"))
        (heading-5-regexp
         (format "%s%s%s%s"
                 outline-rgxp
                 "\\{5\\} \\(.*"
                 (if outshine-fontify-whole-heading-line "\n?" "")
                 "\\)"))
        (heading-6-regexp
         (format "%s%s%s%s"
                 outline-rgxp
                 "\\{6\\} \\(.*"
                 (if outshine-fontify-whole-heading-line "\n?" "")
                 "\\)"))
        (heading-7-regexp
         (format "%s%s%s%s"
                 outline-rgxp
                 "\\{7\\} \\(.*"
                 (if outshine-fontify-whole-heading-line "\n?" "")
                 "\\)"))
        (heading-8-regexp
         (format "%s%s%s%s"
                 outline-rgxp
                 "\\{8\\} \\(.*"
                 (if outshine-fontify-whole-heading-line "\n?" "")
                 "\\)")))
    (font-lock-add-keywords
     nil
     `((,heading-1-regexp 1 'outshine-level-1 t)
       (,heading-2-regexp 1 'outshine-level-2 t)
       (,heading-3-regexp 1 'outshine-level-3 t)
       (,heading-4-regexp 1 'outshine-level-4 t)
       (,heading-5-regexp 1 'outshine-level-5 t)
       (,heading-6-regexp 1 'outshine-level-6 t)
       (,heading-7-regexp 1 'outshine-level-7 t)
       (,heading-8-regexp 1 'outshine-level-8 t)))
    (outshine-font-lock-flush)))


;;;;; Functions for speed-commands

;; copied and modified from org-mode.el
(defun outshine-print-speed-command (e)
  (if (> (length (car e)) 1)
      (progn
        (princ "\n")
        (princ (car e))
        (princ "\n")
        (princ (make-string (length (car e)) ?-))
        (princ "\n"))
    (princ (car e))
    (princ "   ")
    (if (symbolp (cdr e))
        (princ (symbol-name (cdr e)))
      (prin1 (cdr e)))
    (princ "\n")))

(defun outshine-speed-command-activate (keys)
  "Hook for activating single-letter speed commands.
`outshine-speed-commands-default' specifies a minimal command set.
Use `outshine-speed-commands-user' for further customization."
  (when (or (and
             (bolp)
             (looking-at outline-regexp))
             ;; (looking-at (outshine-calc-outline-regexp)))
            (and
             (functionp outshine-use-speed-commands)
             (funcall outshine-use-speed-commands)))
    (cdr (assoc keys (append outshine-speed-commands-user
                             outshine-speed-commands-default)))))


(defun outshine-defkey (keymap key def)
  "Define a KEY in a KEYMAP with definition DEF."
  (define-key keymap key def))

(defun outshine-remap (map &rest commands)
  "In MAP, remap the functions given in COMMANDS.
COMMANDS is a list of alternating OLDDEF NEWDEF command names."
  (let (new old)
    (while commands
      (setq old (pop commands) new (pop commands))
      (if (fboundp 'command-remapping)
          (outshine-defkey map (vector 'remap old) new)
        (substitute-key-definition old new map global-map)))))

(outshine-remap outline-minor-mode-map
             'self-insert-command 'outshine-self-insert-command)

;;;;; Functions for hiding comment-subtrees

(defun outshine-hide-comment-subtrees-in-region (beg end)
  "Re-hide all comment subtrees after a visibility state change."
  (save-excursion
    (let* ((re (concat ":" outshine-comment-tag ":")))
      (goto-char beg)
      (while (re-search-forward re end t)
        (when (outline-on-heading-p t)
          (outshine-flag-subtree t)
          (outline-end-of-subtree))))))

(defun outshine-flag-subtree (flag)
  (save-excursion
    (outline-back-to-heading t)
    (outline-end-of-heading)
    (outline-flag-region (point)
                         (progn (outline-end-of-subtree) (point))
                         flag)))

(defun outshine-hide-comment-subtrees ()
  "Re-hide all comment subtrees after a visibility state change."
  (let ((state outshine-current-buffer-visibility-state))
  (when (and (not outshine-open-comment-trees)
             (not (memq state '(overview folded))))
    (save-excursion
      (let* ((globalp (memq state '(contents all)))
             (beg (if globalp (point-min) (point)))
             (end (if globalp (point-max)
                    (outline-end-of-subtree))))
        (outshine-hide-comment-subtrees-in-region beg end)
        (goto-char beg)
        (if (looking-at (concat ".*:" outshine-comment-tag ":"))
            (message "%s" (substitute-command-keys
                           "Subtree is tagged as comment and
                           stays closed. Use
                           \\[outshine-force-cycle-comment] to
                           cycle it anyway."))))))))

;; ;; FIXME max-lisp-eval-depth exceeded error when turned on
;; ;; with max-lisp-eval-depth set to 600
;; (add-hook 'outline-view-change-hook
;; 	  'outshine-hide-comment-subtrees)


;;;;; Use outorg functions

;; (defun outshine-pt-rgxps ()
;;   "Return list with 5 regexps, like (rgx0 rgx1 rgx2 rgx3 rgx4).

;; These regexps, if non-nil, match
;;  - rgx0 :: buffer-substring from bol to point
;;  - rgx1 :: buffer-substring from bol of previous line to point
;;  - rgx2 :: buffer-substring from bol of second previous line to point
;;  - rgx3 :: buffer-substring from bol of third previous line to point
;;  - rgx4 :: buffer-substring from bol of fourth previous line to point"
;;   (let ((cur-buf (current-buffer))
;;         (buf-mode major-mode)
;;         beg end rgx0 rgx1 rgx2 rgx3 rgx4)
;;     (save-excursion
;;       (save-restriction
;;         (widen)
;;         (setq end (point))
;;         (save-excursion
;;           (setq beg (outline-previous-heading)))
;;         (with-temp-buffer
;;           (insert-buffer-substring-no-properties
;;            cur-buf beg end)
;;           (funcall `,buf-mode)
;;           (save-excursion
;;             (uncomment-region (point-min) (point-max)))
;;           (let ((pt (1- (point-max))))
;;             (setq rgx0
;;                   (regexp-opt
;;                    (list
;;                     (buffer-substring-no-properties
;;                      (point-at-bol) pt))))
;;             (when (= (save-excursion (forward-line -1)) 0)
;;               (setq rgx1
;;                     (regexp-opt
;;                      (list
;;                       (buffer-substring-no-properties
;;                        (save-excursion (forward-line -1) (point))
;;                        pt)))))
;;             (when (= (save-excursion (forward-line -2)) 0)
;;               (setq rgx2
;;                     (regexp-opt
;;                      (list
;;                       (buffer-substring-no-properties
;;                        (save-excursion (forward-line -2) (point))
;;                        pt)))))
;;             (when (= (save-excursion (forward-line -3)) 0)
;;               (setq rgx3
;;                     (regexp-opt
;;                      (list
;;                       (buffer-substring-no-properties
;;                        (save-excursion (forward-line -3) (point))
;;                        pt)))))
;;             (when (= (save-excursion (forward-line -4)) 0)
;;               (setq rgx4
;;                     (regexp-opt
;;                      (list
;;                       (buffer-substring-no-properties
;;                        (save-excursion (forward-line -4) (point))
;;                        pt)))))))
;;         (list rgx4 rgx3 rgx2 rgx1 rgx0)))))

(defun outshine-comment-region (beg end &optional arg)
       "Use comment-style that always inserts at BOL.
Call `comment-region' with a comment-style that guarantees
   insertion of comment-start markers at beginning-of-line."
       (interactive "r")
       (let ((comment-style
              (if (member comment-style '(indent-or-triple indent))
                  'plain
                comment-style)))
         (comment-region beg end arg)))

(defun outshine-get-outorg-edit-buffer-content (&optional buf-or-file)
  "Get content of buffer `outorg-edit-buffer-name.'
Use current buffer for conversion, unless BUF-OR-FILE is given."
  (let (buf-strg)
    (with-current-buffer
	(cond
	 ((ignore-errors (file-exists-p buf-or-file))
	  (find-file-noselect buf-or-file))
	 ((ignore-errors (get-buffer buf-or-file))
	  buf-or-file)
	 (t (current-buffer)))
      (outshine-use-outorg
       (lambda ()
	 (interactive)
	 (setq buf-strg
	       (buffer-substring-no-properties
		(point-min) (point-max))))
       'WHOLE-BUFFER-P))
    buf-strg))

;; courtesy of Pascal Bourguignon
(defun outshine-use-outorg-finish-store-log-note ()
  "Finish store-log-note and exit recursive edit"
  (message "...entering outorg-finish-function")
  (setq outorg-org-finish-function-called-p t)
  (org-store-log-note)
  (outorg-copy-edits-and-exit))
  ;; (exit-recursive-edit))

(defun outshine-use-outorg (fun &optional whole-buffer-p &rest funargs)
  "Use outorg to call FUN with FUNARGS on subtree or thing at point.

FUN should be an Org-mode function that acts on the subtree or
org-element at point. Optionally, with WHOLE-BUFFER-P non-nil,
`outorg-edit-as-org' can be called on the whole buffer.

Sets the variable `outshine-use-outorg-last-headline-marker' so
that it always contains a point-marker to the last headline this
function was called upon."
  (save-excursion
    (unless (outline-on-heading-p)
      (or (outline-previous-heading)
	  (outline-next-heading)))
    (move-marker outshine-use-outorg-last-headline-marker (point)))
  (if whole-buffer-p
      (outorg-edit-as-org '(4))
    (outorg-edit-as-org))
  (setq outorg-called-via-outshine-use-outorg-p t)
  (goto-char outorg-edit-buffer-point-marker)
  (if funargs
      (apply fun funargs)
    (call-interactively fun))
  (outorg-copy-edits-and-exit))

;;;;; Hook function

;;;###autoload
(defun outshine-hook-function ()
  "Add this function to outline-minor-mode-hook"
  (outshine-set-outline-regexp-base)
  (outshine-normalize-regexps)
  (let ((out-regexp (outshine-calc-outline-regexp)))
    (outshine-set-local-outline-regexp-and-level
     out-regexp
     'outshine-calc-outline-level
     outshine-outline-heading-end-regexp)
    (setq outline-promotion-headings
          (outshine-make-promotion-headings-list 8))
    ;; imenu preparation
    (and outshine-imenu-show-headlines-p
         (set (make-local-variable
               'outshine-imenu-preliminary-generic-expression)
               `((nil ,(concat out-regexp "\\(.*$\\)") 1)))
	 (if imenu-generic-expression
	     (add-to-list 'imenu-generic-expression
                          (car outshine-imenu-preliminary-generic-expression))
           (setq imenu-generic-expression
                 outshine-imenu-preliminary-generic-expression)))
    (when outshine-startup-folded-p
      (condition-case error-data
          (outline-hide-sublevels 1)
        ('error (message "No outline structure detected"))))
    (when (pcase outshine-fontify
            (`t t)
            (`nil nil)
            ((pred functionp) (funcall outshine-fontify))
            (_ (user-error "Invalid value for variable `outshine-fontify'")))
      (outshine-fontify-headlines out-regexp))))

;; ;; add this to your .emacs
;; (add-hook 'outline-minor-mode-hook 'outshine-hook-function)

;;;;; Additional outline functions
;;;;;; Functions from `outline-magic'

(defun outline-cycle-emulate-tab ()
  "Check if TAB should be emulated at the current position."
  ;; This is called after the check for point in a headline,
  ;; so we can assume we are not in a headline
  (if (and (eq outline-cycle-emulate-tab 'white)
           (save-excursion
             (beginning-of-line 1) (looking-at "[ \t]+$")))
      t
    outline-cycle-emulate-tab))

(defun outline-change-level (delta)
  "Workhorse for `outline-demote' and `outline-promote'."
  (let* ((headlist (outline-headings-list))
         (atom (outline-headings-atom headlist))
         (re (concat "^" outline-regexp))
         (transmode (and transient-mark-mode mark-active))
         beg end)

    ;; Find the boundaries for this operation
    (save-excursion
      (if transmode
          (setq beg (min (point) (mark))
                end (max (point) (mark)))
        (outline-back-to-heading)
        (setq beg (point))
        (outline-end-of-heading)
        (outline-end-of-subtree)
        (setq end (point)))
      (setq beg (move-marker (make-marker) beg)
            end (move-marker (make-marker) end))

      (let (head newhead level newlevel static)

        ;; First a dry run to test if there is any trouble ahead.
        (goto-char beg)
        (while (re-search-forward re end t)
          (outline-change-heading headlist delta atom 'test))

        ;; Now really do replace the headings
        (goto-char beg)
        (while (re-search-forward re end t)
          (outline-change-heading headlist delta atom))))))

(defun outline-headings-list ()
  "Return a list of relevant headings, either a user/mode defined
list, or an alist derived from scanning the buffer."
  (let (headlist)
    (cond
     (outline-promotion-headings
      ;; configured by the user or the mode
      (setq headlist outline-promotion-headings))

     ((and (eq major-mode 'outline-mode) (string= outline-regexp "[*\^L]+"))
      ;; default outline mode with original regexp
      ;; this need special treatment because of the \f in the regexp
      (setq headlist '(("*" . 1) ("**" . 2))))  ; will be extrapolated

     (t ;; Check if the buffer contains a complete set of headings
      (let ((re (concat "^" outline-regexp)) head level)
        (save-excursion
          (goto-char (point-min))
          (while (re-search-forward re nil t)
            (save-excursion
              (beginning-of-line 1)
              (setq head (outline-cleanup-match (match-string 0))
                    level (funcall outline-level))
              (add-to-list  'headlist (cons head level))))))
      ;; Check for uniqueness of levels in the list
      (let* ((hl headlist) entry level seen nonunique)
        (while (setq entry (car hl))
          (setq hl (cdr hl)
                level (cdr entry))
          (if (and (not (outline-static-level-p level))
                   (member level seen))
              ;; We have two entries for the same level.
              (add-to-list 'nonunique level))
          (add-to-list 'seen level))
        (if nonunique
            (error "Cannot promote/demote: non-unique headings at level %s\nYou may want to configure `outline-promotion-headings'."
                   (mapconcat 'int-to-string nonunique ","))))))
    ;; OK, return the list
    headlist))

(defun outline-change-heading (headlist delta atom &optional test)
  "Change heading just matched by `outline-regexp' by DELTA levels.
HEADLIST can be either an alist ((\"outline-match\" . level)...) or a
straight list like `outline-promotion-headings'. ATOM is a character
if all headlines are composed of a single character.
If TEST is non-nil, just prepare the change and error if there are problems.
TEST nil means, really replace old heading with new one."
  (let* ((head (outline-cleanup-match (match-string 0)))
         (level (save-excursion
                  (beginning-of-line 1)
                  (funcall outline-level)))
         (newhead  ; compute the new head
          (cond
           ((= delta 0) t)
           ((outline-static-level-p level) t)
           ((null headlist) nil)
           ((consp (car headlist))
            ;; The headlist is an association list
            (or (car (rassoc (+ delta level) headlist))
                (and atom
                     (> (+ delta level) 0)
                     (make-string (+ delta level) atom))))
           (t
            ;; The headlist is a straight list - grab the correct element.
            (let* ((l (length headlist))
                   (n1 (- l (length (member head headlist)))) ; index old
                   (n2 (+ delta n1)))                         ; index new
              ;; Careful checking
              (cond
               ((= n1 l) nil)                ; head not found
               ((< n2 0) nil)                ; newlevel too low
               ((>= n2 l) nil)               ; newlevel too high
               ((let* ((tail (nthcdr (min n1 n2) headlist))
                       (nilpos (- (length tail) (length (memq nil tail)))))
                  (< nilpos delta))          ; nil element between old and new
                nil)
               (t (nth n2 headlist))))))))      ; OK, we have a match!
    (if (not newhead)
        (error "Cannot shift level %d heading \"%s\" to level %d"
               level head (+ level delta)))
    (if (and (not test) (stringp newhead))
        (save-excursion
          (beginning-of-line 1)
          (or (looking-at (concat "[ \t]*\\(" (regexp-quote head) "\\)"))
              (error "Please contact maintainer"))
          (replace-match (outline-cleanup-match newhead) t t nil 1)))))

(defun outline-headings-atom (headlist)
  "Use the list created by `outline-headings-list' and check if all
headings are polymers of a single character, e.g. \"*\".
If yes, return this character."
  (if (consp (car headlist))
      ;; this is an alist - it makes sense to check for atomic structure
      (let ((re (concat "\\`"
                        (regexp-quote (substring (car (car headlist)) 0 1))
                        "+\\'")))
        (if (not (delq nil (mapcar (lambda (x) (not (string-match re (car x))))
                                   headlist)))
            (string-to-char (car (car headlist)))))))

(defun outline-cleanup-match (s)
  "Remove text properties and start/end whitespace from a string."
  (set-text-properties 1 (length s) nil s)
  (save-match-data
    (if (string-match "^[ \t]+" s) (setq s (replace-match "" t t s)))
    (if (string-match "[ \t]+$" s) (setq s (replace-match "" t t s))))
  s)

(defun outline-static-level-p (level)
  "Test if a level should not be changed by level promotion/demotion."
  (>= level 1000))

;;;;; Special Case Latex-Mode

;; (defun outshine-get-latex-documentclass (&optional buf-or-name no-check-p)
;;   "Return latex document class of current-buffer.
;; If BUF-OR-NAME is non-nil, use it instead of current buffer. If
;; NO-CHECK-P is non-nil, assume BUF-OR-NAME is ok (i.e. live and in
;; latex-mode) and just use it."
;;   (catch 'exit
;;   (let ((buf (cond
;; 	      ((and buf-or-name no-check-p) buf-or-name)
;; 	      ((and buf-or-name
;; 		    (buffer-live-p buf-or-name)
;; 		    (with-current-buffer buf-or-name
;; 		      (eq major-mode 'latex-mode)))
;; 	       buf-or-name)
;; 	      ((eq major-mode 'latex-mode) (current-buffer))
;; 	      (t (throw 'exit nil)))))
;;     (with-current-buffer buf
;;       (save-excursion
;; 	(save-restriction
;; 	  (widen)
;; 	  (goto-char (point-min))
;; 	  (re-search-forward outshine-latex-documentclass-regexp
;; 			     nil 'NOERROR 1)
;; 	  (org-no-properties (match-string 1))))))))

;;;;; Agenda Functions

;; (defun outshine-agenda-create-temporary-agenda-file (&optional restriction-lock buf-or-name pos)
;;   "Create a single temporary outshine agenda file.

;; Concatenate all `outshine-agenda-files', after converting them to
;; Org-mode, into a single Org file in the
;; `outshine-temporary-directory'. Return that file's
;; buffer-file-name.

;; When uncommenting this section, `outshine-temporary-directory' needs to be uncommented as well
;; If this section is removed, please remove `outshine-temporary-directory' as well

;; When RESTRICTION-LOCK is given, act conditional on its value:

;;  - file :: (symbol) restrict to buffer

;;  - t :: (any) restrict to subtree

;; Use current-buffer and point position, unless BUF-OR-NAME and/or
;; POS are non-nil."
;;   (let* ((temporary-file-directory outshine-temporary-directory)
;; 	 (curr-agenda-file (make-temp-file "outshine-" nil ".org"))
;; 	 (buf (if (and buf-or-name (buffer-file-name buf-or-name))
;; 		  buf-or-name
;; 		(current-buffer)))
;; 	 (pos (if (and pos (integer-or-marker-p pos)
;; 		       (<= pos (buffer-size buf)))
;; 		  pos
;; 		(point))))
;;     (with-current-buffer (find-file-noselect curr-agenda-file)
;;       (cond
;;        ((eq restriction-lock 'file)
;; 	(insert
;; 	 (with-current-buffer buf
;; 	   (outshine-get-outorg-edit-buffer-content))))
;;        (restriction-lock
;; 	(insert
;; 	 (with-current-buffer buf
;; 	   (save-excursion
;; 	     (goto-char pos)
;; 	     (save-restriction
;; 	       (outshine-narrow-to-subtree)
;; 	       (outshine-get-outorg-edit-buffer-content))))))
;;        (t (mapc
;; 	   (lambda (--file)
;; 	     (insert
;; 	      (outshine-get-outorg-edit-buffer-content --file))
;; 	     (forward-line 2))
;; 	   outshine-agenda-files)))
;;       (save-buffer)
;;       (kill-buffer))
;;     curr-agenda-file))

;; ;; rather obsolete - better use agenda restriction lock
;; (defun outshine-agenda-set-org-agenda-files (&rest file-lst)
;;   "Set `org-agenda-files' to FILE-LST.
;; Store old value in `outshine-agenda-old-org-agenda-files'."
;;   (setq outshine-agenda-old-org-agenda-files org-agenda-files)
;;   (setq org-agenda-files file-lst))

;; ;; rather obsolete - better use agenda restriction lock
;; (defun outshine-agenda-restore-org-agenda-files ()
;;   "Restore `org-agenda-files'.
;; The old value is stored in
;; `outshine-agenda-old-org-agenda-files'."
;;   (setq org-agenda-files outshine-agenda-old-org-agenda-files)
;;   (setq outshine-agenda-old-org-agenda-files nil))

;;;; Commands
;;;;; Additional outline commands
;;;;;; Commands from `out-xtra'

(defun outline-hide-sublevels (keep-levels)
  "Hide everything except the first KEEP-LEVEL headers."
  (interactive "p")
  (if (< keep-levels 1)
      (error "Must keep at least one level of headers"))
  (setq keep-levels (1- keep-levels))
  (save-excursion
    (goto-char (point-min))
    ;; Skip the prelude, if any.
    (unless (outline-on-heading-p t) (outline-next-heading))
    (hide-subtree)
    (show-children keep-levels)
    (condition-case err
        (while (outline-get-next-sibling)
          (hide-subtree)
          (show-children keep-levels))
      (error nil))))

(defun outline-hide-other ()
  "Hide everything except for the current body and the parent headings."
  (interactive)
  (outline-hide-sublevels 1)
  (let ((last (point))
        (pos (point)))
    (while (save-excursion
             (and (re-search-backward "[\n\r]" nil t)
                  (eq (following-char) ?\r)))
      (save-excursion
        (beginning-of-line)
        (if (eq last (point))
            (progn
              (outline-next-heading)
              (outline-flag-region last (point) ?\n))
          (show-children)
          (setq last (point)))))))

;;;;;; Commands from `outline-magic'

(defun outline-next-line ()
  "Forward line, but mover over invisible line ends.
Essentially a much simplified version of `next-line'."
  (interactive)
  (beginning-of-line 2)
  (while (and (not (eobp))
              (get-char-property (1- (point)) 'invisible))
    (beginning-of-line 2)))

(defun outline-move-subtree-up (&optional arg)
  "Move the currrent subtree up past ARG headlines of the same level."
  (interactive "p")
  (let ((headers (or arg 1)))
    (outline-move-subtree-down (- headers))))

(defun outline-move-subtree-down (&optional arg)
  "Move the currrent subtree down past ARG headlines of the same level."
  (interactive "p")
  (let* ((headers (or arg 1))
        (re (concat "^" outline-regexp))
        (movfunc (if (> headers 0) 'outline-get-next-sibling
                   'outline-get-last-sibling))
        (ins-point (make-marker))
        (cnt (abs headers))
        beg end txt)
    ;; Select the tree
    (outline-back-to-heading)
    (setq beg (point))
    (outline-end-of-subtree)
    (if (= (char-after) ?\n) (forward-char 1))
    (setq end (point))
    ;; Find insertion point, with error handling
    (goto-char beg)
    (while (> cnt 0)
      (or (funcall movfunc)
          (progn (goto-char beg)
                 (error "Cannot move past superior level")))
      (setq cnt (1- cnt)))
    (if (> headers 0)
        ;; Moving forward - still need to move over subtree
        (progn (outline-end-of-subtree)
               (if (= (char-after) ?\n) (forward-char 1))))
    (move-marker ins-point (point))
    (setq txt (buffer-substring beg end))
    (delete-region beg end)
    (insert txt)
    (goto-char ins-point)
    (move-marker ins-point nil)))

(defun outline-promote (&optional arg)
  "Decrease the level of an outline-structure by ARG levels.
When the region is active in transient-mark-mode, all headlines in the
region are changed.  Otherwise the current subtree is targeted. Note that
after each application of the command the scope of \"current subtree\"
may have changed."
  (interactive "p")
  (let ((delta (or arg 1)))
    (outline-change-level (- delta))))

(defun outline-demote (&optional arg)
  "Increase the level of an outline-structure by ARG levels.
When the region is active in transient-mark-mode, all headlines in the
region are changed.  Otherwise the current subtree is targeted. Note that
after each application of the command the scope of \"current subtree\"
may have changed."
  (interactive "p")
  (let ((delta (or arg 1)))
    (outline-change-level delta)))

(defun outline-cycle (&optional arg)
  "Visibility cycling for outline(-minor)-mode.

- When point is at the beginning of the buffer, or when called with a
  C-u prefix argument, rotate the entire buffer through 3 states:
  1. OVERVIEW: Show only top-level headlines.
  2. CONTENTS: Show all headlines of all levels, but no body text.
  3. SHOW ALL: Show everything.

- When point is at the beginning of a headline, rotate the subtree started
  by this line through 3 different states:
  1. FOLDED:   Only the main headline is shown.
  2. CHILDREN: The main headline and the direct children are shown.  From
               this state, you can move to one of the children and
               zoom in further.
  3. SUBTREE:  Show the entire subtree, including body text.

- When point is not at the beginning of a headline, execute
  `indent-relative', like TAB normally does."
  (interactive "P")
  (setq deactivate-mark t)
  (cond

   ((equal arg '(4))
    ;; Run `outline-cycle' as if at the top of the buffer.
    (let ((outshine-org-style-global-cycling-at-bob-p nil)
          (current-prefix-arg nil))
    (save-excursion
      (goto-char (point-min))
      (outline-cycle nil))))

   (t
    (cond
     ;; Beginning of buffer: Global cycling
     ((or
       ;; outline-magic style behaviour
       (and
        (bobp)
        (not outshine-org-style-global-cycling-at-bob-p))
       ;; org-mode style behaviour
       (and
        (bobp)
        (not (outline-on-heading-p))
        outshine-org-style-global-cycling-at-bob-p))
      (cond
       ((eq last-command 'outline-cycle-overview)
        ;; We just created the overview - now do table of contents
        ;; This can be slow in very large buffers, so indicate action
        (unless outshine-cycle-silently
          (message "CONTENTS..."))
        (save-excursion
          ;; Visit all headings and show their offspring
          (goto-char (point-max))
          (catch 'exit
            (while (and (progn (condition-case nil
                                   (outline-previous-visible-heading 1)
                                 (error (goto-char (point-min))))
                               t)
                        (looking-at outline-regexp))
              (show-branches)
              (if (bobp) (throw 'exit nil))))
          (unless outshine-cycle-silently
            (message "CONTENTS...done")))
        (setq
         this-command 'outline-cycle-toc
         outshine-current-buffer-visibility-state 'contents))
       ((eq last-command 'outline-cycle-toc)
        ;; We just showed the table of contents - now show everything
        (show-all)
        (unless outshine-cycle-silently
          (message "SHOW ALL"))
        (setq
         this-command 'outline-cycle-showall
         outshine-current-buffer-visibility-state 'all))
       (t
        ;; Default action: go to overview
        ;; (hide-sublevels 1)
        (let ((toplevel
               (cond
                (current-prefix-arg
                 (prefix-numeric-value current-prefix-arg))
                ((save-excursion
                   (beginning-of-line)
                   (looking-at outline-regexp))
                 (max 1 (funcall outline-level)))
                (t 1))))
          (hide-sublevels toplevel))
        (unless outshine-cycle-silently
          (message "OVERVIEW"))
        (setq
         this-command 'outline-cycle-overview
         outshine-current-buffer-visibility-state 'overview))))

     ((save-excursion (beginning-of-line 1) (looking-at outline-regexp))
      ;; At a heading: rotate between three different views
      (outline-back-to-heading)
      (let ((goal-column 0) beg eoh eol eos)
        ;; First, some boundaries
        (save-excursion
          (outline-back-to-heading)           (setq beg (point))
          (save-excursion (outline-next-line) (setq eol (point)))
          (outline-end-of-heading)            (setq eoh (point))
          (outline-end-of-subtree)            (setq eos (point)))
        ;; Find out what to do next and set `this-command'
        (cond
         ((= eos eoh)
          ;; Nothing is hidden behind this heading
          (unless outshine-cycle-silently
            (message "EMPTY ENTRY")))
         ((>= eol eos)
          ;; Entire subtree is hidden in one line: open it
          (show-entry)
          (show-children)
          (unless outshine-cycle-silently
            (message "CHILDREN"))
          (setq
           this-command 'outline-cycle-children))
           ;; outshine-current-buffer-visibility-state 'children))
         ((eq last-command 'outline-cycle-children)
          ;; We just showed the children, now show everything.
          (show-subtree)
          (unless outshine-cycle-silently
            (message "SUBTREE")))
         (t
          ;; Default action: hide the subtree.
          (hide-subtree)
          (unless outshine-cycle-silently
            (message "FOLDED"))))))

     ;; TAB emulation
     ((outline-cycle-emulate-tab)
      (indent-relative))

     (t
      ;; Not at a headline: Do indent-relative
      (outline-back-to-heading))))))

(defun outshine-cycle-buffer ()
  "Cycle the visibility state of buffer."
  (interactive)
  (outline-cycle '(4)))

(defun outshine-toggle-silent-cycling (&optional arg)
  "Toggle silent cycling between visibility states.

  When silent cycling is off, visibility state-change messages are
  written to stdout (i.e. the *Messages* buffer), otherwise these
  messages are suppressed. With prefix argument ARG, cycle silently
  if ARG is positive, otherwise write state-change messages."
  (interactive "P")
  (setq outshine-cycle-silently
        (if (null arg)
            (not outshine-cycle-silently)
          (> (prefix-numeric-value arg) 0)))
  (message "Silent visibility cycling %s"
           (if outshine-cycle-silently "enabled" "disabled")))



;;;;;; Commands from `outline-mode-easy-bindings'

;; Copied from: http://emacswiki.org/emacs/OutlineMinorMode

(defun outline-body-p ()
  (save-excursion
    (outline-back-to-heading)
    (outline-end-of-heading)
    (and (not (eobp))
         (progn (forward-char 1)
                (not (outline-on-heading-p))))))

(defun outline-body-visible-p ()
  (save-excursion
    (outline-back-to-heading)
    (outline-end-of-heading)
    (not (outline-invisible-p))))

(defun outline-subheadings-p ()
  (save-excursion
    (outline-back-to-heading)
    (let ((level (funcall outline-level)))
      (outline-next-heading)
      (and (not (eobp))
           (< level (funcall outline-level))))))

(defun outline-subheadings-visible-p ()
  (interactive)
  (save-excursion
    (outline-next-heading)
    (not (outline-invisible-p))))

(defun outline-hide-more ()
  (interactive)
  (when (outline-on-heading-p)
    (cond ((and (outline-body-p)
                (outline-body-visible-p))
           (hide-entry)
           (hide-leaves))
          (t
           (hide-subtree)))))

(defun outline-show-more ()
  (interactive)
  (when (outline-on-heading-p)
    (cond ((and (outline-subheadings-p)
                (not (outline-subheadings-visible-p)))
           (show-children))
          ((and (not (outline-subheadings-p))
                (not (outline-body-visible-p)))
           (show-subtree))
          ((and (outline-body-p)
                (not (outline-body-visible-p)))
           (show-entry))
          (t
           (show-subtree)))))

;;;;; Hidden-line-cookies commands

(defun outshine-show-hidden-lines-cookies ()
  "Show hidden-lines cookies for all visible and folded headlines."
  (interactive)
  (if outshine-show-hidden-lines-cookies-p
      (outshine-write-hidden-lines-cookies)
    (if (not (y-or-n-p "Activate hidden-lines cookies "))
        (message "Unable to show hidden-lines cookies - deactivated.")
      (outshine-toggle-hidden-lines-cookies-activation)
      (outshine-write-hidden-lines-cookies)))
  (setq outshine-hidden-lines-cookies-on-p 1))

(defun outshine-hide-hidden-lines-cookies ()
  "Delete all hidden-lines cookies."
  (interactive)
  (let* ((base-buf (point-marker))
         (indirect-buf-name
          (generate-new-buffer-name
           (buffer-name (marker-buffer base-buf)))))
    (unless outshine-show-hidden-lines-cookies-p
      (setq outshine-show-hidden-lines-cookies-p 1))
    (clone-indirect-buffer indirect-buf-name nil 'NORECORD)
    (save-excursion
      (switch-to-buffer indirect-buf-name)
      (show-all)
      (let ((indirect-buf (point-marker)))
        (outshine-write-hidden-lines-cookies)
        (switch-to-buffer (marker-buffer base-buf))
        (kill-buffer (marker-buffer indirect-buf))
        (set-marker indirect-buf nil))
      (set-marker base-buf nil)))
  (setq outshine-hidden-lines-cookies-on-p nil))

(defun outshine-toggle-hidden-lines-cookies-activation ()
  "Toggles activation of hidden-lines cookies."
  (interactive)
  (if outshine-show-hidden-lines-cookies-p
      (progn
        (setq outshine-show-hidden-lines-cookies-p nil)
        (setq outshine-hidden-lines-cookies-on-p nil)
        (message "hidden-lines cookies are deactivated now"))
    (setq outshine-show-hidden-lines-cookies-p 1)
    (message "hidden-lines cookies are activated now")))

(defun outshine-toggle-hidden-lines-cookies ()
  "Toggles status of hidden-lines cookies between shown and hidden."
  (interactive)
  (if outshine-hidden-lines-cookies-on-p
      (outshine-hide-hidden-lines-cookies)
    (outshine-show-hidden-lines-cookies)))

;;;;; Hide comment-subtrees

(defun outshine-insert-comment-subtree (&optional arg)
  "Insert new subtree that is tagged as comment."
    (interactive "P")
    (outshine-insert-heading)
    (save-excursion
      (insert
       (concat "  :" outshine-comment-tag ":"))))

(defun outshine-toggle-subtree-comment-status (&optional arg)
  "Tag (or untag) subtree at point with `outshine-comment-tag'.

Unless point is on a heading, this function acts on the previous
visible heading when ARG is non-nil, otherwise on the previous
heading."
  (interactive "P")
  (let* ((com-end-p
          (and
           outshine-normalized-comment-end
           (> (length outshine-normalized-comment-end) 0)))
         (comtag (concat ":" outshine-comment-tag ":"))
         (comtag-rgxp
          (if com-end-p
              (concat comtag
                      " *"
                      (regexp-quote
                       outshine-normalized-comment-end)
                      " *")
            (concat comtag " *"))))
    (unless (outline-on-heading-p)
      (if arg
          (outline-previous-visible-heading 1)
        (outline-previous-heading)))
    (end-of-line)
    (cond
     ((looking-back comtag-rgxp)
      (let ((start (match-beginning 0)))
        (delete-region (1- start) (+ start (length comtag)))))
     ((and com-end-p
           (looking-back
            (concat
             (regexp-quote outshine-normalized-comment-end) " *")))
      (goto-char (match-beginning 0))
       (if (looking-back " ")
           (insert (concat comtag " "))
         (insert (concat " " comtag))))
     (t (if (looking-back " ")
          (insert comtag)
         (insert (concat " " comtag)))))))

;; Cycle comment subtrees anyway
(defun outshine-force-cycle-comment ()
  "Cycle subtree even if it comment."
  (interactive)
  (setq this-command 'outline-cycle)
  (let ((outshine-open-comment-trees t))
    (call-interactively 'outline-cycle)))

;;;;; Speed commands

(defun outshine-speed-command-help ()
  "Show the available speed commands."
  (interactive)
  (if (not outshine-use-speed-commands)
      (user-error "Speed commands are not activated, customize `outshine-use-speed-commands'")
    (with-output-to-temp-buffer "*Help*"
      (princ "User-defined Speed commands\n===========================\n")
      (mapc 'outshine-print-speed-command outshine-speed-commands-user)
      (princ "\n")
      (princ "Built-in Speed commands\n=======================\n")
      (mapc 'outshine-print-speed-command outshine-speed-commands-default))
    (with-current-buffer "*Help*"
      (setq truncate-lines t))))

(defun outshine-speed-move-safe (cmd)
  "Execute CMD, but make sure that the cursor always ends up in a headline.
If not, return to the original position and throw an error."
  (interactive)
  (let ((pos (point)))
    (call-interactively cmd)
    (unless (and (bolp) (outline-on-heading-p))
      (goto-char pos)
      (error "Boundary reached while executing %s" cmd))))


(defun outshine-self-insert-command (N)
  "Like `self-insert-command', use overwrite-mode for whitespace in tables.
If the cursor is in a table looking at whitespace, the whitespace is
overwritten, and the table is not marked as requiring realignment."
  (interactive "p")
  ;; (outshine-check-before-invisible-edit 'insert)
  (cond
   ((and outshine-use-speed-commands
	 (let ((kv (this-command-keys-vector)))
	   (setq outshine-speed-command
		 (run-hook-with-args-until-success
		  'outshine-speed-command-hook
		  (make-string 1 (aref kv (1- (length kv))))))))
    ;; (setq outshine-speed-command
    ;;       (run-hook-with-args-until-success
    ;;        'outshine-speed-command-hook
    ;; 	(this-command-keys)))
    (cond
     ((commandp outshine-speed-command)
      (setq this-command outshine-speed-command)
      (call-interactively outshine-speed-command))
     ((functionp outshine-speed-command)
      (funcall outshine-speed-command))
     ((and outshine-speed-command (listp outshine-speed-command))
      (eval outshine-speed-command))
     (t (let (outshine-use-speed-commands)
          (call-interactively 'outshine-self-insert-command)))))
   (t
    (self-insert-command N)
    (if outshine-self-insert-cluster-for-undo
        (if (not (eq last-command 'outshine-self-insert-command))
            (setq outshine-self-insert-command-undo-counter 1)
          (if (>= outshine-self-insert-command-undo-counter 20)
              (setq outshine-self-insert-command-undo-counter 1)
            (and (> outshine-self-insert-command-undo-counter 0)
                 buffer-undo-list (listp buffer-undo-list)
                 (not (cadr buffer-undo-list)) ; remove nil entry
                 (setcdr buffer-undo-list (cddr buffer-undo-list)))
            (setq outshine-self-insert-command-undo-counter
                  (1+ outshine-self-insert-command-undo-counter))))))))

;; comply with `delete-selection-mode' and `electric-pair-mode'
(put 'outshine-self-insert-command 'delete-selection
     (lambda ()
       (not (run-hook-with-args-until-success
             'self-insert-uses-region-functions))))

;; trigger company idle completion like namesake command
(put 'outshine-self-insert-command 'company-begin t)

;; trigger eldoc (elisp help in echo area), like `self-insert-command'
(with-eval-after-load 'eldoc
  (eldoc-add-command 'outshine-self-insert-command))

;;;;; Other Commands

(defun outshine-eval-lisp-subtree ()
  "Mark subtree at point and call `eval-region' on it."
  (interactive)
  (save-excursion
    (outline-mark-subtree)
    (call-interactively 'eval-region)))

(defun outshine-comment-subtree-content ()
  "Mark subtree at point and call `comment-dwim' on its content."
  (interactive)
  (save-excursion
    (outline-mark-subtree)
    (forward-line)
    (call-interactively 'comment-dwim)))

(defun outshine-narrow-to-subtree ()
  "Narrow buffer to subtree at point."
  (interactive)
  (if (outline-on-heading-p)
      (progn
        (outline-mark-subtree)
        (and
         (use-region-p)
         (narrow-to-region (region-beginning) (region-end)))
        (deactivate-mark))
    (message "Not at headline, cannot narrow to subtree")))

(defun outshine-navi ()
  "Open or reuse *Navi* buffer for fast navigation.

Switch to associated read-only *Navi* buffer for fast and
convenient buffer navigation without changing visibility state of
original buffer. Type 'o' (M-x navi-goto-occurrence-other-window)
to switch from the new position in the *Navi* buffer to the same
position in the original buffer.

This function is the outshine replacement for `org-goto'."
  (interactive)
  (if (require 'navi-mode nil t)
      (navi-search-and-switch)
    (message "Install navi-mode.el for this command to work")))

;;;;; Overridden outline commands

;; overriding 'outline-insert-heading'
;; copied and adapted form outline.el, taking into account modes
;; with 'comment-end' defined (as non-empty string).
(defun outshine-insert-heading ()
  "Insert a new heading at same depth at point.
This function takes `comment-end' into account."
  (interactive)
  (let* ((head-with-prop
          (save-excursion
            (condition-case nil
                (outline-back-to-heading)
              (error (outline-next-heading)))
            (if (eobp)
                (or (caar outline-heading-alist) "")
              (match-string 0))))
         (head (substring-no-properties head-with-prop))
         (com-end-p))
    (unless (or (string-match "[ \t]\\'" head)
                (not (string-match (concat "\\`\\(?:" outline-regexp "\\)")
                                   (concat head " "))))
      (setq head (concat head " ")))
    (unless (or (not comment-end) (string-equal "" comment-end))
      (setq head (concat head " " outshine-normalized-comment-end))
      (setq com-end-p t))
    (unless (bolp) (end-of-line) (newline))
    (insert head)
    (unless (eolp)
      (save-excursion (newline-and-indent)))
    (and com-end-p
         (re-search-backward outshine-normalized-comment-end)
         (forward-char -1))
    (run-hooks 'outline-insert-heading-hook)))

;;;;; iMenu and idoMenu Support

(defun outshine-imenu-with-navi-regexp
  (kbd-key &optional PREFER-IMENU-P LAST-PARENTH-EXPR-P)
  "Enhanced iMenu/idoMenu support depending on `navi-mode'.

KBD-KEY is a single character keyboard-key defined as a
user-command for a keyword-search in `navi-mode'. A list of all
registered major-mode languages and their single-key commands can
be found in the customizable variable `navi-key-mappings'. The
regexps that define the keyword-searches associated with these
keyboard-keys can be found in the customizable variable
`navi-keywords'.

Note that all printable ASCII characters are predefined as
single-key commands in navi-mode, i.e. you can define
key-mappings and keywords for languages not yet registered in
navi-mode or add your own key-mappings and keywords for languages
already registered simply by customizing the two variables
mentioned above - as long as there are free keys available for
the language at hand. You need to respect navi-mode's own core
keybindings when doing so, of course.

Please share your own language definitions with the author so
that they can be included in navi-mode, resulting in a growing
number of supported languages over time.

If PREFER-IMENU-P is non-nil, this command calls `imenu' even if
`idomenu' is available.

By default, the whole string matched by the keyword-regexp plus the text
before the next space character is shown as result. If LAST-PARENTH-EXPR-P is
non-nil, only the last parenthetical expression in the match-data is shown,
i.e. the text following the regexp match until the next space character."
  ;; (interactive "cKeyboard key: ")
  (interactive
   (cond
    ((equal current-prefix-arg nil)
     (list (read-char "Key: ")))
    ((equal current-prefix-arg '(4))
     (list (read-char "Key: ")
           nil 'LAST-PARENTH-EXPR-P))
    ((equal current-prefix-arg '(16))
     (list (read-char "Key: ")
           'PREFER-IMENU-P 'LAST-PARENTH-EXPR-P))
    (t (list (read-char "Key: ")
             'PREFER-IMENU-P))))
  (if (require 'navi-mode nil 'NOERROR)
      (let* ((lang (car (split-string
                         (symbol-name major-mode)
                         "-mode" 'OMIT-NULLS)))
             (key (navi-map-keyboard-to-key
                   lang (char-to-string kbd-key)))
             (base-rgx (navi-get-regexp lang key))
             ;; (rgx (concat base-rgx "\\([^[:space:]]+[[:space:]]?$\\)"))
             (rgx (concat base-rgx "\\([^[:space:]]+[[:space:]]\\)"))
             (rgx-depth (regexp-opt-depth rgx))
             (outshine-imenu-generic-expression
              `((nil ,rgx ,(if LAST-PARENTH-EXPR-P rgx-depth 0))))
             (imenu-generic-expression
              outshine-imenu-generic-expression)
             (imenu-prev-index-position-function nil)
             (imenu-extract-index-name-function nil)
             (imenu-auto-rescan t)
             (imenu-auto-rescan-maxout 360000))
        ;; prefer idomenu
        (if (and (require 'idomenu nil 'NOERROR)
                 (not PREFER-IMENU-P))
            (funcall 'idomenu)
          ;; else call imenu
          (require 'imenu)
          (funcall 'imenu
                   (imenu-choose-buffer-index
                    (concat (car
                             (split-string
                              (symbol-name key) ":" 'OMIT-NULLS))
                            ": ")))))
    (message "Unable to load library `navi-mode.el'"))
  (setq imenu-generic-expression
        (or outshine-imenu-default-generic-expression
            outshine-imenu-preliminary-generic-expression)))


(defun outshine-imenu (&optional PREFER-IMENU-P)
  "Convenience function for calling imenu/idomenu from outshine."
  (interactive "P")
  (or outshine-imenu-default-generic-expression
      (setq outshine-imenu-default-generic-expression
            outshine-imenu-preliminary-generic-expression))
  (let* ((imenu-generic-expression
          outshine-imenu-default-generic-expression)
         (imenu-prev-index-position-function nil)
         (imenu-extract-index-name-function nil)
         (imenu-auto-rescan t)
         (imenu-auto-rescan-maxout 360000))
    ;; prefer idomenu
    (if (and (require 'idomenu nil 'NOERROR)
             (not PREFER-IMENU-P))
        (funcall 'idomenu)
      ;; else call imenu
      (funcall 'imenu
               (imenu-choose-buffer-index
                "Headline: ")))))

;;;;; Special Case Latex-mode

(defun outshine-latex-insert-header (&optional buf-or-name pt-or-marker)
  "Insert outshine-header for section at point in latex-buffer.
Use current-buffer, unless BUF-OR-NAME is given. Move to
PT-OR-MARKER first if given."
  (interactive
   (when current-prefix-arg
     (list (read-buffer "Latex-buffer: "))))
  (catch 'exit-let
    (let* ((buf (cond
		 ((and buf-or-name
		       (buffer-live-p (get-buffer buf-or-name))
		       (with-current-buffer buf-or-name
			 (eq major-mode 'latex-mode)))
		  buf-or-name)
		 ((eq major-mode 'latex-mode) (current-buffer))
		 (t (throw 'exit-let nil))))
	   (doc-class (outshine-get-latex-documentclass
		       buf 'NO-CHECK-P))
	   (section-alist (cdr (assoc doc-class
				      outshine-latex-classes))))
      (with-current-buffer buf
	(save-excursion
	  (save-restriction
	    (widen)
	    (when pt-or-marker
	      (goto-char pt-or-marker))
	    (when (looking-at
		   (concat "^[[:space:]]*"
			   "\\("
			   "\\\\part{\\|"
			   "\\\\chapter{\\|"
			   "\\\\section{\\|"
			   "\\\\subsection{\\|"
			   "\\\\subsubsection{\\|"
			   "\\\\paragraph{\\|"
			   "\\\\subparagraph{"
			   "\\)"))
	      (save-excursion
		(beginning-of-line)
		(let ((rgxps (mapcar 'cdr section-alist)))
		  (while rgxps
		    (let ((rgxp (pop rgxps)))
		      (when (looking-at rgxp)
			(let ((title (match-string 1)))
			  (insert
			   (concat
			    "\n"
			    (outshine-calc-outline-string-at-level
			     (car
			      (rassoc rgxp section-alist)))
			    title
			    "\n"))
			  (setq rgxps nil))))))))))))))

(defun outshine-latex-insert-headers-in-buffer (&optional buf-or-name no-preamble-p)
  "Insert outshine-headers for all sections in latex-mode buffer.
Use current-buffer, unless BUF-OR-NAME is given. Add a 1st-level
preamble header unless NO-PREAMBLE-P is non-nil."
  (interactive
   (when current-prefix-arg
     (list (read-buffer "Latex-buffer: ")
	   (y-or-n-p "Skip preamble "))))
  (catch 'exit-let
    (let* ((buf (cond
		 ((and buf-or-name
		       (buffer-live-p (get-buffer buf-or-name))
		       (with-current-buffer buf-or-name
			 (eq major-mode 'latex-mode)))
		  buf-or-name)
		 ((eq major-mode 'latex-mode) (current-buffer))
		 (t (throw 'exit-let nil))))
	   (doc-class (outshine-get-latex-documentclass
		       buf 'NO-CHECK-P))
	   (section-alist (cdr (assoc doc-class
				      outshine-latex-classes))))
      (with-current-buffer buf
	(save-excursion
	  (save-restriction
	    (widen)
	    (goto-char (point-min))
	    (unless no-preamble-p
	      (insert
	       (concat
		(outshine-calc-outline-string-at-level 1)
		"Preamble\n")))
	    (while (re-search-forward
		    (concat
		     "\\("
		     "\\\\part{\\|"
		     "\\\\chapter{\\|"
		     "\\\\section{\\|"
		     "\\\\subsection{\\|"
		     "\\\\subsubsection{\\|"
		     "\\\\paragraph{\\|"
		     "\\\\subparagraph{"
		     "\\)") nil t)
	      (save-excursion
		(beginning-of-line)
		(let ((rgxps (mapcar 'cdr section-alist)))
		  (while rgxps
		    (let ((rgxp (pop rgxps)))
		      (when (looking-at rgxp)
			(let ((title (match-string 1)))
			  (insert
			   (concat
			    "\n"
			    (outshine-calc-outline-string-at-level
			     (car
			      (rassoc rgxp section-alist)))
			    title
			    "\n"))
			  (setq rgxps nil))))))))))))))

(defun outshine-TeX-command-region-on-subtree (&optional arg)
  "Mark subtree and run `TeX-command-region'.
With one prefix ARG, try to move up one level before marking the
subtree, with two prefix ARGs, try to move up two levels before
marking subtree (and subsequently run the tex command)."
  (interactive "p")
  (save-excursion
    (cl-case arg
      (4 (ignore-errors
	   (outline-up-heading 1 t)))
      (16 (ignore-errors
	    (outline-up-heading 2 t)))
      (t nil))
    (message "%s" (point))
    (outline-mark-subtree)
    (call-interactively 'TeX-command-region))
  (deactivate-mark))

;;;;; Outshine Agenda

;; (defun outshine-agenda-add-files (&optional append-p &rest files)
;;   "Prepend FILES to `outshine-agenda-files'.
;; Append rather than prepend if APPEND-P is given or
;; `current-prefix-arg' is non-nil."
;;   (interactive
;;    (let (file-lst)
;;      (list
;;       current-prefix-arg
;;       (if (derived-mode-p 'dired-mode)
;; 	  (dired-get-marked-files)
;; 	(setq file-lst
;; 	      (cons
;; 	       (expand-file-name
;; 		(ido-read-file-name "New agenda file: "))
;; 	       file-lst))
;; 	(while (y-or-n-p "Add more files ")
;; 	  (setq file-lst
;; 		(cons (expand-file-name
;; 		       (ido-read-file-name "New agenda file: "))
;; 		      file-lst)))
;; 	file-lst))))
;;   (if append-p
;;       (setq outshine-agenda-files
;; 	    (delq nil (append outshine-agenda-files
;; 			      (car-safe files))))
;;     (setq outshine-agenda-files
;; 	  (delq nil (append (car-safe files)
;; 			    outshine-agenda-files)))))

;; (defun outshine-agenda-remove-files (&optional remove-all-p &rest files)
;;   "Remove FILES from `outshine-agenda-files'.
;; Remove all agenda-files if REMOVE-ALL-P is given or
;; `current-prefix-arg' is non-nil."
;;   (interactive
;;    (let (file-lst)
;;      (list
;;       current-prefix-arg
;;       (unless current-prefix-arg
;; 	(setq file-lst
;; 	      (cons
;; 	       (org-completing-read "Remove agenda file: "
;; 				    outshine-agenda-files)
;; 	       file-lst))
;; 	(while (y-or-n-p "Remove more files ")
;; 	  (setq file-lst
;; 		(cons
;; 		 (org-completing-read "Remove agenda file: "
;; 				      outshine-agenda-files)
;; 		 file-lst)))
;; 	file-lst))))
;;   (if remove-all-p
;;       (setq outshine-agenda-files nil)
;;     (mapc
;;      (lambda (--file)
;;        (setq outshine-agenda-files
;; 	     (remove --file outshine-agenda-files)))
;;      (car-safe files))))

;; (defun outshine-agenda-toggle-include-org-agenda (&optional arg)
;;   "Toggle inclusion of Org Agenda files in Outshine Agenda.
;; With prefix argument ARG, include if ARG is positive, otherwise
;; exclude."
;;   (interactive "P")
;;   (setq outshine-agenda-include-org-agenda-p
;;         (if (null arg)
;;             (not outshine-agenda-include-org-agenda-p)
;;           (> (prefix-numeric-value arg) 0)))
;;   (message "Outshine Agenda: inclusion of Org Agenda files %s"
;;            (if outshine-agenda-include-org-agenda-p
;; 	       "enabled" "disabled")))

;; (defun outshine-agenda (&optional agenda-file include-org-p)
;;   "Create Outshine Agenda, i.e. Org Agenda on outshine files.

;; Use org-file AGENDA-FILE instead of `outshine-agenda-files' when
;; given. Include `org-agenda-files' when INCLUDE-ORG-P is non-nil.

;; With `current-prefix-arg' prompt the user for argument values."
;;   (interactive
;;    (when current-prefix-arg
;;      (list
;;       (ido-read-file-name "Agenda file: "
;; 			  outshine-temporary-directory)
;;       (y-or-n-p "Include `org-agenda-files' "))))
;;   (let ((ag-file (or agenda-file
;; 		     (outshine-agenda-create-temporary-agenda-file)))
;; 	(with-org-agenda-files
;; 	 (or include-org-p outshine-agenda-include-org-agenda-p)))
;;     (require 'org-agenda)
;;     (org-agenda-remove-restriction-lock)
;;     (if with-org-agenda-files
;; 	;; FIXME
;; 	(message "Sorry, this is not yet implemented.")
;;       (with-current-buffer (find-file-noselect ag-file)
;; 	(org-agenda-set-restriction-lock 'file)
;; 	(org-agenda)))))

;;;;; Use Outorg for calling Org

;; ;; TEMPLATE A
;; (defun outshine- ()
;;   "Call outorg to trigger `org-'."
;;   (interactive)
;;   (outshine-use-outorg 'org-))

;; ;; TEMPLATE B
;; (defun outshine- (&optional arg)
;;   "Call outorg to trigger `org-'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org- nil arg))

;; ;; C-c C-a		org-attach
;; (defun outshine-attach ()
;;   "Call outorg to trigger `org-attach'."
;;   (interactive)
;;   (outshine-use-outorg 'org-attach))

;; ;; C-c C-b		org-backward-heading-same-level

;; ;; C-c C-c		org-ctrl-c-ctrl-c
;; (defun outshine-ctrl-c-ctrl-c (&optional arg)
;;   "Call outorg to trigger `org-ctrl-c-ctrl-c'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-ctrl-c-ctrl-c arg))

;; ;; C-c C-d		org-deadline
;; (defun outshine-deadline (&optional arg)
;;   "Call outorg to trigger `org-deadline'."
;;   (interactive "P")
;;   (outshine-use-outorg
;;    (lambda ()
;;      (interactive)
;;      (let ((current-prefix-arg arg))
;;        (call-interactively 'org-deadline)))))

;; ;; C-c C-e		org-export-dispatch
;; (defun outshine-export-dispatch (&optional arg)
;;   "Call outorg to trigger `org-export-dispatch'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-export-dispatch
;; 		       (y-or-n-p "Use whole buffer ")
;; 		       arg))

;; ;; C-c C-f		org-forward-heading-same-level

;; CANCELLED use `outshine-imenu' instead
;; ;; C-c C-j		org-goto
;; (defun outshine-goto ()
;;   "Call outorg to trigger `org-goto'."
;;   (interactive)
;;   (outshine-use-outorg 'org-goto t))

;; ;; C-c C-k		org-kill-note-or-show-branches

;; ;; C-c C-l		org-insert-link
;; (defun outshine-insert-link ()
;;   "Call outorg to trigger `org-insert-link'."
;;   (interactive)
;;   (outshine-use-outorg 'org-insert-link))

;; ;; C-c RET		org-ctrl-c-ret

;; ;; ;; C-c C-o		org-open-at-point
;; (defun outshine-open-at-point (&optional whole-buffer-p arg reference-buffer)
;;   "Call outorg to trigger `org-open-at-point'.
;; With one prefix argument, use whole buffer, with two prefix
;; arguments, prompt user for function args WHOLE-BUFFER-P, ARG and
;; REFERENCE-BUFFER."
;;   (interactive
;;    (cond
;;     ((equal current-prefix-arg '(16))
;;      (list (y-or-n-p "Use whole buffer ")
;; 	   (y-or-n-p "Provide ARG ")
;; 	   (read-buffer "Reference-buffer: ")))
;;     (current-prefix-arg (list t))
;;     (t nil)))
;;   (outshine-use-outorg
;;    'org-open-at-point whole-buffer-p nil arg reference-buffer))

;; ;; C-c C-q		org-set-tags-command
;; (defun outshine-set-tags-command ()
;;   "Call outorg to trigger `org-set-tags-command'."
;;   (interactive)
;;   (outshine-use-outorg 'org-set-tags-command))

;; TODO reimplement for outshine
;; ;; C-c C-r		org-reveal
;; (defun outshine-reveal ()
;;   "Call outorg to trigger `org-reveal'."
;;   (interactive)
;;   (outshine-use-outorg 'org-reveal 'WHOLE-BUFFER-P))

;; ;; C-c C-s		org-schedule
;; (defun outshine-schedule (&optional arg)
;;   "Call outorg to trigger `org-schedule'."
;;   (interactive "P")
;;   (outshine-use-outorg
;;    (lambda ()
;;      (interactive)
;;      (let ((current-prefix-arg arg))
;;        (call-interactively 'org-schedule)))))

;; FIXED -> org-store-log-note _outcommented_!
;; FIXME lognote insertion position
;; ;; C-c C-t		org-todo
;; (defun outshine-todo (&optional arg)
;;   "Call outorg to trigger `org-todo'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-todo nil arg))

;; ;; C-c C-v		Prefix Command

;; CANCELLED use outshine-imenu for (org-refile t)
;; ;; C-c C-w		org-refile
;; (defun outshine-refile ()
;;   "Call outorg to trigger `org-refile'."
;;   (interactive)
;;   (outshine-use-outorg 'org-refile))

;; ;; C-c C-x		Prefix Command

;; ;; C-c C-y		org-evaluate-time-range
;; (defun outshine-evaluate-time-range ()
;;   "Call outorg to trigger `org-evaluate-time-range'."
;;   (interactive)
;;   (outshine-use-outorg 'org-evaluate-time-range))

;; FIXME post-command-hook
;; ;; C-c C-z		org-add-note
;; (defun outshine-add-note ()
;;   "Call outorg to trigger `org-add-note'."
;;   (interactive)
;;   (outshine-use-outorg 'org-add-note))

;; ;; C-c ESC		Prefix Command
;; ;; C-c C-^		org-up-element
;; ;; C-c C-_		org-down-element

;; ;; C-c SPC		org-table-blank-field
;; (defun outshine-table-blank-field ()
;;   "Call outorg to trigger `org-table-blank-field'."
;;   (interactive)
;;   (outshine-use-outorg 'org-table-blank-field))

;; ;; C-c !		org-time-stamp-inactive
;; (defun outshine-time-stamp-inactive (&optional arg)
;;   "Call outorg to trigger `org-time-stamp-inactive'."
;;   (interactive "P")
;;   (outshine-use-outorg
;;    (lambda ()
;;      (interactive)
;;      (if (not (org-on-heading-p))
;; 	 	 (if arg
;; 		     (org-time-stamp-inactive arg)
;; 		   (org-time-stamp-inactive))
;;        (or
;; 	(and
;; 	 (re-search-forward org-element--timestamp-regexp nil t)
;; 	 (ignore-errors (goto-char (match-beginning 0))))
;; 	(and
;; 	 (re-search-forward org-complex-heading-regexp nil t)
;; 	 (ignore-errors (goto-char (match-end 4)))))
;;        (insert-char ? )
;;        (if arg
;; 	   (org-time-stamp-inactive arg)
;; 	 (org-time-stamp-inactive))))))

;; ;; C-c #		org-update-statistics-cookies
;; (defun outshine-update-statistics-cookies ()
;;   "Call outorg to trigger `org-update-statistics-cookies'."
;;   (interactive)
;;   (outshine-use-outorg 'org-update-statistics-cookies))

;; ;; C-c $		org-archive-subtree
;; (defun outshine-archive-subtree ()
;;   "Call outorg to trigger `org-archive-subtree'."
;;   (interactive)
;;   (outshine-use-outorg 'org-archive-subtree))

;; ;; C-c %		org-mark-ring-push
;; (defun outshine-mark-ring-push ()
;;   "Call outorg to trigger `org-mark-ring-push'."
;;   (interactive)
;;   (outshine-use-outorg 'org-mark-ring-push))

;; ;; C-c &		org-mark-ring-goto
;; (defun outshine-mark-ring-goto ()
;;   "Call outorg to trigger `org-mark-ring-goto'."
;;   (interactive)
;;   (outshine-use-outorg 'org-mark-ring-goto))

;; ;; C-c '		org-edit-special
;; (defun outshine-edit-special ()
;;   "Call outorg to trigger `org-edit-special'."
;;   (interactive)
;;   (outshine-use-outorg 'org-edit-special))

;; ;; C-c *		org-ctrl-c-star
;; (defun outshine-ctrl-c-star ()
;;   "Call outorg to trigger `org-ctrl-c-star'."
;;   (interactive)
;;   (outshine-use-outorg 'org-ctrl-c-star))

;; ;; C-c +		org-table-sum
;; (defun outshine-table-sum ()
;;   "Call outorg to trigger `org-table-sum'."
;;   (interactive)
;;   (outshine-use-outorg 'org-table-sum))

;; ;; ;; C-c ,		org-priority
;; (defun outshine-priority ()
;;   "Call outorg to trigger `org-priority'."
;;   (interactive)
;;   (outshine-use-outorg 'org-priority))

;; ;; FIXME:
;; ;; - cursor moves to parent header
;; ;; - does nothing at bol ?
;; ;; C-c -		org-ctrl-c-minus
;; (defun outshine-ctrl-c-minus ()
;;   "Call outorg to trigger `org-ctrl-c-minus'."
;;   (interactive)
;;   (outshine-use-outorg 'org-ctrl-c-minus))

;; ;; C-c .		org-time-stamp
;; (defun outshine-time-stamp (&optional arg)
;;   "Call outorg to trigger `org-time-stamp'."
;;   (interactive "P")
;;   (outshine-use-outorg
;;    (lambda ()
;;      (interactive)
;;      (if (not (org-on-heading-p))
;; 	 (if arg (org-time-stamp arg) (org-time-stamp nil))
;;        (or
;; 	(and
;; 	 (re-search-forward org-element--timestamp-regexp nil t)
;; 	 (ignore-errors (goto-char (match-beginning 0))))
;; 	(and
;; 	 (re-search-forward org-complex-heading-regexp nil t)
;; 	 (ignore-errors (goto-char (match-end 4)))))
;;        (insert-char ? )
;;        	 (if arg (org-time-stamp arg) (org-time-stamp nil))))))

;; CANCELLED makes no sense
;; ;; C-c /		org-sparse-tree
;; (defun outshine-sparse-tree ()
;;   "Call outorg to trigger `org-sparse-tree'."
;;   (interactive)
;;   (outshine-use-outorg 'org-sparse-tree))

;; ;; C-c :		org-toggle-fixed-width
;; (defun outshine-toggle-fixed-width ()
;;   "Call outorg to trigger `org-toggle-fixed-width'."
;;   (interactive)
;;   (outshine-use-outorg 'org-toggle-fixed-width))

;; ;; C-c ;		org-toggle-comment
;; (defun outshine-toggle-comment ()
;;   "Call outorg to trigger `org-toggle-comment'."
;;   (interactive)
;;   (outshine-use-outorg 'org-toggle-comment))

;; ;; C-c <		org-date-from-calendar
;; (defun outshine-date-from-calendar ()
;;   "Call outorg to trigger `org-date-from-calendar'."
;;   (interactive)
;;   (outshine-use-outorg 'org-date-from-calendar))

;; ;; C-c =		org-table-eval-formula
;; (defun outshine-table-eval-formula ()
;;   "Call outorg to trigger `org-table-eval-formula'."
;;   (interactive)
;;   (outshine-use-outorg 'org-table-eval-formula))

;; ;; C-c >		org-goto-calendar
;; (defun outshine-goto-calendar ()
;;   "Call outorg to trigger `org-goto-calendar'."
;;   (interactive)
;;   (outshine-use-outorg 'org-goto-calendar))

;; ;; C-c ?		org-table-field-info
;; (defun outshine-table-field-info ()
;;   "Call outorg to trigger `org-table-field-info'."
;;   (interactive)
;;   (outshine-use-outorg 'org-table-field-info))

;; CANCELLED use `outline-mark-subtree' instead
;; ;; C-c @		org-mark-subtree
;; (defun outshine-mark-subtree ()
;;   "Call outorg to trigger `org-mark-subtree'."
;;   (interactive)
;;   (outshine-use-outorg 'org-mark-subtree))

;; ;; C-c \		org-match-sparse-tree
;; (defun outshine-match-sparse-tree ()
;;   "Call outorg to trigger `org-match-sparse-tree'."
;;   (interactive)
;;   (outshine-use-outorg 'org-match-sparse-tree 'WHOLE-BUFFER-P))

;; ;; FIXME handle markers for sorting regionso2
;; ;; C-c ^		org-sort
;; (defun outshine-sort-entries (&optional arg)
;;   "Call outorg to trigger `org-sort'.
;; With prefix ARG, use whole buffer."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-sort-entries arg))

;;   (interactive)
;;   (outshine-use-outorg 'org-table-edit-field))

;; ;; C-c {		org-table-toggle-formula-debugger
;; (defun outshine-table-toggle-formula-debugger ()
;;   "Call outorg to trigger `org-table-toggle-formula-debugger'."
;;   (interactive)
;;   (outshine-use-outorg 'org-table-toggle-formula-debugger))

;; ;; C-c |		org-table-create-or-convert-from-region
;; (defun outshine-table-create-or-convert-from-region ()
;;   "Call outorg to trigger `org-table-create-or-convert-from-region'."
;;   (interactive)
;;   (outshine-use-outorg 'org-table-create-or-convert-from-region))

;; ;; C-c }		org-table-toggle-coordinate-overlays
;; (defun outshine-table-toggle-coordinate-overlays ()
;;   "Call outorg to trigger `org-table-toggle-coordinate-overlays'."
;;   (interactive)
;;   (outshine-use-outorg 'org-table-toggle-coordinate-overlays))

;; ;; C-c ~		org-table-create-with-table.el
;; (defun outshine-table-create-with-table.el ()
;;   "Call outorg to trigger `org-table-create-with-table.el'."
;;   (interactive)
;;   (outshine-use-outorg 'org-table-create-with-table.el))

;; ;; C-c C-*		org-list-make-subtree
;; (defun outshine-list-make-subtree ()
;;   "Call outorg to trigger `org-list-make-subtree'."
;;   (interactive)
;;   (outshine-use-outorg 'org-list-make-subtree))

;; ;; C-c <down>	org-shiftdown
;; ;; C-c <up>	org-shiftup
;; (defun outshine- ()
;;   "Call outorg to trigger `org-'."
;;   (interactive)
;;   (outshine-use-outorg 'org-))

;; ;; C-c C-M-l	org-insert-all-links
;; (defun outshine-insert-all-links ()
;;   "Call outorg to trigger `org-insert-all-links'."
;;   (interactive)
;;   (outshine-use-outorg 'org-insert-all-links))

;; (defun outshine-previous-block ()
;;   "Call outorg to trigger `org-previous-block'."
;;   (interactive)
;;   (outshine-use-outorg 'org-previous-block 'WHOLE-BUFFER-P))

;; ;; FIXME
;; ;; ;; C-c M-b		org-previous-block
;; (defun outshine-previous-block ()
;;   "Similar semantics to `org-previous-block'."
;;   (interactive)
;;   (forward-comment -10000))

;; ;; FIXME
;; ;; C-c M-f		org-next-block
;; (defun outshine-next-block ()
;;   "Similar semantics to `org-next-block'."
;;   (interactive)
;;   (forward-comment 10000))

;; ;; C-c M-l		org-insert-last-stored-link
;; (defun outshine-insert-last-stored-link ()
;;   "Call outorg to trigger `org-insert-last-stored-link'."
;;   (interactive)
;;   (outshine-use-outorg 'org-insert-last-stored-link))

;; ;; C-c M-o		tj/mail-subtree

;; ;; C-c M-w		org-copy
;; (defun outshine-copy ()
;;   "Call outorg to trigger `org-copy'."
;;   (interactive)
;;   (outshine-use-outorg 'org-copy))

;; ;; C-c C-v C-a	org-babel-sha1-hash
;; (defun outshine-babel-sha1-hash ()
;;   "Call outorg to trigger `org-babel-sha1-hash'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-sha1-hash))

;; ;; C-c C-v C-b	org-babel-execute-buffer
;; (defun outshine-babel-execute-buffer ()
;;   "Call outorg to trigger `org-babel-execute-buffer'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-execute-buffer 'WHOLE-BUFFER-P))

;; ;; C-c C-v C-c	org-babel-check-src-block
;; (defun outshine-babel-check-src-block ()
;;   "Call outorg to trigger `org-babel-check-src-block'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-check-src-block))

;; ;; C-c C-v C-d	org-babel-demarcate-block
;; (defun outshine-babel-demarcate-block ()
;;   "Call outorg to trigger `org-babel-demarcate-block'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-demarcate-block))

;; ;; C-c C-v C-e	org-babel-execute-maybe
;; (defun outshine-babel-execute-maybe ()
;;   "Call outorg to trigger `org-babel-execute-maybe'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-execute-maybe))

;; ;; C-c C-v C-f	org-babel-tangle-file
;; (defun outshine-babel-tangle-file ()
;;   "Call outorg to trigger `org-babel-tangle-file'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-tangle-file 'WHOLE-BUFFER-P))

;; ;; C-c C-v TAB	org-babel-view-src-block-info
;; (defun outshine-babel-view-src-block-info ()
;;   "Call outorg to trigger `org-babel-view-src-block-info'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-view-src-block-info))

;; ;; FIXME:
;; ;; split-string: Wrong type argument: stringp, nil
;; ;; C-c C-v C-j	org-babel-insert-header-arg
;; (defun outshine-babel-insert-header-arg ()
;;   "Call outorg to trigger `org-babel-insert-header-arg'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-insert-header-arg))

;; ;; C-c C-v C-l	org-babel-load-in-session
;; (defun outshine-babel-load-in-session ()
;;   "Call outorg to trigger `org-babel-load-in-session'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-load-in-session))

;; ;; C-c C-v C-n	org-babel-next-src-block
;; (defun outshine-babel-next-src-block ()
;;   "Call outorg to trigger `org-babel-next-src-block'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-next-src-block))

;; ;; C-c C-v C-o	org-babel-open-src-block-result
;; (defun outshine-babel-open-src-block-result ()
;;   "Call outorg to trigger `org-babel-open-src-block-result'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-open-src-block-result))

;; ;; C-c C-v C-p	org-babel-previous-src-block
;; (defun outshine-babel-previous-src-block ()
;;   "Call outorg to trigger `org-babel-previous-src-block'."
;;   (interactive)
;;   (outshine-use-outorg
;;    'org-babel-previous-src-block 'WHOLE-BUFFER-P))

;; ;; C-c C-v C-r	org-babel-goto-named-result
;; (defun outshine-babel-goto-named-result ()
;;   "Call outorg to trigger `org-babel-goto-named-result'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-goto-named-result
;; 		       'WHOLE-BUFFER-P))

;; ;; C-c C-v C-s	org-babel-execute-subtree
;; (defun outshine-babel-execute-subtree ()
;;   "Call outorg to trigger `org-babel-execute-subtree'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-execute-subtree))

;; ;; C-c C-v C-t	org-babel-tangle
;; (defun outshine-babel-tangle ()
;;   "Call outorg to trigger `org-babel-tangle'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-tangle 'WHOLE-BUFFER-P))

;; ;; C-c C-v C-u	org-babel-goto-src-block-head
;; (defun outshine-babel-goto-src-block-head ()
;;   "Call outorg to trigger `org-babel-goto-src-block-head'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-goto-src-block-head))

;; ;; C-c C-v C-v	org-babel-expand-src-block
;; (defun outshine-babel-expand-src-block ()
;;   "Call outorg to trigger `org-babel-expand-src-block'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-expand-src-block))

;; ;; C-c C-v C-x	org-babel-do-key-sequence-in-edit-buffer
;; (defun outshine-babel-do-key-sequence-in-edit-buffer ()
;;   "Call outorg to trigger `org-babel-do-key-sequence-in-edit-buffer'."
;;   (interactive)
;;   (outshine-use-outorg
;;    'org-babel-do-key-sequence-in-edit-buffer))

;; ;; C-c C-v C-z	org-babel-switch-to-session
;; (defun outshine-babel-switch-to-session ()
;;   "Call outorg to trigger `org-babel-switch-to-session'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-switch-to-session))

;; ;; C-c C-v ESC	Prefix Command
;; ;; C-c C-v I	org-babel-view-src-block-info
;; ;; C-c C-v a	org-babel-sha1-hash
;; ;; C-c C-v b	org-babel-execute-buffer
;; ;; C-c C-v c	org-babel-check-src-block
;; ;; C-c C-v d	org-babel-demarcate-block
;; ;; C-c C-v e	org-babel-execute-maybe
;; ;; C-c C-v f	org-babel-tangle-file

;; ;; C-c C-v g	org-babel-goto-named-src-block
;; (defun outshine-babel-goto-named-src-block ()
;;   "Call outorg to trigger `org-babel-goto-named-src-block'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-goto-named-src-block
;; 		       'WHOLE-BUFFER-P))

;; ;; C-c C-v h	org-babel-describe-bindings
;; (defun outshine-babel-describe-bindings ()
;;   "Call outorg to trigger `org-babel-describe-bindings'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-describe-bindings))

;; ;; C-c C-v i	org-babel-lob-ingest
;; (defun outshine-babel-lob-ingest ()
;;   "Call outorg to trigger `org-babel-lob-ingest'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-lob-ingest 'WHOLE-BUFFER-P))

;; ;; C-c C-v j	org-babel-insert-header-arg

;; ;; C-c C-v k	org-babel-remove-result-one-or-many
;; (defun outshine-babel-remove-result-one-or-many (&optional arg)
;;   "Call outorg to trigger `org-babel-remove-result-one-or-many'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-babel-remove-result-one-or-many arg))

;; ;; C-c C-v l	org-babel-load-in-session
;; ;; C-c C-v n	org-babel-next-src-block
;; ;; C-c C-v o	org-babel-open-src-block-result
;; ;; C-c C-v p	org-babel-previous-src-block
;; ;; C-c C-v r	org-babel-goto-named-result
;; ;; C-c C-v s	org-babel-execute-subtree
;; ;; C-c C-v t	org-babel-tangle
;; ;; C-c C-v u	org-babel-goto-src-block-head
;; ;; C-c C-v v	org-babel-expand-src-block
;; ;; C-c C-v x	org-babel-do-key-sequence-in-edit-buffer

;; ;; C-c C-v z	org-babel-switch-to-session-with-code
;; (defun outshine-babel-switch-to-session-with-code ()
;;   "Call outorg to trigger `org-babel-switch-to-session-with-code'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-switch-to-session-with-code))

;; ;; C-c C-x C-a	org-archive-subtree-default
;; (defun outshine-archive-subtree-default ()
;;   "Call outorg to trigger `org-archive-subtree-default'."
;;   (interactive)
;;   (outshine-use-outorg 'org-archive-subtree-default))

;; ;; C-c C-x C-b	org-toggle-checkbox
;; (defun outshine-toggle-checkbox (&optional arg)
;;   "Call outorg to trigger `org-toggle-checkbox'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-toggle-checkbox nil arg))

;; ;; C-c C-x C-c	org-columns
;; (defun outshine-columns ()
;;   "Call outorg to trigger `org-columns'."
;;   (interactive)
;;   (outshine-use-outorg 'org-columns 'WHOLE-BUFFER-P))

;; ;; C-c C-x C-d	org-clock-display
;; (defun outshine-clock-display ()
;;   "Call outorg to trigger `org-clock-display'."
;;   (interactive)
;;   (outshine-use-outorg 'org-clock-display 'WHOLE-BUFFER-P))

;; CANCELLED simply call `org-emphasize'
;; ;; C-c C-x C-f	org-emphasize
;; (defun outshine-emphasize ()
;;   "Call outorg to trigger `org-emphasize'."
;;   (interactive)
;;   (outshine-use-outorg 'org-emphasize))

;; ;; C-c C-x TAB	org-clock-in
;; (defun outshine-clock-in ()
;;   "Call outorg to trigger `org-clock-in'."
;;   (interactive)
;;   (outshine-use-outorg
;;    (lambda ()
;;      (interactive)
;;      (org-clock-in)
;;      (remove-hook 'kill-buffer-hook 'org-check-running-clock))))

;; ;; C-c C-x C-j	org-clock-goto
;; (defun outshine-clock-goto ()
;;   "Similar semantics to `org-clock-goto'."
;;   (interactive)
;;   (switch-to-buffer
;;    (condition-case err
;;        (marker-buffer outshine-use-outorg-last-headline-marker)
;;      (error "Can't find header with running clock: %s" err)))
;;    (goto-char outshine-use-outorg-last-headline-marker))

;; ;; C-c C-x C-l	org-preview-latex-fragment
;; (defun outshine-preview-latex-fragment ()
;;   "Call outorg to trigger `org-preview-latex-fragment'."
;;   (interactive)
;;   (outshine-use-outorg 'org-preview-latex-fragment))

;; ;; C-c C-x RET	Prefix Command

;; ;; reimplementation
;; ;; C-c C-x C-n	org-next-link
;; (defun outshine-next-link ()
;;   "Similar semantics to `org-next-link'."
;;   (interactive)
;;   (re-search-forward org-link-re-with-space nil t 1)
;;   (goto-char (match-beginning 0)))

;; ;; C-c C-x C-o	org-clock-out
;; (defun outshine-clock-out ()
;;   "Call outorg to trigger `org-clock-out'."
;;   (interactive)
;;   (with-current-buffer
;;       (condition-case err
;; 	  (marker-buffer outshine-use-outorg-last-headline-marker)
;; 	(error "Can't find header with running clock: %s" err))
;;     (goto-char outshine-use-outorg-last-headline-marker)
;;     (outshine-use-outorg 'org-clock-out)))

;; ;; reimplementation
;; ;; C-c C-x C-p	org-previous-link
;; (defun outshine-previous-link ()
;;   "Similar semantics to `org-previous-link'."
;;   (interactive)
;;   (re-search-backward org-link-re-with-space nil t 1)
;;   (goto-char (match-beginning 0)))

;; ;; C-c C-x C-q	org-clock-cancel
;; (defun outshine-clock-cancel ()
;;   "Call outorg to trigger `org-clock-cancel'."
;;   (interactive)
;;   (with-current-buffer
;;       (condition-case err
;; 	  (marker-buffer outshine-use-outorg-last-headline-marker)
;; 	(error "Can't find header with running clock: %s" err))
;;     (goto-char outshine-use-outorg-last-headline-marker)
;;     (outshine-use-outorg 'org-clock-cancel)))

;; ;; C-c C-x C-r	org-clock-report
;; (defun outshine-clock-report (&optional arg)
;;   "Call outorg to trigger `org-clock-report'."
;;   (interactive)
;;   (outshine-use-outorg 'org-clock-report 'WHOLE-BUFFER-P arg))

;; ;; C-c C-x C-s	org-advertized-archive-subtree
;; (defun outshine-advertized-archive-subtree (&optional arg)
;;   "Call outorg to trigger `org-advertized-archive-subtree'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-advertized-archive-subtree arg))

;; ;; C-c C-x C-t	org-toggle-time-stamp-overlays
;; (defun outshine-toggle-time-stamp-overlays ()
;;   "Call outorg to trigger `org-toggle-time-stamp-overlays'."
;;   (interactive)
;;   (outshine-use-outorg 'org-toggle-time-stamp-overlays
;; 		       'WHOLE-BUFFER-P))

;; ;; C-c C-x C-u	org-dblock-update
;; (defun outshine-dblock-update (&optional arg)
;;   "Call outorg to trigger `org-dblock-update'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-dblock-update arg))

;; ;; C-c C-x C-v	org-toggle-inline-images
;; (defun outshine-toggle-inline-images ()
;;   "Call outorg to trigger `org-toggle-inline-images'."
;;   (interactive)
;;   (outshine-use-outorg
;;    'org-toggle-inline-images 'WHOLE-BUFFER-P))

;; ;; C-c C-x C-w	org-cut-special
;; (defun outshine-cut-special ()
;;   "Call outorg to trigger `org-cut-special'."
;;   (interactive)
;;   (outshine-use-outorg 'org-cut-special 'WHOLE-BUFFER-P))

;; FIXME
;; ;; C-c C-x C-x	org-clock-in-last
;; (defun outshine-clock-in-last (&optional arg)
;;   "Call outorg to trigger `org-clock-in-last'."
;;   (interactive "P")
;;   (with-current-buffer
;;       (condition-case err
;; 	  (marker-buffer outshine-use-outorg-last-headline-marker)
;; 	(error "Can't find header with running clock: %s" err))
;;     (goto-char outshine-use-outorg-last-headline-marker)
;;     (outshine-use-outorg 'org-clock-in-last nil arg)))

;; ;; C-c C-x C-y	org-paste-special
;; (defun outshine-paste-special ()
;;   "Call outorg to trigger `org-paste-special'."
;;   (interactive)
;;   (outshine-use-outorg 'org-paste-special 'WHOLE-BUFFER-P))

;; ;; FIXME: whole buffer?
;; ;; C-c C-x C-z	org-resolve-clocks
;; (defun outshine-resolve-clocks ()
;;   "Call outorg to trigger `org-resolve-clocks'."
;;   (interactive)
;;   (outshine-use-outorg 'org-resolve-clocks))

;; ;; C-c C-x ESC	Prefix Command
;; ;; C-c C-x !	org-reload
;; (defun outshine-reload ()
;;   "Call outorg to trigger `org-reload'."
;;   (interactive)
;;   (otshine-use-outorg 'org-reload))

;; ;; C-c C-x ,	org-timer-pause-or-continue
;; (defun outshine-timer-pause-or-continue (&optional arg)
;;   "Call outorg to trigger `org-timer-item'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-timer-pause-or-continue nil arg))

;; ;; C-c C-x -	org-timer-item
;; (defun outshine-timer-item ()
;;   "Call outorg to trigger `org-timer-item'."
;;   (interactive)
;;   (outshine-use-outorg 'org-timer-item))

;; ;; C-c C-x .	org-timer
;; (defun outshine-timer ()
;;   "Call outorg to trigger `org-timer'."
;;   (interactive)
;;   (outshine-use-outorg 'org-timer))

;; ;; C-c C-x 0	org-timer-start
;; (defun outshine-timer-start ()
;;   "Call outorg to trigger `org-timer-start'."
;;   (interactive)
;;   (outshine-use-outorg 'org-timer-start))

;; ;; C-c C-x :	org-timer-cancel-timer
;; (defun outshine-timer-cancel-timer ()
;;   "Call outorg to trigger `org-timer-cancel-timer'."
;;   (interactive)
;;   (outshine-use-outorg 'org-timer-cancel-timer))

;; ;; C-c C-x ;	org-timer-set-timer
;; (defun outshine-timer-set-timer ()
;;   "Call outorg to trigger `org-timer-set-timer'."
;;   (interactive)
;;   (outshine-use-outorg 'org-timer-set-timer))

;; ;; C-c C-x <	org-agenda-set-restriction-lock
;; (defun outshine-agenda-set-restriction-lock (&optional arg)
;;   "Call `outshine-agenda' with restriction.
;; With prefix ARG given, restrict to current subtree, otherwise to
;; current buffer(-file). "
;;   (interactive "P")
;;   (let ((ag-file
;; 	 (if arg
;; 	     (outshine-agenda-create-temporary-agenda-file t)
;; 	   (outshine-agenda-create-temporary-agenda-file 'file))))
;;     (outshine-agenda ag-file)))

;; ;; C-c C-x >	org-agenda-remove-restriction-lock
;; (defun outshine-agenda-remove-restriction-lock (&optional include-org-p)
;;   "Call `outshine-agenda' without restriction.
;; Use `outshine-agenda-files'. When INCLUDE-ORG-P is non-nil or prefix-arg is given, include `org-agenda-files'."
;;   (interactive "P")
;;   (outshine-agenda nil include-org-p))

;; ;; C-c C-x A	org-archive-to-archive-sibling
;; (defun outshine-archive-to-archive-sibling ()
;;   "Call outorg to trigger `org-archive-to-archive-sibling'."
;;   (interactive)
;;   (outshine-use-outorg 'org-archive-to-archive-sibling
;; 		       'WHOLE-BUFFER-P))

;; ;; C-c C-x D	org-shiftmetadown

;; ;; C-c C-x E	org-inc-effort
;; (defun outshine-inc-effort ()
;;   "Call outorg to trigger `org-inc-effort'."
;;   (interactive)
;;   (outshine-use-outorg 'org-inc-effort))

;; ;; C-c C-x G	org-feed-goto-inbox
;; (defun outshine-feed-goto-inbox ()
;;   "Call outorg to trigger `org-feed-goto-inbox'."
;;   (interactive)
;;   (outshine-use-outorg 'org-feed-goto-inbox 'WHOLE-BUFFER-P))

;; ;; C-c C-x L	org-shiftmetaleft

;; ;; C-c C-x M	org-insert-todo-heading
;; (defun outshine-insert-todo-heading (&optional arg)
;;   "Call outorg to trigger `org-insert-todo-heading'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-insert-todo-heading
;; 		       (= (prefix-numeric-value arg) 16)))

;; ;; C-c C-x P	org-set-property-and-value
;; (defun outshine-set-property-and-value ()
;;   "Call outorg to trigger `org-set-property-and-value'."
;;   (interactive)
;;   (outshine-use-outorg 'org-set-property-and-value))

;; ;; C-c C-x R	org-shiftmetaright
;; ;; C-c C-x U	org-shiftmetaup

;; ;; C-c C-x [	org-reftex-citation
;; (defun outshine-reftex-citation ()
;;   "Call outorg to trigger `org-reftex-citation'."
;;   (interactive)
;;   (outshine-use-outorg 'org-reftex-citation 'WHOLE-BUFFER-P))

;; ;; C-c C-x \	org-toggle-pretty-entities
;; (defun outshine-toggle-pretty-entities ()
;;   "Call outorg to trigger `org-toggle-pretty-entities'."
;;   (interactive)
;;   (outshine-use-outorg 'org-toggle-pretty-entities
;; 		       'WHOLE-BUFFER-P))

;; ;; FIXME: whole buffer?
;; ;; C-c C-x _	org-timer-stop
;; (defun outshine-timer-stop ()
;;   "Call outorg to trigger `org-timer-stop'."
;;   (interactive)
;;   (outshine-use-outorg 'org-timer-stop))

;; ;; C-c C-x a	org-toggle-archive-tag
;; (defun outshine-toggle-archive-tag ()
;;   "Call outorg to trigger `org-toggle-archive-tag'."
;;   (interactive)
;;   (outshine-use-outorg 'org-toggle-archive-tag))

;; ;; C-c C-x b	org-tree-to-indirect-buffer
;; (defun outshine-tree-to-indirect-buffer (&optional arg)
;;   "Call outorg to trigger `org-tree-to-indirect-buffer'."
;;   (interactive "P")
;;   (outshine-use-outorg 'org-tree-to-indirect-buffer arg))

;; ;; C-c C-x c	org-clone-subtree-with-time-shift
;; (defun outshine-clone-subtree-with-time-shift ()
;;   "Call outorg to trigger `org-clone-subtree-with-time-shift'."
;;   (interactive)
;;   (outshine-use-outorg 'org-clone-subtree-with-time-shift))

;; ;; C-c C-x d	org-insert-drawer
;; (defun outshine-insert-drawer ()
;;   "Call outorg to trigger `org-insert-drawer'."
;;   (interactive)
;;   (outshine-use-outorg 'org-insert-drawer))

;; ;; ;; C-c C-x e	org-set-effort
;; (defun outshine-set-effort (&optional arg)
;;   "Call outorg to trigger `org-set-effort'."
;;   (interactive "p")
;;   (outshine-use-outorg
;;    'org-set-effort nil arg))

;; ;; C-c C-x f	org-footnote-action
;; (defun outshine-footnote-action (&optional special)
;;   "Call outorg to trigger `org-footnote-action'."
;;   (interactive "P")
;;   (outshine-use-outorg
;;    'org-footnote-action 'WHOLE-BUFFER-P special))

;; ;; C-c C-x g	org-feed-update-all
;; (defun outshine-feed-update-all ()
;;   "Call outorg to trigger `org-feed-update-all'."
;;   (interactive)
;;   (outshine-use-outorg 'org-feed-update-all))

;; ;; C-c C-x i	org-insert-columns-dblock
;; (defun outshine-insert-columns-dblock ()
;;   "Call outorg to trigger `org-insert-columns-dblock'."
;;   (interactive)
;;   (outshine-use-outorg 'org-insert-columns-dblock))

;; ;; C-c C-x l	org-metaleft
;; ;; C-c C-x m	org-meta-return

;; ;; C-c C-x o	org-toggle-ordered-property
;; (defun outshine-toggle-ordered-property ()
;;   "Call outorg to trigger `org-toggle-ordered-property'."
;;   (interactive)
;;   (outshine-use-outorg 'org-toggle-ordered-property))

;; ;; C-c C-x p	org-set-property
;; (defun outshine-set-property ()
;;   "Call outorg to trigger `org-set-property'."
;;   (interactive)
;;   (outshine-use-outorg 'org-set-property))

;; ;; C-c C-x q	org-toggle-tags-groups
;; (defun outshine-toggle-tags-groups ()
;;   "Call outorg to trigger `org-toggle-tags-groups'."
;;   (interactive)
;;   (outshine-use-outorg 'org-toggle-tags-groups))

;; ;; C-c C-x r	org-metaright
;; ;; C-c C-x u	org-metaup

;; ;; C-c C-x v	org-copy-visible
;; (defun outshine-copy-visible ()
;;   "Call outorg to trigger `org-copy-visible'."
;;   (interactive)
;;   (outshine-use-outorg 'org-copy-visible 'WHOLE-BUFFER-P))

;; ;; C-c C-x <left>	org-shiftcontrolleft
;; ;; C-c C-x <right>			org-shiftcontrolright

;; ;; C-c M-#		outorg-edit-as-org
;; ;; C-c M-+		outorg-edit-comments-and-propagate-changes
;; ;; C-c M-a		show-all
;; ;; C-c M-c		hide-entry
;; ;; C-c M-e		show-entry
;; ;; C-c M-k		show-branches
;; ;; C-c M-p		outshine-imenu
;; ;; C-c M-q		outline-hide-sublevels
;; ;; C-c M-t		hide-body
;; ;; C-c M-u		outline-up-heading

;; ;; C-c C-v C-M-h	org-babel-mark-block
;; (defun outshine-babel-mark-block ()
;;   "Call outorg to trigger `org-babel-mark-block'."
;;   (interactive)
;;   (outshine-use-outorg 'org-babel-mark-block))

;; ;; C-c C-x C-M-v	org-redisplay-inline-images
;; (defun outshine-redisplay-inline-images ()
;;   "Call outorg to trigger `org-redisplay-inline-images'."
;;   (interactive)
;;   (outshine-use-outorg 'org-redisplay-inline-images
;; 		       'WHOLE-BUFFER-P))

;; ;; ;; C-c C-x M-w	org-copy-special
;; (defun outshine-copy-special ()
;;   "Call outorg to trigger `org-copy-special'."
;;   (interactive)
;;   (outshine-use-outorg 'org-copy-special))

;; ;; C-c C-x RET g	org-mobile-pull
;; (defun outshine-mobile-pull ()
;;   "Call outorg to trigger `org-mobile-pull'."
;;   (interactive)
;;   (outshine-use-outorg 'org-mobile-pull))

;; ;; C-c C-x RET p	org-mobile-push
;; (defun outshine-mobile-push ()
;;   "Call outorg to trigger `org-mobile-push'."
;;   (interactive)
;;   (outshine-use-outorg 'org-mobile-push))

;; ;; <remap> <backward-paragraph>	org-backward-paragraph
;; ;; <remap> <comment-dwim>		org-comment-dwim
;; ;; <remap> <delete-backward-char>	org-delete-backward-char
;; ;; <remap> <delete-char>		org-delete-char
;; ;; <remap> <forward-paragraph>	org-forward-paragraph
;; ;; <remap> <open-line>		org-open-line
;; ;; <remap> <outline-backward-same-level>
;; ;; 				org-backward-heading-same-level
;; ;; <remap> <outline-demote>	org-demote-subtree
;; ;; <remap> <outline-forward-same-level>
;; ;; 				org-forward-heading-same-level
;; ;; <remap> <outline-insert-heading>
;; ;; 				org-ctrl-c-ret
;; ;; <remap> <outline-mark-subtree>	org-mark-subtree
;; ;; <remap> <outline-promote>	org-promote-subtree
;; ;; <remap> <self-insert-command>	org-self-insert-command
;; ;; <remap> <show-branches>		org-kill-note-or-show-branches
;; ;; <remap> <show-subtree>		org-show-subtree
;; ;; <remap> <transpose-words>	org-transpose-words


;;; Menus and Keybindings

;; FIXME
;; From: Stefan Monnier <monnier@iro.umontreal.ca>
;; Subject: Re: Commands with more than one keybinding in menus
;; Newsgroups: gmane.emacs.help
;; To: help-gnu-emacs@gnu.org
;; Date: Wed, 14 Aug 2013 12:23:12 -0400 (4 minutes, 20 seconds ago)
;; Organization: A noiseless patient Spider

;; > The macro was offered by a user of outshine, I only fiddled around with
;; > it until it worked without errors. It serves its purpose, because
;; > without it a minor-mode, unconditionally defining 'M-[S-]<arrow-key>'
;; > bindings, runs a high risk of breaking major-mode or user settings - I
;; > would not want to do without it.

;; There are a few ways to have your cake and eat it too:
;; - Move the conditional test into the command, so the menu entries are
;;   bound to the same command as the keys.  If you want the menu-entries
;;   to skip the test, then you can do that by checking the event(s) that
;;   triggered the command.
;; - You can use ":keys STRING" in the menu.  This will show "STRING" as
;;   the shortcut without checking if it indeed runs the same command.
;; - You can use dynamic key-bindings, i.e. instead of binding your key to
;;   (lambda () (interactive) (if foo (CMD))), bind it to
;;   (menu-item "" CMD :filter (lambda (cmd) (if foo cmd))).

;;;; Menus
;;;;; Advertise Bindings

(put 'outshine-insert-heading :advertised-binding [M-ret])
(put 'outline-cycle :advertised-binding [?\t])
(put 'outshine-cycle-buffer :advertised-binding [backtab])
(put 'outline-promote :advertised-binding [M-S-left])
(put 'outline-demote :advertised-binding [M-S-right])
(put 'outline-move-subtree-up :advertised-binding [M-S-up])
(put 'outline-move-subtree-down :advertised-binding [M-S-down])
(put 'outline-hide-more :advertised-binding [M-left])
(put 'outline-show-more :advertised-binding [M-right])
(put 'outline-next-visible-header :advertised-binding [M-down])
(put 'outline-previous-visible-header :advertised-binding [M-up])
(put 'show-all :advertised-binding [?\M-# \?M-a])
(put 'outline-up-heading :advertised-binding [?\M-# ?\M-u])
(put 'outorg-edit-as-org :advertised-binding [?\M-# ?\M-#])

;;;;; Define Menu

(easy-menu-define outshine-menu outline-minor-mode-map "Outshine menu"
  '("Outshine"
     ["Cycle Subtree" outline-cycle
      :active (outline-on-heading-p) :keys "<tab>"]
     ["Cycle Buffer" outshine-cycle-buffer t :keys "<backtab>"]
     ["Show More" outline-show-more
      :active (outline-on-heading-p) :keys "M-<right>"]
     ["Hide More" outline-hide-more
      :active (outline-on-heading-p) :keys "M-<left>"]
     ["Show All" show-all t :keys "M-# M-a>"]
     "--"
     ["Insert Heading" outshine-insert-heading t :keys "M-<return>"]
     ["Promote Heading" outline-promote
      :active (outline-on-heading-p) :keys "M-S-<left>"]
     ["Demote Heading" outline-demote
      :active (outline-on-heading-p) :keys "M-S-<right>"]
     ["Move Heading Up" outline-move-heading-up
      :active (outline-on-heading-p) :keys "M-S-<up>"]
     ["Move Heading Down" outline-move-heading-down
      :active (outline-on-heading-p) :keys "M-S-<down>"]
    "--"
     ["Previous Visible Heading" outline-previous-visible-heading
      t :keys "M-<up>"]
     ["Next Visible Heading" outline-next-visible-heading
      t :keys "M-<down>"]
     ["Up Heading" outline-up-heading t]
    "--"
     ["Mark Subtree" outline-mark-subtree t]
     ["Edit As Org" outorg-edit-as-org t]))

;; add "Outshine" menu item

;; (easy-menu-add outshine-menu outline-minor-mode-map)
;; get rid of "Outline" menu item
(define-key outline-minor-mode-map [menu-bar outline] 'undefined)

;;;; Keybindings
;;;;; Principal Keybindings

;; from
;; http://stackoverflow.com/questions/4351044/binding-m-up-m-down-in-emacs-23-1-1
(define-key input-decode-map "\e\eOA" [(meta up)])
(define-key input-decode-map "\e\eOB" [(meta down)])

;;  Adapted from `org-mode' and `outline-mode-easy-bindings'
;; Visibility Cycling
;; (outshine-define-key-with-fallback
;;  outline-minor-mode-map (kbd "<tab>")
;;  (outline-cycle arg) (outline-on-heading-p))

;; (outshine-define-key-with-fallback
;;  outline-minor-mode-map (kbd "TAB")
;;  (outline-cycle arg) (outline-on-heading-p))

(outshine-define-key-with-fallback
 outline-minor-mode-map (kbd "TAB")
 (outline-cycle arg)
 (or
  (and
   (bobp)
   (not (outline-on-heading-p))
   outshine-org-style-global-cycling-at-bob-p)
  (outline-on-heading-p)))

;; works on the console too
(define-key
  outline-minor-mode-map (kbd "M-TAB") 'outshine-cycle-buffer)
;; outline-minor-mode-map (kbd "<backtab>") 'outshine-cycle-buffer)
;; outline-minor-mode-map (kbd "BACKTAB") 'outshine-cycle-buffer)
(outshine-define-key-with-fallback
 outline-minor-mode-map (kbd "M-<left>")
 (outline-hide-more) (outline-on-heading-p))
(outshine-define-key-with-fallback
 outline-minor-mode-map (kbd "M-<right>")
 (outline-show-more) (outline-on-heading-p))
;; Headline Insertion
(outshine-define-key-with-fallback
 ;; outline-minor-mode-map (kbd "M-<return>")
 outline-minor-mode-map (kbd "M-RET")
 (outshine-insert-heading) (outline-on-heading-p))
;; Structure Editing
(outshine-define-key-with-fallback
 outline-minor-mode-map (kbd "M-S-<left>")
 (outline-promote) (outline-on-heading-p))
(outshine-define-key-with-fallback
 outline-minor-mode-map (kbd "M-S-<right>")
 (outline-demote) (outline-on-heading-p))
(outshine-define-key-with-fallback
 outline-minor-mode-map (kbd "M-S-<up>")
 (outline-move-subtree-up) (outline-on-heading-p))
(outshine-define-key-with-fallback
 outline-minor-mode-map (kbd "M-S-<down>")
 (outline-move-subtree-down) (outline-on-heading-p))
;; Motion
(define-key
  ;; outline-minor-mode-map [(meta up)]
  outline-minor-mode-map [M-up]
  ;; outline-minor-mode-map (kbd "M-<up>")
  ;; outline-minor-mode-map (kbd "<M-up>")
  'outline-previous-visible-heading)
(define-key
  ;; outline-minor-mode-map [(meta down)]
  outline-minor-mode-map [M-down]
  ;; outline-minor-mode-map (kbd "M-<down>")
  ;; outline-minor-mode-map (kbd "<M-down>")
  'outline-next-visible-heading)

;;;;; Other Keybindings

;; ;;;;;; [Prefix]

;; ;; Put this in your init.el. The prefix can only be changed before
;; ;; outline (minor) mode is loaded!

;; ;; #+begin_example
;; ;;  (defvar outline-minor-mode-prefix "\M-#")
;; ;; #+end_example

;; ;;;;;; [Subprefix]

;; ;; Set the outline-minor-mode-prefix key in your init-file
;; ;; before loading outline-mode
;; (let ((map (lookup-key outline-minor-mode-map outline-minor-mode-prefix)))
;;   ;; define sub-prefix
;;   ;; (define-key map (kbd "C-v") nil)
;;   (define-key map (kbd "M-+") nil)
;;   ;; (define-key map (kbd "C-x") nil)
;;   (define-key map (kbd "M-#") nil)

;; ;;;;;; [M-# Punctuation]

;;   (define-key map (kbd "#") 'outorg-edit-as-org)
;;   (define-key map (kbd "SPC") 'outshine-table-blank-field)
;;   (define-key map (kbd "!") 'outshine-time-stamp-inactive)
;;   (define-key map (kbd "$") 'outshine-archive-subtree)
;;   (define-key map (kbd "%") 'outshine-mark-ring-push)
;;   (define-key map (kbd "&") 'outshine-mark-ring-goto)
;;   (define-key map (kbd "'") 'outshine-edit-special)
;;   (define-key map (kbd "*") 'outshine-ctrl-c-star)
;;   (define-key map (kbd "+") 'outshine-table-sum)
;;   (define-key map (kbd ",") 'outshine-priority)
;;   (define-key map (kbd "-") 'outshine-ctrl-c-minus)
;;   (define-key map (kbd ".") 'outshine-time-stamp)
;;   ;; (define-key map (kbd "/") 'outshine-sparse-tree)
;;   (define-key map (kbd ":") 'outshine-toggle-fixed-width)
;;   (define-key map (kbd ";") 'outshine-toggle-comment)
;;   (define-key map (kbd "<") 'outshine-date-from-calendar)
;;   (define-key map (kbd "=") 'outshine-table-eval-formula)
;;   (define-key map (kbd ">") 'outshine-goto-calendar)
;;   (define-key map (kbd "?") 'outshine-table-field-info)
;;   (define-key map (kbd "@") 'outshine-mark-subtree)
;;   (define-key map (kbd "\\") 'outshine-match-sparse-tree)
;;   (define-key map (kbd "^") 'outshine-sort-entries)
;;   (define-key map (kbd "`") 'outshine-table-edit-field)
;;   (define-key map (kbd "{") 'outshine-table-toggle-formula-debugger)
;;   (define-key map (kbd "|")
;;     'outshine-table-create-or-convert-from-region)
;;   (define-key map (kbd "}")
;;     'outshine-table-toggle-coordinate-overlays)
;;   (define-key map (kbd "~") 'outshine-table-create-with-table.el)

;; ;;;;;; [M-# Letter]

;;   ;; (outshine-define-key-with-fallback
;;   ;;  outline-minor-mode-map (kbd "J")
;;   ;;  (outline-hide-more) (outline-on-heading-p))
;;   ;; (outshine-define-key-with-fallback
;;   ;;  outline-minor-mode-map (kbd "L")
;;   ;;  (outline-show-more) (outline-on-heading-p))
;;   ;; (define-key map (kbd "I") 'outline-previous-visible-heading)
;;   ;; (define-key map (kbd "K") 'outline-next-visible-heading)

;; ;;;;;; [M-# letter]


;; ;;;;;; [M-# M-Punctuation]

;;   ;; (define-key map (kbd "C-^") 'outshine-up-element)
;;   ;; (define-key map (kbd "M-^") 'outshine-up-element)

;;   ;; (define-key map (kbd "C-_") 'outshine-down-element)
;;   ;; (define-key map (kbd "M-_") 'outshine-down-element)


;;   ;; (define-key map (kbd "C-x C-M-v")
;;   ;;   'outshine-redisplay-inline-images)
;;   (define-key map (kbd "M-# C-M-v")
;;     'outshine-redisplay-inline-images)
;;   ;; (define-key map (kbd "C-x RET g") 'outshine-mobile-pull)
;;   (define-key map (kbd "M-# RET g") 'outshine-mobile-pull)
;;   ;; (define-key map (kbd "C-x RET p") 'outshine-mobile-push)
;;   (define-key map (kbd "M-# RET p") 'outshine-mobile-push)
;;   ;; (define-key map (kbd "C-c C-x RET g") 'outshine-mobile-pull)
;;   ;; (define-key map (kbd "C-c C-x RET p") 'outshine-mobile-push)


;; ;;;;;; [M-# M-letter]

;;   ;; (define-key map (kbd "C-t") 'hide-body)
;;   (define-key map (kbd "M-t") 'hide-body)
;;   ;; (define-key map (kbd "C-a") 'show-all)
;;   (define-key map (kbd "M-a") 'show-all)
;;   ;; (define-key map (kbd "C-c") 'hide-entry)
;;   (define-key map (kbd "M-c") 'hide-entry)
;;   ;; (define-key map (kbd "C-e") 'show-entry)
;;   (define-key map (kbd "M-e") 'show-entry)
;;   ;; (define-key map (kbd "C-l") 'hide-leaves)
;;   (define-key map (kbd "M-l") 'hide-leaves)
;;   ;; (define-key map (kbd "C-k") 'show-branches)
;;   (define-key map (kbd "M-k") 'show-branches)
;;   ;; (define-key map (kbd "C-q") 'outline-hide-sublevels)
;;   (define-key map (kbd "M-q") 'outline-hide-sublevels)
;;   ;; (define-key map (kbd "C-o") 'outline-hide-other)
;;   (define-key map (kbd "M-o") 'outline-hide-other)
;;   ;; (define-key map (kbd "C-u") 'outline-up-heading)
;;   (define-key map (kbd "M-u") 'outline-up-heading)
;;   ;; (define-key map (kbd "C-+") 'outshine-imenu-with-navi-regexp)
;;   ;; (define-key map (kbd "M-+") 'outshine-imenu-with-navi-regexp)
;;   ;; (define-key map (kbd "C-p") 'outshine-imenu)
;;   (define-key map (kbd "M-p") 'outshine-imenu)
;;   ;; USE OUTORG TO CALL ORG
;;   ;; 1st binding for 'C-c' prefix, 2nd for 'M-#' prefix
;;   ;; (define-key map (kbd "C-j") 'outshine-goto)
;;   ;; (define-key map (kbd "M-j") 'outshine-goto)
;;   (define-key map (kbd "M-j") 'outshine-imenu)
;;   ;; (define-key map (kbd "C-o") 'outshine-open-at-point)
;;   (define-key map (kbd "M-o") 'outshine-open-at-point)
;;   ;; (define-key map (kbd "C-a") 'outshine-attach)
;;   (define-key map (kbd "M-a") 'outshine-attach)
;;   ;; (define-key map (kbd "C-c") 'outshine-ctrl-c-ctrl-c)
;;   (define-key map (kbd "M-c") 'outshine-ctrl-c-ctrl-c)
;;   ;; (define-key map (kbd "C-d") 'outshine-deadline)
;;   (define-key map (kbd "M-d") 'outshine-deadline)
;;   ;; (define-key map (kbd "C-e") 'outshine-export-dispatch)
;;   (define-key map (kbd "M-e") 'outshine-export-dispatch)
;;   ;; (define-key map (kbd "C-k")
;;   ;;   'outshine-kill-note-or-show-branches)
;;   (define-key map (kbd "M-k") 'outshine-kill-note-or-show-branches)
;;   ;; (define-key map (kbd "C-l") 'outshine-insert-link)
;;   (define-key map (kbd "M-l") 'outshine-insert-link) ; FIXME
;;   ;; (define-key map (kbd "RET") 'outshine-ctrl-c-ret)
;;   ;; (define-key map (kbd "C-q") 'outshine-set-tags-command)
;;   (define-key map (kbd "M-q") 'outshine-set-tags-command)
;;   ;; (define-key map (kbd "C-r") 'outshine-reveal)
;;   (define-key map (kbd "M-r") 'outshine-reveal)
;;   ;; (define-key map (kbd "C-s") 'outshine-schedule)
;;   (define-key map (kbd "M-s") 'outshine-schedule)
;;   ;; (define-key map (kbd "C-t") 'outshine-todo)
;;   (define-key map (kbd "M-t") 'outshine-todo)
;;   ;; (define-key map (kbd "C-v") 'Prefix Command)
;;   ;; (define-key map (kbd "C-w") 'outshine-refile)
;;   ;; (define-key map (kbd "M-w") 'outshine-refile)
;;   (define-key map (kbd "M-w") 'outshine-imenu)
;;   ;; (define-key map (kbd "C-x") 'Prefix Command)
;;   ;; (define-key map (kbd "C-y") 'outshine-evaluate-time-range)
;;   (define-key map (kbd "M-y") 'outshine-evaluate-time-range)
;;   ;; (define-key map (kbd "C-z") 'outshine-add-note)
;;   (define-key map (kbd "M-z") 'outshine-add-note)
;;   ;; (define-key map (kbd "ESC") 'Prefix Command)
;;   ;; (define-key map (kbd "C-*") 'outshine-list-make-subtree)
;;   (define-key map (kbd "M-*") 'outshine-list-make-subtree)
;;   (define-key map (kbd "C-M-l") 'outshine-insert-all-links)
;;   (define-key map (kbd "M-b") 'outshine-previous-block)
;;   (define-key map (kbd "M-f") 'outshine-next-block)
;;   ;; FIXME overrides keybinding
;;   (define-key map (kbd "M-l") 'outshine-insert-last-stored-link)
;;   ;; C-c M-o		tj/mail-subtree
;;   (define-key map (kbd "M-w") 'outshine-copy)

;;   ;; (define-key map (kbd "C-b")
;;   ;;   'outshine-backward-heading-same-level)
;;   ;; (define-key map (kbd "M-b")
;;   ;;   'outshine-backward-heading-same-level)

;;   ;; (define-key map (kbd "C-f")
;;   ;;   'outshine-forward-heading-same-level)
;;   ;; (define-key map (kbd "M-f")
;;   ;;   'outshine-forward-heading-same-level)


;; ;;;;;; [M-# M-# Punctuation]

;;   (define-key map (kbd "M-# #") 'outshine-update-statistics-cookies)
;;   (define-key map (kbd "M-# +")
;;     'outorg-edit-comments-and-propagate-changes)
;;   ;; (define-key map (kbd "C-x !") 'outshine-reload)
;;   (define-key map (kbd "M-# !") 'outshine-reload)
;;   ;; (define-key map (kbd "C-x [") 'outshine-reftex-citation)
;;   (define-key map (kbd "M-# [") 'outshine-reftex-citation)
;;   ;; (define-key map (kbd "C-x \\")
;;   ;;   'outshine-toggle-pretty-entities)
;;   (define-key map (kbd "M-# \\") 'outshine-toggle-pretty-entities)
;;   ;; (define-key map (kbd "C-x _") 'outshine-timer-stop)
;;   (define-key map (kbd "M-# _") 'outshine-timer-stop)
;;   ;; (define-key map (kbd "C-x ,")
;;   ;;   'outshine-timer-pause-or-continue)
;;   (define-key map (kbd "M-# ,") 'outshine-timer-pause-or-continue)
;;   ;; (define-key map (kbd "C-x -") 'outshine-timer-item)
;;   (define-key map (kbd "M-# -") 'outshine-timer-item)
;;   ;; (define-key map (kbd "C-x .") 'outshine-timer)
;;   (define-key map (kbd "M-# .") 'outshine-timer)
;;   ;; (define-key map (kbd "C-x 0") 'outshine-timer-start)
;;   (define-key map (kbd "M-# 0") 'outshine-timer-start)
;;   ;; (define-key map (kbd "C-x :") 'outshine-timer-cancel-timer)
;;   (define-key map (kbd "M-# :") 'outshine-timer-cancel-timer)
;;   ;; (define-key map (kbd "C-x ;") 'outshine-timer-set-timer)
;;   (define-key map (kbd "M-# ;") 'outshine-timer-set-timer)
;;   ;; (define-key map (kbd "C-x <")
;;   ;;   'outshine-agenda-set-restriction-lock)
;;   (define-key map (kbd "M-# <")
;;     'outshine-agenda-set-restriction-lock)
;;   ;; (define-key map (kbd "C-x >")
;;   ;;   'outshine-agenda-remove-restriction-lock)
;;   (define-key map (kbd "M-# >")
;;     'outshine-agenda-remove-restriction-lock)
;;   ;; (define-key map (kbd "C-x TAB") 'outshine-clock-in)
;;   (define-key map (kbd "M-# TAB") 'outshine-clock-in)

;; ;;;;;; [M-# M-# Letter]

;;   ;; (define-key map (kbd "C-x A")
;;   ;;   'outshine-archive-to-archive-sibling)
;;   (define-key map (kbd "M-# A")
;;     'outshine-archive-to-archive-sibling)
;;   ;; (define-key map (kbd "C-x D") 'outshine-shiftmetadown)
;;   (define-key map (kbd "M-# D") 'outshine-shiftmetadown)
;;   ;; (define-key map (kbd "C-x E") 'outshine-inc-effort)
;;   (define-key map (kbd "M-# E") 'outshine-inc-effort)
;;   ;; (define-key map (kbd "C-x G") 'outshine-feed-goto-inbox)
;;   (define-key map (kbd "M-# G") 'outshine-feed-goto-inbox)
;;   ;; (define-key map (kbd "C-x L") 'outshine-shiftmetaleft)
;;   (define-key map (kbd "M-# L") 'outshine-shiftmetaleft)
;;   ;; (define-key map (kbd "C-x M") 'outshine-insert-todo-heading)
;;   (define-key map (kbd "M-# M") 'outshine-insert-todo-heading)
;;   ;; (define-key map (kbd "C-x P") 'outshine-set-property-and-value)
;;   (define-key map (kbd "M-# P") 'outshine-set-property-and-value)
;;   ;; (define-key map (kbd "C-x R") 'outshine-shiftmetaright)
;;   (define-key map (kbd "M-# R") 'outshine-shiftmetaright)
;;   ;; (define-key map (kbd "C-x U") 'outshine-shiftmetaup)
;;   (define-key map (kbd "M-# U") 'outshine-shiftmetaup)

;; ;;;;;; [M-# M-# letter]

;;   ;; (define-key map (kbd "C-x a") 'outshine-toggle-archive-tag)
;;   (define-key map (kbd "M-# a") 'outshine-toggle-archive-tag)
;;   ;; (define-key map (kbd "C-x b")
;;   ;;   'outshine-tree-to-indirect-buffer)
;;   (define-key map (kbd "M-# b") 'outshine-tree-to-indirect-buffer)
;;   ;; (define-key map (kbd "C-x c")
;;   ;;   'outshine-clone-subtree-with-time-shift)
;;   (define-key map (kbd "M-# c") 'outshine-clone-subtree-with-time-shift)
;;   ;; (define-key map (kbd "C-x d") 'outshine-insert-drawer)
;;   (define-key map (kbd "M-# d") 'outshine-insert-drawer)
;;   ;; (define-key map (kbd "C-x e") 'outshine-set-effort)
;;   (define-key map (kbd "M-# e") 'outshine-set-effort)
;;   ;; (define-key map (kbd "C-x f") 'outshine-footnote-action)
;;   (define-key map (kbd "M-# f") 'outshine-footnote-action)
;;   ;; (define-key map (kbd "C-x g") 'outshine-feed-update-all)
;;   (define-key map (kbd "M-# g") 'outshine-feed-update-all)
;;   ;; (define-key map (kbd "C-x i") 'outshine-insert-columns-dblock)
;;   (define-key map (kbd "M-# i") 'outshine-insert-columns-dblock)
;;   ;; (define-key map (kbd "C-x l") 'outshine-metaleft)
;;   (define-key map (kbd "M-# l") 'outshine-metaleft)
;;   ;; (define-key map (kbd "C-x m") 'outshine-meta-return)
;;   (define-key map (kbd "M-# m") 'outshine-meta-return)
;;   ;; (define-key map (kbd "C-x o")
;;   ;;   'outshine-toggle-ordered-property)
;;   (define-key map (kbd "M-# o") 'outshine-toggle-ordered-property)
;;   ;; (define-key map (kbd "C-x p") 'outshine-set-property)
;;   (define-key map (kbd "M-# p") 'outshine-set-property)
;;   ;; (define-key map (kbd "C-x q") 'outshine-toggle-tags-groups)
;;   (define-key map (kbd "M-# q") 'outshine-toggle-tags-groups)
;;   ;; (define-key map (kbd "C-x r") 'outshine-metaright)
;;   (define-key map (kbd "M-# r") 'outshine-metaright)
;;   ;; (define-key map (kbd "C-x u") 'outshine-metaup)
;;   (define-key map (kbd "M-# u") 'outshine-metaup)
;;   ;; (define-key map (kbd "C-x v") 'outshine-copy-visible)
;;   (define-key map (kbd "M-# v") 'outshine-copy-visible)

;; ;;;;;; [M-# M-# M-letter]

;;   ;; (define-key map (kbd "C-x C-a")
;;   ;;   'outshine-archive-subtree-default)
;;   (define-key map (kbd "M-# M-a") 'outshine-archive-subtree-default)
;;   ;; (define-key map (kbd "C-x C-b") 'outshine-toggle-checkbox)
;;   (define-key map (kbd "M-# M-b") 'outshine-toggle-checkbox)
;;   ;; (define-key map (kbd "C-x C-c") 'outshine-columns)
;;   (define-key map (kbd "M-# M-c") 'outshine-columns)
;;   ;; (define-key map (kbd "C-x C-d") 'outshine-clock-display)
;;   (define-key map (kbd "M-# M-d") 'outshine-clock-display)
;;   ;; (define-key map (kbd "C-x C-f") 'org-emphasize)
;;   (define-key map (kbd "M-# M-f") 'org-emphasize)
;;   ;; (define-key map (kbd "C-x C-j") 'outshine-clock-goto)
;;   (define-key map (kbd "M-# M-j") 'outshine-clock-goto)
;;   ;; (define-key map (kbd "C-x C-l")
;;   ;;   'outshine-preview-latex-fragment)
;;   (define-key map (kbd "M-# M-l") 'outshine-preview-latex-fragment)
;;   ;; (define-key map (kbd "C-x C-n") 'outshine-next-link)
;;   (define-key map (kbd "M-# M-n") 'outshine-next-link)
;;   ;; (define-key map (kbd "C-x C-o") 'outshine-clock-out)
;;   (define-key map (kbd "M-# M-o") 'outshine-clock-out)
;;   ;; (define-key map (kbd "C-x C-p") 'outshine-previous-link)
;;   (define-key map (kbd "M-# M-p") 'outshine-previous-link)
;;   ;; (define-key map (kbd "C-x C-q") 'outshine-clock-cancel)
;;   (define-key map (kbd "M-# M-q") 'outshine-clock-cancel)
;;   ;; (define-key map (kbd "C-x C-r") 'outshine-clock-report)
;;   (define-key map (kbd "M-# M-r") 'outshine-clock-report)
;;   ;; (define-key map (kbd "C-x C-s")
;;   ;;   'outshine-advertized-archive-subtree)
;;   (define-key map (kbd "M-# M-s")
;;     'outshine-advertized-archive-subtree)
;;   ;; (define-key map (kbd "C-x C-t")
;;   ;;   'outshine-toggle-time-stamp-overlays)
;;   (define-key map (kbd "M-# M-t")
;;     'outshine-toggle-time-stamp-overlays)
;;   ;; (define-key map (kbd "C-x C-u") 'outshine-dblock-update)
;;   (define-key map (kbd "M-# M-u") 'outshine-dblock-update)
;;   ;; (define-key map (kbd "C-x C-v") 'outshine-toggle-inline-images)
;;   (define-key map (kbd "M-# M-v") 'outshine-toggle-inline-images)
;;   ;; (define-key map (kbd "C-x C-k") 'outshine-cut-special)
;;   (define-key map (kbd "M-# M-k") 'outshine-cut-special)
;;   ;; (define-key map (kbd "C-x M-w") 'outshine-copy-special)
;;   (define-key map (kbd "M-# M-w") 'outshine-copy-special)
;;   ;; (define-key map (kbd "C-x C-x") 'outshine-clock-in-last)
;;   (define-key map (kbd "M-# M-x") 'outshine-clock-in-last)
;;   ;; (define-key map (kbd "C-x C-y") 'outshine-paste-special)
;;   (define-key map (kbd "M-# M-y") 'outshine-paste-special)
;;   ;; (define-key map (kbd "C-x C-z") 'outshine-resolve-clocks)
;;   (define-key map (kbd "M-# M-z") 'outshine-resolve-clocks)

;; ;;;;;; [M-# M-+ Punctuation]

;;   ;; (define-key map (kbd "C-v TAB")
;;   ;;   'outshine-babel-view-src-block-info)
;;   (define-key map (kbd "M-+ TAB")
;;     'outshine-babel-view-src-block-info)

;; ;;;;;; [M-# M-+ Letter]

;;   ;; (define-key map (kbd "C-v I") 'outshine-babel-view-src-block-info)
;;   (define-key map (kbd "M-+ I") 'outshine-babel-view-src-block-info)

;; ;;;;;; [M-# M-+ letter]

;;   ;; (define-key map (kbd "C-v a") 'outshine-babel-sha1-hash)
;;   (define-key map (kbd "M-+ a") 'outshine-babel-sha1-hash)
;;   ;; (define-key map (kbd "C-v b") 'outshine-babel-execute-buffer)
;;   (define-key map (kbd "M-+ b") 'outshine-babel-execute-buffer)
;;   ;; (define-key map (kbd "C-v c") 'outshine-babel-check-src-block)
;;   (define-key map (kbd "M-+ c") 'outshine-babel-check-src-block)
;;   ;; (define-key map (kbd "C-v d") 'outshine-babel-demarcate-block)
;;   (define-key map (kbd "M-+ d") 'outshine-babel-demarcate-block)
;;   ;; (define-key map (kbd "C-v e") 'outshine-babel-execute-maybe)
;;   (define-key map (kbd "M-+ e") 'outshine-babel-execute-maybe)
;;   ;; (define-key map (kbd "C-v f") 'outshine-babel-tangle-file)
;;   (define-key map (kbd "M-+ f") 'outshine-babel-tangle-file)
;;   ;; (define-key map (kbd "C-v g") 'outshine-babel-goto-named-src-block)
;;   (define-key map (kbd "M-+ g") 'outshine-babel-goto-named-src-block)
;;   ;; (define-key map (kbd "C-v h") 'outshine-babel-describe-bindings)
;;   (define-key map (kbd "M-+ h") 'outshine-babel-describe-bindings)
;;   ;; (define-key map (kbd "C-v i") 'outshine-babel-lob-ingest)
;;   (define-key map (kbd "M-+ i") 'outshine-babel-lob-ingest)
;;   ;; (define-key map (kbd "C-v j") 'outshine-babel-insert-header-arg)
;;   (define-key map (kbd "M-+ j") 'outshine-babel-insert-header-arg)
;;   ;; (define-key map (kbd "C-v k") 'outshine-babel-remove-result-one-or-many)
;;   (define-key map (kbd "M-+ k") 'outshine-babel-remove-result-one-or-many)
;;   ;; (define-key map (kbd "C-v l") 'outshine-babel-load-in-session)
;;   (define-key map (kbd "M-+ l") 'outshine-babel-load-in-session)
;;   ;; (define-key map (kbd "C-v n") 'outshine-babel-next-src-block)
;;   (define-key map (kbd "M-+ n") 'outshine-babel-next-src-block)
;;   ;; (define-key map (kbd "C-v o") 'outshine-babel-open-src-block-result)
;;   (define-key map (kbd "M-+ o") 'outshine-babel-open-src-block-result)
;;   ;; (define-key map (kbd "C-v p") 'outshine-babel-previous-src-block)
;;   (define-key map (kbd "M-+ p") 'outshine-babel-previous-src-block)
;;   ;; (define-key map (kbd "C-v r") 'outshine-babel-goto-named-result)
;;   (define-key map (kbd "M-+ r") 'outshine-babel-goto-named-result)
;;   ;; (define-key map (kbd "C-v s") 'outshine-babel-execute-subtree)
;;   (define-key map (kbd "M-+ s") 'outshine-babel-execute-subtree)
;;   ;; (define-key map (kbd "C-v t") 'outshine-babel-tangle)
;;   (define-key map (kbd "M-+ t") 'outshine-babel-tangle)
;;   ;; (define-key map (kbd "C-v u") 'outshine-babel-goto-src-block-head)
;;   (define-key map (kbd "M-+ u") 'outshine-babel-goto-src-block-head)
;;   ;; (define-key map (kbd "C-v v") 'outshine-babel-expand-src-block)
;;   (define-key map (kbd "M-+ v") 'outshine-babel-expand-src-block)
;;   ;; (define-key map (kbd "C-v x") 'outshine-babel-do-key-sequence-in-edit-buffer)
;;   (define-key map (kbd "M-+ x") 'outshine-babel-do-key-sequence-in-edit-buffer)
;;   ;; (define-key map (kbd "C-v z") 'outshine-babel-switch-to-session-with-code)
;;   (define-key map (kbd "M-+ z") 'outshine-babel-switch-to-session-with-code)

;; ;;;;;; [M-# M-+ M-Punctuation]

;;   ;; (define-key map (kbd "C-v '")
;;   ;;   'outorg-edit-comments-and-propagate-changes)
;;   (define-key map (kbd "M-# M-+")
;;     'outorg-edit-comments-and-propagate-changes)

;; ;;;;;; [M-# M-+ M-letter]

;;   ;; (define-key map (kbd "C-v C-a") 'outshine-babel-sha1-hash)
;;   (define-key map (kbd "M-+ M-a") 'outshine-babel-sha1-hash)
;;   ;; (define-key map (kbd "C-v C-b") 'outshine-babel-execute-buffer)
;;   (define-key map (kbd "M-+ M-b") 'outshine-babel-execute-buffer)
;;   ;; (define-key map (kbd "C-v C-c")
;;   ;;   'outshine-babel-check-src-block)
;;   (define-key map (kbd "M-+ M-c") 'outshine-babel-check-src-block)
;;   ;; (define-key map (kbd "C-v C-d")
;;   ;;   'outshine-babel-demarcate-block)
;;   (define-key map (kbd "M-+ M-d") 'outshine-babel-demarcate-block)
;;   ;; (define-key map (kbd "C-v C-e") 'outshine-babel-execute-maybe)
;;   (define-key map (kbd "M-+ M-e") 'outshine-babel-execute-maybe)
;;   ;; (define-key map (kbd "C-v C-f") 'outshine-babel-tangle-file)
;;   (define-key map (kbd "M-+ M-f") 'outshine-babel-tangle-file)
;;   ;; (define-key map (kbd "C-v C-j")
;;   ;;  'outshine-babel-insert-header-arg)
;;   (define-key map (kbd "M-+ M-j") 'outshine-babel-insert-header-arg)
;;   ;; (define-key map (kbd "C-v C-l") 'outshine-babel-load-in-session)
;;   (define-key map (kbd "M-+ M-l") 'outshine-babel-load-in-session)
;;   ;; (define-key map (kbd "C-v C-n") 'outshine-babel-next-src-block)
;;   (define-key map (kbd "M-+ M-n") 'outshine-babel-next-src-block)
;;   ;; (define-key map (kbd "C-v C-o") 'outshine-babel-open-src-block-result)
;;   (define-key map (kbd "M-+ M-o") 'outshine-babel-open-src-block-result)
;;   ;; (define-key map (kbd "C-v C-p") 'outshine-babel-previous-src-block)
;;   (define-key map (kbd "M-+ M-p") 'outshine-babel-previous-src-block)
;;   ;; (define-key map (kbd "C-v C-r") 'outshine-babel-goto-named-result)
;;   (define-key map (kbd "M-+ M-r") 'outshine-babel-goto-named-result)
;;   ;; (define-key map (kbd "C-v C-s") 'outshine-babel-execute-subtree)
;;   (define-key map (kbd "M-+ M-s") 'outshine-babel-execute-subtree)
;;   ;; (define-key map (kbd "C-v C-t") 'outshine-babel-tangle)
;;   (define-key map (kbd "M-+ M-t") 'outshine-babel-tangle)
;;   ;; (define-key map (kbd "C-v C-u") 'outshine-babel-goto-src-block-head)
;;   (define-key map (kbd "M-+ M-u") 'outshine-babel-goto-src-block-head)
;;   ;; (define-key map (kbd "C-v C-v") 'outshine-babel-expand-src-block)
;;   (define-key map (kbd "M-+ M-v") 'outshine-babel-expand-src-block)
;;   ;; (define-key map (kbd "C-v C-x") 'outshine-babel-do-key-sequence-in-edit-buffer)
;;   (define-key map (kbd "M-+ M-x") 'outshine-babel-do-key-sequence-in-edit-buffer)
;;   ;; (define-key map (kbd "C-v C-z") 'outshine-babel-switch-to-session)
;;   (define-key map (kbd "M-+ M-z") 'outshine-babel-switch-to-session)

;;   ;; (define-key map (kbd "C-v C-M-h") 'outshine-babel-mark-block)
;;   (define-key map (kbd "M-+ C-M-h") 'outshine-babel-mark-block)

;; )

;; ;; (define-key map (kbd "<up>") 'outshine-shiftup)
;; ;; (define-key map (kbd "<down>") 'outshine-shiftdown)
;; ;; C-c C-x <left>	org-shiftcontrolleft
;; ;; C-c C-x <right>      org-shiftcontrolright


;;; Run hooks and provide

(run-hooks 'outshine-hook)

(provide 'outshine)

;; Local Variables:
;; coding: utf-8
;; ispell-local-dictionary: "en_US"
;; indent-tabs-mode: nil
;; End:

;;; outshine.el ends here
