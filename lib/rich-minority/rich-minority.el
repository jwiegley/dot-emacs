;;; rich-minority.el --- Clean-up and Beautify the list of minor-modes.

;; Copyright (C) 2014, 2015 Free Software Foundation, Inc.

;; Author: Artur Malabarba <emacs@endlessparentheses.com>
;; URL: https://github.com/Malabarba/rich-minority
;; Package-Requires: ((cl-lib "0.5"))
;; Version: 1.0.1
;; License: GNU General Public License v3 or newer
;; Keywords: mode-line faces

;;; Commentary:
;;
;;   Emacs package for hiding and/or highlighting the list of minor-modes
;;   in the mode-line.
;;
;;
;; Usage
;; ─────
;;
;;   To activate the enrichment of your minor-modes list, call `M-x
;;   rich-minority-mode', or add this to your init file:
;;
;;   ┌────
;;   │ (rich-minority-mode 1)
;;   └────
;;
;;   By default, this has a couple of small effects (provided as examples)
;;   it is up to you to customize it to your liking with the following
;;   three variables:
;;
;;   `rm-blacklist': List of minor mode names that will be hidden from the
;;                   minor-modes list. Use this to hide *only* a few modes
;;                   that are always active and don’t really contribute
;;                   information.
;;   `rm-whitelist': List of minor mode names that are allowed on the
;;                   minor-modes list. Use this to hide *all but* a few
;;                   modes.
;;   `rm-text-properties': List text properties to apply to each minor-mode
;;                         lighter. For instance, by default we highlight
;;                         `Ovwrt' with a red face, so you always know if
;;                         you’re in `overwrite-mode'.
;;
;;
;; Comparison to Diminish
;; ──────────────────────
;;
;;   Diminish is an established player in the mode-line world, who also
;;   handles the minor-modes list. What can rich-minority /offer in
;;   contrast/?
;;
;;   • rich-minority is more versatile:
;;     1. It accepts *regexps*, instead of having to specify each
;;        minor-mode individually;
;;     2. It also offers a *whitelist* behaviour, in addition to the
;;        blacklist;
;;     3. It supports *highlighting* specific minor-modes with completely
;;        arbitrary text properties.
;;   • rich-minority takes a cleaner, functional approach. It doesn’t hack
;;     into the `minor-mode-alist' variable.
;;
;;   What is rich-minority /missing/?
;;
;;   1. It doesn’t have a quick and simple replacement functionality yet.
;;      Although you can set the `display' property of a minor-mode to
;;      whatever string you want and that will function as a replacement.
;;   2. Its source comments lack [Will Mengarini’s poetry]. :-)
;;
;;
;;   [Will Mengarini’s poetry] http://www.eskimo.com/~seldon/diminish.el
;;
;;
;; Installation
;; ────────────
;;
;;   This package is available fom Melpa, you may install it by calling
;;   `M-x package-install'.


;;; Code:
(require 'cl-lib)

(declare-function lm-version "lisp-mnt")
(defun rm-bug-report ()
  "Opens github issues page in a web browser. Please send any bugs you find.
Please include your Emacs and rich-minority versions."
  (interactive)
  (require 'lisp-mnt)
  (message "Your rm-version is: %s, and your emacs version is: %s.\nPlease include this in your report!"
           (lm-version "rich-minority.el") emacs-version)
  (browse-url "https://github.com/Malabarba/rich-minority/issues/new"))
(defun rm-customize ()
  "Open the customization menu in the `rich-minority' group."
  (interactive)
  (customize-group 'rich-minority t))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Customization variables.
(defcustom rm-blacklist '(" hl-p")
  "List of minor modes you want to hide from the mode-line.

Has three possible values:

- nil: All minor modes are shown in the mode-line (but see also
  `rm-whitelist').

- List of strings: Represents a list of minor mode names that
  will be hidden from the minor-modes list.

- A string: If this variable is set to a single string, this
  string must be a regexp. This regexp will be compared to each
  minor-mode lighter, and those which match are hidden from the
  minor-mode list.

If you'd like to use a list of regexps, simply use something like the following:
    (setq rm-blacklist (mapconcat 'identity list-of-regexps \"\\\\|\"))

Don't forget to start each string with a blank space, as most
minor-mode lighters start with a space."
  :type '(choice (repeat string)
                 (regexp :tag "Regular expression."))
  :group 'rich-minority
  :package-version '(rich-minority . "0.1.1"))
(define-obsolete-variable-alias 'rm-excluded-modes 'rm-blacklist "0.1.1")
(define-obsolete-variable-alias 'rm-hidden-modes 'rm-blacklist "0.1.1")

(defcustom rm-whitelist nil
  "List of minor modes you want to include in the mode-line.

- nil: All minor modes are shown in the mode-line (but see also
  `rm-blacklist').

- List of strings: Represents a list of minor mode names that are
  allowed on the minor-modes list. Any minor-mode whose lighter
  is not in this list will NOT be displayed.

- A string: If this variable is set to a single string, this
  string must be a regexp. This regexp will be compared to each
  minor-mode lighter, and only those which match are displayed on
  the minor-mode list.

If you'd like to use a list of regexps, simply use something like the following:
    (setq rm-whitelist (mapconcat 'identity list-of-regexps \"\\\\|\"))

Don't forget to start each string with a blank space, as most
minor-mode lighters start with a space."
  :type '(choice (repeat string)
                 (regexp :tag "Regular expression."))
  :group 'rich-minority
  :package-version '(rich-minority . "0.1.1"))
(define-obsolete-variable-alias 'rm-included-modes 'rm-whitelist "0.1.1")

(defcustom rm-text-properties
  '(("\\` Ovwrt\\'" 'face 'font-lock-warning-face))
  "Alist of text properties to be applied to minor-mode lighters.
The car of each element must be a regexp, and the cdr must be a
list of text properties.

    (REGEXP PROPERTY-NAME PROPERTY-VALUE ...)

If the regexp matches a minor mode lighter, the text properties
are applied to it. They are tested in order, and search stops at
the first match.

These properties take priority over those defined in
`rm-base-text-properties'."
  :type '(repeat (cons regexp (repeat sexp)))
  :group 'rich-minority
  :package-version '(rich-minority . "0.1"))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Functions and Defvars
(defconst rm--help-echo-bottom
  "Mouse-1: Mode Menu.\nMouse-2: Mode Help.\nMouse-3: Toggle Minor Modes.")

(defvar-local rm--help-echo nil
  "Used to set the help-echo string dynamically.")

(defun rm-format-mode-line-entry (entry)
  "Format an ENTRY of `minor-mode-alist'.
Return a cons of the mode line string and the mode name, or nil
if the mode line string is empty."
  (let ((mode-symbol (car entry))
        (mode-string (format-mode-line entry)))
    (unless (string= mode-string "")
      (cons mode-string mode-symbol))))

;;;###autoload
(defun rm--mode-list-as-string-list ()
  "Return `minor-mode-list' as a simple list of strings."
  (let ((full-list (delq nil (mapcar #'rm-format-mode-line-entry
                                     minor-mode-alist)))
        (spacer (propertize " " 'display '(space :align-to 15))))
    (setq rm--help-echo
          (format "Full list:\n%s\n\n%s"
                  (mapconcat (lambda (pair)
                               (format "   %s%s(%S)"
                                       (car pair) spacer (cdr pair)))
                             full-list "\n")
                  rm--help-echo-bottom))
    (mapcar #'rm--propertize
            (rm--remove-hidden-modes
             (mapcar #'car full-list)))))

(defcustom rm-base-text-properties
  '('help-echo 'rm--help-echo
               'mouse-face 'mode-line-highlight
               'local-map mode-line-minor-mode-keymap)
  "List of text propeties to apply to every minor mode."
  :type '(repeat sexp)
  :group 'rich-minority
  :package-version '(rich-minority . "0.1"))

(defun rm--propertize (mode)
  "Propertize the string MODE according to `rm-text-properties'."
  (if (null (stringp mode))
      `(:propertize ,mode ,@rm-base-text-properties)
    (let ((al rm-text-properties)
          done prop)
      (while (and (null done) al)
        (setq done (pop al))
        (if (string-match (car done) mode)
            (setq prop (cdr done))
          (setq done nil)))
      (eval `(propertize ,mode ,@prop ,@rm-base-text-properties)))))

(defun rm--remove-hidden-modes (li)
  "Remove from LI elements that match `rm-blacklist' or don't match `rm-whitelist'."
  (let ((pred (if (listp rm-blacklist) #'member #'rm--string-match))
        (out li))
    (when rm-blacklist
      (setq out
            (remove nil
                    (mapcar
                     (lambda (x) (unless (and (stringp x)
                                         (funcall pred x rm-blacklist))
                              x))
                     out))))
    (when rm-whitelist
      (setq pred (if (listp rm-whitelist) #'member #'rm--string-match))
      (setq out
            (remove nil
                    (mapcar
                     (lambda (x) (unless (and (stringp x)
                                         (null (funcall pred x rm-whitelist)))
                              x))
                     out))))
    out))

(defun rm--string-match (string regexp)
  "Like `string-match', but arg STRING comes before REGEXP."
  (string-match regexp string))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; minor-mode
(defvar rm--mode-line-construct
  '(:eval (rm--mode-list-as-string-list))
  "Construct used to replace `minor-mode-alist'.")

(defvar rm--warning-absent-element
  "Couldn't find %S inside `mode-line-modes'. If you didn't change it yourself, please file a bug report with M-x rm-bug-report"
  "Warning message used when something wasn't found.")

(defvar rm--backup-construct nil
  "Construct containing `minor-mode-alist' which we removed from the mode-line.")

;;;###autoload
(define-minor-mode rich-minority-mode nil nil " $"
  :global t
  (if rich-minority-mode
      (let ((place (or (member 'minor-mode-alist mode-line-modes)
                       (cl-member-if
                        (lambda (x) (and (listp x)
                                    (equal (car x) :propertize)
                                    (equal (cadr x) '("" minor-mode-alist))))
                        mode-line-modes))))
        (if place
            (progn
              (setq rm--backup-construct (car place))
              (setcar place rm--mode-line-construct))
          (setq rich-minority-mode nil)
          (if (member 'sml/pos-id-separator mode-line-format)
              (message "You don't need to activate rich-minority-mode if you're using smart-mode-line")
            (warn rm--warning-absent-element 'minor-mode-alist))))
    (let ((place (member rm--mode-line-construct mode-line-modes)))
      (if place
          (setcar place rm--backup-construct)
        (warn rm--warning-absent-element rm--mode-line-construct)))))

(provide 'rich-minority)

;;; rich-minority.el ends here

;; Local Variables:
;; nameless-current-name: "rm"
;; End:
