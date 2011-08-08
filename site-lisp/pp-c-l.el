;;; pp-c-l.el --- Display Control-l characters in a pretty way
;; 
;; Filename: pp-c-l.el
;; Description: Display Control-l characters in a buffer in a pretty way
;; Author: Drew Adams
;; Maintainer: Drew Adams
;; Copyright (C) 2007-2011, Drew Adams, all rights reserved.
;; Created: Thu Feb 08 20:28:09 2007
;; Version: 1.0
;; Last-Updated: Tue Jan  4 13:15:37 2011 (-0800)
;;           By: dradams
;;     Update #: 201
;; URL: http://www.emacswiki.org/cgi-bin/wiki/pp-c-l.el
;; Keywords: display, convenience, faces
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;; 
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Commentary: 
;; 
;;  Faces defined here:
;;
;;    `pp^L-highlight'.
;;
;;  User options defined here:
;;
;;    `pp^L-^L-string', `pp^L-^L-string-function',
;;    `pp^L-^L-string-post', `pp^L-^L-string-pre',
;;    `pretty-control-l-mode'.
;;
;;  Commands defined here:
;;
;;    `pp^l', `pretty-control-l-mode', `refresh-pretty-control-l'.
;;
;;  Non-interactive functions defined here:
;;
;;   `pp^L-^L-display-table-entry', `pp^L-make-glyph-code'.
;;
;;
;;  To use this library, add this to your initialization file
;;  (~/.emacs or ~/_emacs):
;;
;;    (require 'pp-c-l)           ; Load this library.
;;
;;  To turn on this mode by default, then either customize option
;;  `pretty-control-l-mode' to non-nil or add this line also to your
;;  init file:
;;
;;    (pretty-control-l-mode 1)   ; Turn on pretty display of `^L'.
;;
;;  For most of the user options defined here, if you change the value
;;  then you will need to re-enter `pretty-control-l-mode', for the
;;  new value to take effect.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Change Log:
;;
;; 2011/01/04 dadams
;;     Removed autoloads: non def* sexps & non-interactive fns.  Added for defalias.
;; 2010/04/28 dadams
;;     Added autoload cookie for pp^L-^L-display-table-entry.  Thx to Peter Galbraith.
;; 2010/04/08 dadams
;;     Added autoload cookies.  Thx to Peter Galbraith.
;; 2009/03/02 dadams
;;     Enhancement by Andrey Paramonov.
;;       pp^L-^L-display-table-entry: Added window argument.
;;       pretty-control-l-mode: Update display table of each window.
;;                              Add/remove refresh to window-configuration-hook.
;;       refresh-pretty-control-l: Just call mode function when turned on.
;; 2009/02/26 dadams
;;     Added: pp^L-^L-string-function, refresh-pretty-control-l.
;;     pp^L-^L-display-table-entry: Use pp^L-^L-string-function if non-nil.
;; 2008/05/02 dadams
;;     pp^L-make-glyph-code: If make-glyph-code exists, use that (alias).
;; 2007/05/28 dadams
;;     pp^L-make-glyph-code: Reported Emacs 23 bug to Emacs.
;;       Fixed to work also with Emacs 23+, per Kenichi Handa's suggestion.  
;; 2007/02/08 dadams
;;     Created.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or
;; (at your option) any later version.
;; 
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;; 
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Code:

;;;;;;;;;;;;;;;;;;;;

;; Convenience function suggested by Kim Storm to emacs-devel@gnu.org, in response to
;; my email 2007-02-05, subject: "cannot understand Elisp manual node Glyphs".
;; Added to Emacs as `make-glyph-code' starting with Emacs 23.
;; The version here works also for Emacs versions before Emacs 23.
;; The constant passed as second arg to lsh must be the same as constant
;; CHARACTERBITS in `src/lisp.h'.
(if (fboundp 'make-glyph-code)
    (defalias 'pp^L-make-glyph-code 'make-glyph-code)
  (defun pp^L-make-glyph-code (char &optional face)
    "Return a glyph code representing char CHAR with face FACE."
    (if face
        (logior char (lsh (face-id face) 19)) ; CHARACTERBITS
      char)))

;;;###autoload
(defgroup Pretty-Control-L nil
  "Options to define pretty display of Control-l (`^L') characters."
  :prefix "pp^L-" :group 'convenience :group 'wp
  :link `(url-link :tag "Send Bug Report"
          ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=pp-c-l.el bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
  :link '(url-link :tag "Other Libraries by Drew"
          "http://www.emacswiki.org/cgi-bin/wiki/DrewsElispLibraries")
  :link '(url-link :tag "Download" "http://www.emacswiki.org/cgi-bin/wiki/pp-c-l.el")
  :link '(url-link :tag "Description"
          "http://www.emacswiki.org/cgi-bin/wiki/PrettyControlL")
  :link '(emacs-commentary-link :tag "Commentary" "pp-c-l"))

;;;###autoload
(defface pp^L-highlight
    (if (> emacs-major-version 21)
        '((((type x w32 mac graphic) (class color))
           (:box (:line-width 3 :style pressed-button)))
          (t (:inverse-video t)))
      '((((type x w32 mac graphic) (class color))
         (:foreground "Blue" :background "DarkSeaGreen1"))
        (t (:inverse-video t))))
  "*Face used to highlight `pp^L-^L-vector'."
  :group 'Pretty-Control-L :group 'faces)

;;;###autoload
(defcustom pp^L-^L-string "          Section (Printable Page)          "
  "*Highlighted string displayed in place of each Control-l (^L) character.
If `pp^L-^L-string-function' is non-nil, then the string that function
returns is used instead of `pp^L-^L-string'."
  :type 'string :group 'Pretty-Control-L)

(defcustom pp^L-^L-string-function nil
  "*Function to produce string displayed in place of a Control-l (^L) char.
The function accepts as argument the window where the ^L is displayed.
If the option value is non-nil, option `pp^L-^L-string' is not used.
You can use this option to have a dynamically defined display string.
For example, this value displays a window-width horizontal line:
  (lambda (win) (make-string (1- (window-width win)) ?_))"
  :type '(choice (const :tag "None" nil) function) :group 'Pretty-Control-L)

(defcustom pp^L-^L-string-pre (if (> emacs-major-version 21) "\n" "")
  "*String displayed just before `pp^L-^L-string'.
This text is not highlighted."
  :type 'string :group 'Pretty-Control-L)

(defcustom pp^L-^L-string-post ""
  "*String displayed just after `pp^L-^L-string'.
This text is not highlighted."
  :type 'string :group 'convenience :group 'wp)

(unless (fboundp 'define-minor-mode)    ; Emacs 20.
  (defcustom pretty-control-l-mode nil
    "*Toggle pretty display of Control-l (`^L') characters.
Setting this variable directly does not take effect;
use either \\[customize] or command `pretty-control-l-mode'."
    :set (lambda (symbol value) (pretty-control-l-mode (if value 1 -1)))
    :initialize 'custom-initialize-default
    :type 'boolean :group 'Pretty-Control-L))

(defun pp^L-^L-display-table-entry (window)
  "Returns the display-table entry for Control-l (`^L') char in WINDOW.
A vector determining how a Control-l character is displayed in WINDOW.
Either a vector of characters or nil.  The characters are displayed in
place of the Control-l character.  nil means `^L' is displayed.

In effect, this concatenates `pp^L-^L-string-pre', `pp^L-^L-string',
and `pp^L-^L-string-post'."
  (vconcat (mapconcat (lambda (c) (list c)) pp^L-^L-string-pre "")
           (mapcar (lambda (c) (pp^L-make-glyph-code c 'pp^L-highlight))
                   (if pp^L-^L-string-function
                       (funcall pp^L-^L-string-function window)
                     pp^L-^L-string))
           (mapconcat (lambda (c) (list c)) pp^L-^L-string-post "")))

;;;###autoload
(defalias 'pp^l 'pretty-control-l-mode)
(if (fboundp 'define-minor-mode)
    ;; Emacs 21 and later.
    ;; We eval this so that even if the library is byte-compiled with Emacs 20,
    ;; loading it into Emacs 21+ will define variable `pretty-control-l-mode'.
    (eval '(define-minor-mode pretty-control-l-mode
            "Toggle pretty display of Control-l (`^L') characters.
With ARG, turn pretty display of `^L' on if and only if ARG is positive."
            :init-value nil :global t :group 'Pretty-Control-L
            :link `(url-link :tag "Send Bug Report"
                    ,(concat "mailto:" "drew.adams" "@" "oracle" ".com?subject=\
pp-c-l.el bug: \
&body=Describe bug here, starting with `emacs -q'.  \
Don't forget to mention your Emacs and library versions."))
            :link '(url-link :tag "Other Libraries by Drew"
                    "http://www.emacswiki.org/cgi-bin/wiki/DrewsElispLibraries")
            :link '(url-link :tag "Download"
                    "http://www.emacswiki.org/cgi-bin/wiki/pp-c-l.el")
            :link '(url-link :tag "Description"
                    "http://www.emacswiki.org/cgi-bin/wiki/PrettyControlL")
            :link '(emacs-commentary-link :tag "Commentary" "pp-c-l")
            (if pretty-control-l-mode
                (add-hook 'window-configuration-change-hook 'refresh-pretty-control-l)
              (remove-hook 'window-configuration-change-hook 'refresh-pretty-control-l))
            (walk-windows 
 	     (lambda (window)
 	       (let ((display-table  (or (window-display-table window)
                                         (make-display-table))))
 		 (aset display-table ?\014 (and pretty-control-l-mode
                                                (pp^L-^L-display-table-entry window)))
 		 (set-window-display-table window display-table)))
             'no-minibuf
             'visible)))

  ;; Emacs 20
  (defun pretty-control-l-mode (&optional arg)
    "Toggle pretty display of Control-l (`^L') characters.
With ARG, turn pretty display of `^L' on if and only if ARG is positive."
    (interactive "P")
    (setq pretty-control-l-mode
          (if arg (> (prefix-numeric-value arg) 0) (not pretty-control-l-mode)))
    (if pretty-control-l-mode
        (add-hook 'window-configuration-change-hook 'refresh-pretty-control-l)
      (remove-hook 'window-configuration-change-hook 'refresh-pretty-control-l))
    (walk-windows 
     (lambda (window)
       (let ((display-table  (or (window-display-table window) (make-display-table))))
         (aset display-table ?\014 (and pretty-control-l-mode
                                        (pp^L-^L-display-table-entry window)))
         (set-window-display-table window display-table)))
     'no-minibuf
     'visible)))

;;;###autoload
(defun refresh-pretty-control-l ()
  "Reinitialize `pretty-control-l-mode', if on, to update the display."
  (interactive)
  (when pretty-control-l-mode (pretty-control-l-mode t)))
  
;;;;;;;;;;;;;;;;;;;;

(provide 'pp-c-l)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; pp-c-l.el ends here
