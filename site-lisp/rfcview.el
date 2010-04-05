;;; rfcview.el -- view IETF RFCs with readability-improved formatting

;; Copyright (C) 2001-2002 Neil W. Van Dyke

;; Author:   Neil W. Van Dyke <neil@neilvandyke.org>
;; Version:  0.5
;; X-URL:    http://www.neilvandyke.org/rfcview/
;; X-CVS:    $Id: rfcview.el,v 1.25 2002/10/16 00:56:23 nwv Exp $ GMT

;; This is free software; you can redistribute it and/or modify it under the
;; terms of the GNU General Public License as published by the Free Software
;; Foundation; either version 2, or (at your option) any later version.  This
;; is distributed in the hope that it will be useful, but without any warranty;
;; without even the implied warranty of merchantability or fitness for a
;; particular purpose.  See the GNU General Public License for more details.
;; You should have received a copy of the GNU General Public License along with
;; GNU Emacs; see the file `COPYING'.  If not, write to the Free Software
;; Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA 02111-1307, USA.

;;; COMMENTARY:

;; Introduction:
;;
;;   For historical reasons, IETF Internet RFCs are required to be in a plain
;;   ASCII text format that's best-suited for sending directly to a 6-lpi
;;   US-letter-size printer.  This makes them suboptimal for viewing on-screen,
;;   as you will be doing for countless hours if you're ever doing network
;;   programming to one of them.  Fortunately, the ASCII format is usually
;;   close to what you, the Emacs zealot, *truly* want -- which is a format
;;   suited to more pleasurably viewing the RFC in Emacs.
;;
;;   The `rfcview' package uses Emacs overlays to add some fontification and
;;   hide the page headers and footers (which it replaces with one-line page
;;   number references that look like "(p.1)", right-justified).  The file is
;;   never modified, and you can see the raw ASCII text by pressing `t'.

;; System Requirements:
;;
;;   The `rfcview.el' package was first written using FSF GNU Emacs 20.7 on a
;;   GNU/Linux system, and is now maintained under Emacs 21.1.  It should work
;;   with recent Emacs versions on Unix variants.  `rfcview.el' has not yet
;;   been tested with the XEmacs fork of Emacs, and I'd welcome any necessary
;;   patches.

;; Installation:
;;
;;   1. Put this `rfcview.el' file somewhere in your Emacs Lisp load path.
;;
;;   2. Add the following lines to your `~/.emacs' file:
;;
;;          (setq auto-mode-alist
;;                (cons '("/rfc[0-9]+\\.txt\\(\\.gz\\)?\\'" . rfcview-mode)
;;                      auto-mode-alist))
;;
;;          (autoload 'rfcview-mode "rfcview" nil t)
;;
;;   3. Restart Emacs.  The next time you visit an RFC file, it should be
;;      displayed prettily using `rfcview-mode'.
;;
;;   4. Optionally, do `M-x rfcview-customize RET' to 

;; Things for the Author to Someday Do (but Probably Not):
;;
;;   * RFC 1700 (STD 2) has unnumbered headings and column-zero body text.  We
;;     don't try to cope right now, but we might assume, e.g., that lines in
;;     all-caps with preceding and succeeding blank lines are headings.
;;
;;   * Hide extraneous blank lines.
;;
;;   * Handle "Table of Contents" heading centered, such as in RFC 1035 and RFC
;;     1157.
;;
;;   * Add hyperlinks to TOC entries.
;;
;;   * Build popup TOC navigation menu.
;;
;;   * Make hyperlinks for bibliographic references.  Display in other-window
;;     vertically-sized to fit only the reference (or min window height).
;;
;;   * Maybe make hyperlinks for urls (but not email addrs).
;;
;;   * Make hyperlinks to referenced RFCs.
;;
;;   * Download RFCs on demand, and cache them.  Probably integrate one of the
;;     existing one or two packages that do this.
;;
;;   * Make an RFCedit mode.
;;
;;   * Handle multi-line heading like:
;;
;;         19.6.1.1 Changes to Simplify Multi-homed Web Servers and Conserve IP
;;         Addresses

;;; CHANGE LOG:

;; [Version 0.5, 15-Oct-2002] Updated email address.
;;
;; [Version 0.4, 26-Feb-2002]
;; * Added `rfcview-use-view-mode-p' feature (suggested by Andreas Fuchs).
;; * Added `.gz' handling to `auto-mode-alist' example for people whose Emacs
;;   auto-decompression features don't strip the compression extension before
;;   doing the `auto-mode-alist' lookup.  (thanks to Andreas Fuchs)
;;
;; [Version 0.3, 22-Feb-2002]
;; * Added autoload cookie (suggested by Daniel Pittman).

;; [Version 0.2, 22-Feb-2002]
;; * Tweaks to support some Internet-Drafts.
;; * In heading patterns, `.' is now optional after single-integer heading
;;   numbers, but remains mandatory after alphabetic (appendix) section
;;   numbers.
;; * Hides carriage return characters (which is already done in some Emacs
;;   configurations, but not in others).

;; [Version 0.1, 17-Mar-2001] Initial release.  Note that there's some
;; hyperlink-related code, but it's not finished, so pretend it's not there --
;; but the static reformatting stuff works and is useful, and I can't spend any
;; more time on this package in the near future, so I'm releasing the package
;; now.

;;; CODE:

(require 'easymenu)

;; Customization:

(defgroup rfcview nil
  "View IETF RFC files with formatting."
  :group  'hypermedia
  :prefix "rfcview-")

(defcustom rfcview-mode-hook nil
  "Hook variable for `rfcview-mode'."
  :group 'rfcview
  :type  'hook)

(defcustom rfcview-use-view-mode-p t
  "If non-nil, start `view-mode' when `rfcview-mode' is started."
  :group 'rfcview
  :type  'boolean)

(defface rfcview-title-face
  '((t (:bold t)))
  "Face used for titles."
  :group 'rfcview)

(defface rfcview-headname-face
  '((t (:bold t :underline t)))
  "Face used for heading names."
  :group 'rfcview)

(defface rfcview-headnum-face
  '((t (:bold t)))
  "Face used for heading numbers."
  :group 'rfcview)

(defface rfcview-headlink-face
  '((t (:foreground "blue"))
    (t (:bold t)))
  "Face used for hyperlinks to headings."
  :group 'rfcview)

(defface rfcview-mouseover-face
  '((((class color)) (:foreground "white" :background "blue" :bold t))
    (t               (:inverse-video t)))
  "Face used for mousing over a hyperlink."
  :group 'rfcview)

(defface rfcview-rfcnum-face
  '((t (:bold t)))
  "Face used for RFC number in the header."
  :group 'rfcview)

(defface rfcview-stdnum-face
  '((t (:bold t)))
  "Face used for STD number in the header."
  :group 'rfcview)

;; Global Variables:

(defvar rfcview-debug-show-hidden-p nil)

(defvar rfcview-mode-map nil)

(defvar rfcview-stock-section-names
  '("abstract"
    "acknowledgement"
    "acknowledgements"
    "acknowledgment"
    "acknowledgments"
    "appendices"
    "author's address"
    "authors' addresses"
    "bibliography"
    "chair's address"
    "copyright notice"
    "copyright statement"
    "editor's address"
    "editors' addresses"
    "full copyright notice"
    "full copyright statement"
    "iesg note"
    "index"
    "introduction"
    "references and bibliography"
    "references"
    "security considerations"
    "status of this memo"
    "table of contents"))

(defvar rfcview-headlink-ovlcat nil)
(defvar rfcview-headname-ovlcat nil)
(defvar rfcview-headnum-ovlcat  nil)
(defvar rfcview-hide-ovlcat     nil)
(defvar rfcview-pagenum-ovlcat  nil)
(defvar rfcview-title-ovlcat    nil)

;; Buffer-Local Variables:

(defvar rfcview-local-heading-alist nil)

;; Functions:

(defun rfcview-add-overlay (begin end category)
  (unless category (error "rfcview-add-overlay nil category"))
  (let ((overlay (make-overlay begin end)))
    (overlay-put overlay 'category category)
    overlay))

;;;###autoload
(defun rfcview-customize ()
  (interactive)
  (customize-group 'rfcview))

(defun rfcview-grok-buffer ()
  (interactive)
  (let ((case-fold-search nil)
        (top-point        (point-min))
        (title-line-point nil))
    
    ;; Clean up everything.
    (rfcview-remove-all-overlays)
    (rfcview-remove-all-markers)
    (make-local-variable 'rfcview-local-heading-alist)
    (setq rfcview-local-heading-alist '())

    ;; Hide any CRs.
    (goto-char (point-min))
    (while (re-search-forward "\r+" nil t)
      (rfcview-hide-region (match-beginning 0) (match-end 0)))

    ;; Add hiding overlay for whitespace at start of file, and set `top-point'
    ;; to just after it.
    (goto-char (point-min))
    (when (re-search-forward "\\`\\([ \t\f]*\r?\n\\)+" nil t)
      (rfcview-hide-region (match-beginning 0) (match-end 0))
      (setq top-point (point)))
    
    ;; Add overlays for page headers and footers.
    (let ((headerfooter-re (concat "^[ \t]*"
                                   "\\(\r?\n\\)"         ; #1
                                   "\\([ \t]*\r?\n\\)*"  ; #2
                                   "[^ \t\f].*\\[Page "
                                   "\\([0-9iIvVxX]+\\)"  ; #3
                                   "\\][ ]*\r?\n?"
                                   "\\("                 ; <#4
                                   "\f"
                                   "\\([ \t]*\r?\n\\)?"  ; #5
                                   "\\("                 ; <#6
                                   "\\("                 ; <#7
                                   "RFC [0-9]+"
                                   "\\|"                 ; |#7
                                   "Internet-Draft[ \t]"
                                   "\\)"                 ; >#7
                                   ".*\r?\n"
                                   "\\([ \t]*\r?\n\\)*"  ; #8
                                   "\\)?"                ; >#6
                                   "\\)?"                ; >#4
                                   )))
      (while (re-search-forward headerfooter-re nil t)
        (rfcview-hide-region (match-end 1) (match-end 0))
        (when (match-beginning 6)
          (let ((overlay  (rfcview-add-overlay (match-beginning 1)
                                               (match-end 1)
                                               'rfcview-pagenum-ovlcat))
                ;; Note: If we wanted to do this right, we would save a marker
                ;;       and then backpatch once we see the next page footer.
                (page-str (format
                           "(p.%s)"
                           (let ((n (string-to-number (match-string 3))))
                             (if (= n 0) "?" (1+ n))))))
            (overlay-put overlay
                         'before-string 
                         (concat (make-string (max (- 79
                                                      (- (match-beginning 1)
                                                         (match-beginning 0))
                                                      (length page-str))
                                                   0)
                                              32)
                                 page-str))))))

    ;; Find the first blank line (which should be between top headers and
    ;; before title), remember point, and hide any extraneous blank lines.
    (goto-char top-point)
    (unless (re-search-forward (concat "^[ \t]*\r?\n"
                                       "\\(\\([ \t]*\r?\n\\)+\\)?")
                               nil t)
      (error "This doesn't seem to be an RFC - no blank line before title."))
    (when (match-beginning 1)
      (rfcview-hide-region (match-beginning 1) (match-end 1)))
    (setq title-line-point (point))

    ;; Add overlay for the RFC number.
    (goto-char top-point)
    (when (let ((case-fold-search t))
            (re-search-forward "^request for comments:[ \t]+\\([0-9X]+\\)"
                               title-line-point t))
      (rfcview-add-overlay (match-beginning 1)
                           (match-end 1)
                           'rfcview-rfcnum-ovlcat))

    ;; Add overlay for the STD number.
    (goto-char top-point)
    (when (let ((case-fold-search nil))
            (re-search-forward "^STD:[ \t]+[0-9]+"
                               title-line-point t))
      (rfcview-add-overlay (match-beginning 0)
                           (match-end 0)
                           'rfcview-stdnum-ovlcat))

    ;; Add overlays to the title line(s).  Note that we currently assume no
    ;; blank lines in the title; otherwise we have to do a perfect job of
    ;; identifying the first non-title line (usually a section heading, which
    ;; some some RFCs make difficult to always identify).
    (goto-char title-line-point)
    (if (re-search-forward (concat
                            "\\([^ \t\f\r\n].*[^ \t\f\r\n]\\)"
                            "\\(\r?\n[ \t]*[^ \t\f\r\n].*[^ \t\f\r\n]\\)*"))
        (rfcview-add-overlay (match-beginning 0)
                             (match-end       0)
                             'rfcview-title-ovlcat))

    ;; Find all the headings.  Add overlays for them, and build
    ;; `rfcview-local-heading-alist'.
    (goto-char title-line-point)
    (let ((case-fold-search t)
          ;; Note: We can't just look for lines that begin in column 0, since
          ;; some RFCs put source code, ASCII-art, description list headings,
          ;; body text, and other stuff in column 0.  So we look for stock
          ;; headings and ones that appear to begin with section numbers.
          (heading-re (concat
                       "^"
                       "\\("                     ; <#1
                       "\\("                     ; <#2 = numbered section
                       "\\("                     ; <#3 = number
                       "\\([0-9]+\\.?\\|[A-Z]\\.\\)" ; #4
                       "\\([0-9]+\\.?\\)*"       ; #5
                       "\\)"                     ; >#3 = number
                       "[ \t]+"
                       "\\([^\r\n]+\\)"          ; #6 = name
                       "\\)"                     ; >#2 = numbered section
                       "\\|"                     ; |#1
                       "\\("                     ; <#7 = stock section
                       "\\("                     ; <#8
                       (mapconcat 'identity rfcview-stock-section-names "\\|")
                       "\\)"                     ; >#8
                       ":?[ \t]*$"
                       "\\)"                     ; >#7 = stock section
                       "\\|"                     ; |#1
                       "\\("                     ; <#9 = lit-appendix
                       
                       "appendix[ \t]+"
                       "\\([A-Z]\\)"             ; #10 = number
                       
                       "\\(\\.\\|:\\|[ \t]+-\\)" ; #11
                       "[ \t]+"
                       "\\([^\r\n]+\\)"          ; #12 = name

                       "\\)"                     ; >#9 = lit-appendix
                       "\\)"                     ; >#1
                       )))
      (while (re-search-forward heading-re nil t)
        (let ((num-match           nil)
              (num-highlight-begin nil)
              (num-highlight-end   nil)
              (name-match          nil))
          ;; Get the match data numbers.
          (cond ((match-beginning 3) (setq num-match  3
                                           name-match 6))
                ((match-beginning 8) (setq num-match  nil
                                           name-match 8))
                ((match-beginning 9) (setq num-match  10
                                           name-match 12)
                 (setq num-highlight-begin (match-beginning 9)
                       num-highlight-end   (match-end       11)))
                (t (error "this should never happen")))

          ;; Add overlays.
          (when num-match
            (rfcview-add-overlay (or num-highlight-begin
                                     (match-beginning num-match))
                                 (or num-highlight-end
                                     (match-end       num-match))
                                 'rfcview-headnum-ovlcat))
          (rfcview-add-overlay (match-beginning name-match)
                               (match-end       name-match)
                               'rfcview-headname-ovlcat)
          ;; Prepend the `rfcview-local-heading-alist' entry.
          (setq rfcview-local-heading-alist
                (let ((num  (when num-match
                              (upcase (match-string-no-properties num-match))))
                      (name (match-string-no-properties name-match)))
                  (cons (cons (downcase (or num name))
                              (vector
                               num
                               name
                               (rfcview-make-marker (match-beginning 0))
                               (rfcview-make-marker (match-end       0))))
                        rfcview-local-heading-alist))))))
    ;; Reverse `rfcview-local-heading-alist'.
    (setq rfcview-local-heading-alist (nreverse rfcview-local-heading-alist))

    ;; Leave the point at the visible top of the buffer.
    (goto-char top-point))
  
  (message "This RFC has been reformatted for viewing in Emacs."))

(defun rfcview-hide-region (start end)
  (rfcview-add-overlay start end 'rfcview-hide-ovlcat))

(defun rfcview-link-add-headlink (start end marker)
  (let ((overlay (rfcview-add-overlay start end 'rfcview-headlink-ovlcat)))
    (overlay-put overlay 'rfcview-link (list 'head marker))
    overlay))

(defun rfcview-link-add-headlink-for (start end key)
  (let ((vec (cdr (member (downcase key) rfcview-local-heading-alist))))
    (when vec
      (rfcview-link-add-headlink start end (aref vec 2)))))

(defun rfcview-make-marker (pt)
  (let ((marker (make-marker)))
    (set-marker marker pt)
    marker))

;;;###autoload
(defun rfcview-mode ()
  "Major mode for viewing Internet RFCs.

http://www.neilvandyke.org/rfcview/

Key bindings:
\\{rfcview-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'rfcview-mode)
  (setq mode-name "RFCview")
  (use-local-map rfcview-mode-map)
  (make-local-variable 'font-lock-defaults)
  (make-local-variable 'rfcview-local-heading-alist)
  (setq font-lock-defaults nil)
  (when rfcview-use-view-mode-p
    (view-mode-enter nil (function (lambda (buf) (rfcview-quit)))))
  (rfcview-grok-buffer)
  (run-hooks 'rfcview-mode-hook))

(defun rfcview-put-alist (symbol alist)
  (mapcar (function (lambda (cell)
                      (put symbol (nth 0 cell) (cdr cell))))
          alist))

(defun rfcview-quit ()
  (interactive)
  (kill-buffer (current-buffer)))

(defun rfcview-remove-all-markers ()
  ;; TODO: 
  )

(defun rfcview-remove-all-overlays ()
  (mapcar (function (lambda (lst)
                      (while lst
                        (delete-overlay (car lst))
                        (setq lst (cdr lst)))))
          (let ((lists (overlay-lists)))
            (list (car lists) (cdr lists)))))

(defun rfcview-textmode ()
  (interactive)
  (rfcview-remove-all-overlays)
  (rfcview-remove-all-markers)
  (text-mode))

;; Keymap and Menu:

(setq rfcview-mode-map
      (let ((km (make-sparse-keymap)))
        (define-key km "t" 'rfcview-textmode)
        (define-key km "q" 'rfcview-quit)
        km))

(easy-menu-define rfcview-mode-menu rfcview-mode-map
  "Menu for RFCview."
  '("RFCview"
    ["Quit"      rfcview-quit     t]
    ["Text Mode" rfcview-textmode t]
    ;;("Table of Contents" ["ERROR!" error t])
    ))

;; Overlay Categories:

(rfcview-put-alist 'rfcview-hide-ovlcat 
                   (if rfcview-debug-show-hidden-p
                       '((face       . region)
                         (intangible . nil)
                         (invisible  . nil))
                     '((face       . default)
                       (intangible . t)
                       (invisible  . t))))

(rfcview-put-alist 'rfcview-headname-ovlcat '((face . rfcview-headname-face)))
(rfcview-put-alist 'rfcview-headnum-ovlcat  '((face . rfcview-headnum-face)))
(rfcview-put-alist 'rfcview-rfcnum-ovlcat   '((face . rfcview-rfcnum-face)))
(rfcview-put-alist 'rfcview-stdnum-ovlcat   '((face . rfcview-stdnum-face)))
(rfcview-put-alist 'rfcview-title-ovlcat    '((face . rfcview-title-face)))

(rfcview-put-alist 'rfcview-headlink-ovlcat
                   '((face       . rfcview-headlink-face)
                     (mouse-face . rfcview-mouseover-face)))

;; End:

(provide 'rfcview)

;;; rfcview.el ends here
