;;; compile+.el --- Extensions to `compile.el'.
;;
;; Filename: compile+.el
;; Description: Extensions to `compile.el'.
;; Author: Drew Adams
;; Maintainer: Drew Adams (concat "drew.adams" "@" "oracle" ".com")
;; Copyright (C) 2004-2015, Drew Adams, all rights reserved.
;; Created: Tue Nov 16 16:38:23 2004
;; Version: 0
;; Package-Requires: ((compile- "0"))
;; Last-Updated: Thu Jan  1 10:28:49 2015 (-0800)
;;           By: dradams
;;     Update #: 930
;; URL: http://www.emacswiki.org/compile+.el
;; Doc URL: http://www.emacswiki.org/GrepPlus
;; Doc URL: http://www.emacswiki.org/CompilationMode
;; Keywords: tools, processes
;; Compatibility: GNU Emacs: 22.x, 23.x, 24.x, 25.x
;;
;; Features that might be required by this library:
;;
;;   `avoid', `compile', `compile-', `fit-frame', `frame-fns',
;;   `misc-fns'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;;    Extensions to `compile.el'.
;;
;;  See also the companion file `compile-.el'.
;;        `compile-.el' should be loaded before `compile.el'.
;;        `compile+.el' should be loaded after `compile.el'.
;;
;;  Put this in your initialization file (`~/.emacs'):
;;
;;    (require 'compile+)
;;
;;  Additional keys are bound here.  Some bindings that would normally
;;  try to modify a compilation mode buffer are unbound, so they are
;;  available for local (Compilation Mode) definition.
;;
;;
;;  ***** NOTE: The following variable defined in `compile.el'
;;              has been REDEFINED HERE:
;;
;;  `compilation-error-regexp-alist-alist' -
;;     Regexp matches whole line, so mouse-over it.
;;
;;
;;  ***** NOTE: The following macro defined in `compile.el'
;;              has been REDEFINED HERE:
;;
;;  `compilation-assq'.
;;
;;
;;  ***** NOTE: The following functions defined in `compile.el'
;;              have been REDEFINED HERE:
;;
;;  `compilation-compat-error-properties',
;;  `compilation-directory-properties', `compilation-goto-locus',
;;  `compilation-internal-error-properties'.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Change Log:
;;
;; 2011/10/03 dadams
;;     Added macros from compile.el: compilation--make-cdrloc, compilation--loc->marker,
;;                                   compilation--file-struct->loc-tree
;;     compilation-directory-properties: Updated Emacs 24 definition.
;; 2011/02/15 dadams
;;     compilation-directory-properties, compilation-internal-error-properties,
;;       compilation--compat-error-properties:
;;         Updated for Emacs 24.
;; 2011/01/03 dadams
;;     Corrected compatibility: Emacs 22+, not 21+.
;; 2009/02/22 dadams
;;     compilation-goto-locus:
;;       Respect until-move value of next-error-highlight (defined in simple+.el).
;; 2007/09/23 dadams
;;     Removed second arg to undefine-killer-commands.
;; 2007/03/15 dadams
;;     Added: compilation-goto-locus (redefinition).
;; 2005/12/16 dadams
;;     Updated to use compilation-mouseover (in compile-.el).
;;       Added: Redefinitions of compilation-error-regexp-alist-alist,
;;              compilation-assq, compilation-compat-error-properties,
;;              compilation-directory-properties
;;              compilation-internal-error-properties.
;;     Added compile-mode-summary and key bindings.
;;     Removed redefinitions of compilation-goto-locus and overlay.
;;       No longer require strings.el.
;; 2004/11/16 dadams
;;     New version for Emacs 21. Old version renamed to compile+20.el.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Code:

(require 'compile-) ;; compilation-mouseover
(require 'compile) ;; compilation-error-regexp-alist-alist, compilation-minor-mode-map

(require 'misc-fns nil t) ;; (no error if not found): undefine-killer-commands


;; Quiet the byte-compiler.
(defvar compilation-debug)
(defvar compilation-enter-directory-face)
(defvar compilation-error-regexp-alist-alist)
(defvar compilation-highlight-overlay)
(defvar compilation-highlight-regexp)
(defvar compilation-leave-directory-face)
(defvar next-error-highlight)
(defvar next-error-highlight-timer)
(defvar next-error-overlay-arrow-position)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-key compilation-minor-mode-map "?" 'describe-mode) ; Defined in `help.el'.
(define-key compilation-minor-mode-map "a" 'first-error)
(define-key compilation-minor-mode-map "b" 'compile-mode-summary)
(define-key compilation-minor-mode-map "c" 'compile)
(define-key compilation-minor-mode-map "d" 'compile-mode-summary)
(define-key compilation-minor-mode-map "e" 'compile-mode-summary)
(define-key compilation-minor-mode-map "f" 'compile-goto-error)
(define-key compilation-minor-mode-map "g" 'recompile)
(define-key compilation-minor-mode-map "h" 'describe-mode) ; Defined in `help.el'.
(define-key compilation-minor-mode-map "i" 'compile-mode-summary)
(define-key compilation-minor-mode-map "j" 'compile-mode-summary)
(define-key compilation-minor-mode-map "k" 'kill-compilation)
(define-key compilation-minor-mode-map "l" 'compile-mode-summary)
(define-key compilation-minor-mode-map "m" 'compile)       ; Make.
(define-key compilation-minor-mode-map "n" 'compilation-next-error)
(define-key compilation-minor-mode-map "o" 'compile-mode-summary)
(define-key compilation-minor-mode-map "p" 'compilation-previous-error)
(define-key compilation-minor-mode-map "q" 'quit-window)
(define-key compilation-minor-mode-map "r" 'recompile)
(define-key compilation-minor-mode-map "s" 'compile-mode-summary)
(define-key compilation-minor-mode-map "t" 'compile-mode-summary)
(define-key compilation-minor-mode-map "u" 'compile-mode-summary)
(define-key compilation-minor-mode-map "v" 'compile-mode-summary)
(define-key compilation-minor-mode-map "w" 'compile-mode-summary)
(define-key compilation-minor-mode-map "x" 'compile-mode-summary)
(define-key compilation-minor-mode-map "y" 'compile-mode-summary)
(define-key compilation-minor-mode-map "z" 'compile-mode-summary)
(define-key compilation-minor-mode-map "A" 'first-error)
(define-key compilation-minor-mode-map "B" 'compile-mode-summary)
(define-key compilation-minor-mode-map "C" 'compile)
(define-key compilation-minor-mode-map "D" 'compile-mode-summary)
(define-key compilation-minor-mode-map "E" 'compile-mode-summary)
(define-key compilation-minor-mode-map "F" 'compile-goto-error)
(define-key compilation-minor-mode-map "G" 'recompile)
(define-key compilation-minor-mode-map "H" 'describe-mode) ; Defined in `help.el'.
(define-key compilation-minor-mode-map "I" 'compile-mode-summary)
(define-key compilation-minor-mode-map "J" 'compile-mode-summary)
(define-key compilation-minor-mode-map "K" 'kill-compilation)
(define-key compilation-minor-mode-map "L" 'compile-mode-summary)
(define-key compilation-minor-mode-map "M" 'compile)       ; Make
(define-key compilation-minor-mode-map "N" 'compilation-next-error)
(define-key compilation-minor-mode-map "O" 'compile-mode-summary)
(define-key compilation-minor-mode-map "P" 'compilation-previous-error)
(define-key compilation-minor-mode-map "Q" 'quit-window)
(define-key compilation-minor-mode-map "R" 'recompile)
(define-key compilation-minor-mode-map "S" 'compile-mode-summary)
(define-key compilation-minor-mode-map "T" 'compile-mode-summary)
(define-key compilation-minor-mode-map "U" 'compile-mode-summary)
(define-key compilation-minor-mode-map "V" 'compile-mode-summary)
(define-key compilation-minor-mode-map "W" 'compile-mode-summary)
(define-key compilation-minor-mode-map "X" 'compile-mode-summary)
(define-key compilation-minor-mode-map "Y" 'compile-mode-summary)
(define-key compilation-minor-mode-map "Z" 'compile-mode-summary)
(define-key compilation-minor-mode-map "{" 'compilation-previous-file)
(define-key compilation-minor-mode-map "}" 'compilation-next-file)



;;; REPLACE ORIGINAL defined in `compile.el'.
;;;
;; Use mouseover on whole line.  Same as original in `compile.el', except for this.
(unless (featurep 'compile+)
  (setq compilation-error-regexp-alist-alist
        (mapcar (lambda (elt) `(,(car elt) ,(concat (cadr elt) ".*") ,@(cddr elt)))
                compilation-error-regexp-alist-alist)))

;; Undefine some bindings that would try to modify a Compilation mode buffer.
;; Their key sequences will then appear to the user as available for local
;; (Compilation Mode) definition.
(when (fboundp 'undefine-killer-commands)
  (undefine-killer-commands compilation-mode-map))

;;;###autoload
(defun compile-mode-summary ()
  "Display brief help message for Compile Mode."
  (interactive)
  (message
   (concat
    (substitute-command-keys
     "\\[describe-mode]= help,  \\[compile-goto-error] & \
\\[compile-mouse-goto-error]= this error,  \\[next-error]= next error,  \
\\[kill-compilation]= kill,  \\[grep]= grep,  \\[compile]= compile,  \
\\[recompile]= recompile"))))



;;; ----------------------------------------------------------------
;;; The rest of this file is redefinitions of standard functions in
;;; `compile.el.  The only changes made have been to replace face
;;; `highlight' by face `compilation-mouseover'.  There is no change
;;; at all in macro `compilation-assq'.
;;; ----------------------------------------------------------------


;;; REPLACE ORIGINAL defined in `compile.el'.
;;; Use face `compilation-mouseover', not `highlight'.
;;;
(if (> emacs-major-version 23)
    ;; Internal function for calculating the text properties of a directory
    ;; change message.  The `compilation-directory' property is important, because it
    ;; is the stack of nested enter-messages.  Relative filenames on the following
    ;; lines are relative to the top of the stack.
    (defun compilation-directory-properties (idx leave)
      (if leave (setq leave (match-end leave)))
      ;; find previous stack, and push onto it, or if `leave' pop it
      (let ((dir (compilation--previous-directory (match-beginning 0))))
        (setq dir (if dir (or (get-text-property (1- dir) 'compilation-directory)
                              (get-text-property dir 'compilation-directory))))
        `(font-lock-face
          ,(if leave compilation-leave-directory-face compilation-enter-directory-face)
          compilation-directory ,(if leave
                                     (or (cdr dir)
                                         '(nil)) ; nil only isn't a property-change
                                     (cons (match-string-no-properties idx) dir))
          ;; Place a `compilation-message' everywhere we change text-properties
          ;; so compilation--remove-properties can know what to remove.
          compilation-message ,(compilation--make-message nil 0 nil)
          mouse-face compilation-mouseover
          keymap compilation-button-map
          help-echo "mouse-2: visit destination directory")))
  ;; Internal function for calculating the text properties of a directory
  ;; change message.  The `directory' property is important, because it is
  ;; the stack of nested enter-messages.  Relative filenames on the following
  ;; lines are relative to the top of the stack.
  (defun compilation-directory-properties (idx leave)
    (if leave (setq leave (match-end leave)))
    ;; find previous stack, and push onto it, or if `leave' pop it
    (let ((dir (previous-single-property-change (point) 'directory)))
      (setq dir (if dir (or (get-text-property (1- dir) 'directory)
                            (get-text-property dir 'directory))))
      `(face ,(if leave
                  compilation-leave-directory-face
                  compilation-enter-directory-face)
             directory ,(if leave
                            (or (cdr dir)
                                '(nil)) ; nil only isn't a property-change
                            (cons (match-string-no-properties idx) dir))
             mouse-face compilation-mouseover
             keymap compilation-button-map
             help-echo "mouse-2: visit current directory"))))


;;; SAME AS ORIGINAL defined in `compile.el'.
;;;
;; Data type `reverse-ordered-alist' retriever.  This function retrieves the
;; KEY element from the ALIST, creating it in the right position if not already
;; present. ALIST structure is
;; '(ANCHOR (KEY1 ...) (KEY2 ...)... (KEYn ALIST ...))
;; ANCHOR is ignored, but necessary so that elements can be inserted.  KEY1
;; may be nil.  The other KEYs are ordered backwards so that growing line
;; numbers can be inserted in front and searching can abort after half the
;; list on average.
(eval-when-compile            ;Don't keep it at runtime if not needed.
  (defmacro compilation-assq (key alist)
    `(let* ((l1 ,alist)
            (l2 (cdr l1)))
       (car (if (if (null ,key)
                    (if l2 (null (caar l2)))
                  (while (if l2 (if (caar l2) (< ,key (caar l2)) t))
                    (setq l1 l2
                          l2 (cdr l1)))
                  (if l2 (eq ,key (caar l2))))
                l2
              (setcdr l1 (cons (list ,key) l2)))))))


;;; REPLACE ORIGINAL defined in `compile.el'.
;;; Respect new value of `until-move' for `next-error-highlight' (from `simple+.el').
;;; Raise frame - especially useful when used with `thumb-frm.el'.
;;;
(defun compilation-goto-locus (msg mk end-mk)
  "Jump to an error corresponding to MSG at MK.
All arguments are markers.  If END-MK is non-nil, mark is set there
and overlay is highlighted between MK and END-MK."
  ;; Show compilation buffer in other window, scrolled to this error.
  (let* ((from-compilation-buffer (eq (window-buffer (selected-window))
                                      (marker-buffer msg)))
         ;; Use an existing window if it is in a visible frame.
         (pre-existing (get-buffer-window (marker-buffer msg) 0))
         (w (if (and from-compilation-buffer pre-existing)
                ;; Calling display-buffer here may end up (partly) hiding
                ;; the error location if the two buffers are in two
                ;; different frames.  So don't do it if it's not necessary.
                pre-existing
              (let ((display-buffer-reuse-frames t)
                    (pop-up-windows t))
                ;; Pop up a window.
                (display-buffer (marker-buffer msg)))))
         (highlight-regexp (with-current-buffer (marker-buffer msg)
                             ;; also do this while we change buffer
                             (compilation-set-window w msg)
                             compilation-highlight-regexp)))
    ;; Ideally, the window-size should be passed to `display-buffer' (via
    ;; something like special-display-buffer) so it's only used when
    ;; creating a new window.
    (unless pre-existing (compilation-set-window-height w))

    (if from-compilation-buffer
        ;; If the compilation buffer window was selected,
        ;; keep the compilation buffer in this window;
        ;; display the source in another window.
        (let ((pop-up-windows t))
          (pop-to-buffer (marker-buffer mk) 'other-window))
      (if (window-dedicated-p (selected-window))
          (pop-to-buffer (marker-buffer mk))
        (switch-to-buffer (marker-buffer mk))))
    ;; If narrowing gets in the way of going to the right place, widen.
    (unless (eq (goto-char mk) (point))
      (widen)
      (goto-char mk))
    (if end-mk
        (push-mark end-mk t)
      (if mark-active (setq mark-active)))
    ;; If hideshow got in the way of
    ;; seeing the right place, open permanently.
    (dolist (ov (overlays-at (point)))
      (when (eq 'hs (overlay-get ov 'invisible))
        (delete-overlay ov)
        (goto-char mk)))

    (when highlight-regexp
      (if (timerp next-error-highlight-timer)
          (cancel-timer next-error-highlight-timer))
      (unless compilation-highlight-overlay
        (setq compilation-highlight-overlay
              (make-overlay (point-min) (point-min)))
        (overlay-put compilation-highlight-overlay 'face 'next-error))
      (with-current-buffer (marker-buffer mk)
        (save-excursion
          (if end-mk (goto-char end-mk) (end-of-line))
          (let ((end (point)))
            (if mk (goto-char mk) (beginning-of-line))
            (if (and (stringp highlight-regexp)
                     (re-search-forward highlight-regexp end t))
                (progn
                  (goto-char (match-beginning 0))
                  (move-overlay compilation-highlight-overlay
                                (match-beginning 0) (match-end 0)
                                (current-buffer)))
              (move-overlay compilation-highlight-overlay
                            (point) end (current-buffer)))
            (if (or (eq next-error-highlight t)
                    (numberp next-error-highlight))
                ;; We want highlighting: delete overlay on next input.
                (add-hook 'pre-command-hook
                          'compilation-goto-locus-delete-o)
              (unless (eq next-error-highlight 'until-move)
                ;; We don't want highlighting: delete overlay now.
                (delete-overlay compilation-highlight-overlay)))
            ;; We want highlighting for a limited time:
            ;; set up a timer to delete it.
            (when (numberp next-error-highlight)
              (setq next-error-highlight-timer
                    (run-at-time next-error-highlight nil
                                 'compilation-goto-locus-delete-o)))))
        (raise-frame)))
    (when (and (eq next-error-highlight 'fringe-arrow))
      ;; We want a fringe arrow (instead of highlighting).
      (setq next-error-overlay-arrow-position
            (copy-marker (line-beginning-position))))))


(defmacro compilation--make-cdrloc (line file-struct marker)
  `(list ,line ,file-struct ,marker nil))
(defmacro compilation--loc->marker (loc) `(nth 3 ,loc))
(defmacro compilation--file-struct->loc-tree (fs) `(cdr ,fs))


;;; REPLACE ORIGINAL defined in `compile.el'.
;;; Use face `compilation-mouseover', not `highlight'.
;;;
(if (> emacs-major-version 23)
    (defun compilation-internal-error-properties (file line end-line col end-col type fmts)
      "Get the meta-info that will be added as text-properties.
LINE, END-LINE, COL, END-COL are integers or nil.
TYPE can be 0, 1, or 2, meaning error, warning, or just info.
FILE should be (FILENAME) or (RELATIVE-FILENAME . DIRNAME) or nil.
FMTS is a list of format specs for transforming the file name.
 (See `compilation-error-regexp-alist'.)"
      (unless file (setq file '("*unknown*")))
      (let* ((file-struct (compilation-get-file-structure file fmts))
             ;; Get first already existing marker (if any has one, all have one).
             ;; Do this first, as the compilation-assq`s may create new nodes.
             (marker-line               ; a line structure
              (cadr (compilation--file-struct->loc-tree file-struct)))
             (marker
              (if marker-line (compilation--loc->marker (cadr marker-line))))
             (compilation-error-screen-columns compilation-error-screen-columns)
             end-marker loc end-loc)
        (if (not (and marker (marker-buffer marker)))
            (setq marker nil)      ; no valid marker for this file
          (setq loc (or line 1))   ; normalize no linenumber to line 1
          (catch 'marker       ; find nearest loc, at least one exists
            (dolist (x (cddr (compilation--file-struct->loc-tree
                              file-struct))) ; Loop over remaining lines.
              (if (> (car x) loc)            ; still bigger
                  (setq marker-line x)
                (if (> (- (or (car marker-line) 1) loc)
                       (- loc (car x)))	; current line is nearer
                    (setq marker-line x))
                (throw 'marker t))))
          (setq marker (compilation--loc->marker (cadr marker-line))
                marker-line (or (car marker-line) 1))
          (with-current-buffer (marker-buffer marker)
            (save-excursion
              (save-restriction
                (widen)
                (goto-char (marker-position marker))
                (when (or end-col end-line)
                  (beginning-of-line (- (or end-line line) marker-line -1))
                  (if (or (null end-col) (< end-col 0))
                      (end-of-line)
                    (compilation-move-to-column
                     end-col compilation-error-screen-columns))
                  (setq end-marker (point-marker)))
                (beginning-of-line (if end-line
                                       (- line end-line -1)
                                     (- loc marker-line -1)))
                (if col
                    (compilation-move-to-column
                     col compilation-error-screen-columns)
                  (forward-to-indentation 0))
                (setq marker (point-marker))))))

        (setq loc (compilation-assq line (compilation--file-struct->loc-tree
                                          file-struct)))
        (setq end-loc
              (if end-line
                  (compilation-assq
                   end-col (compilation-assq
                            end-line (compilation--file-struct->loc-tree
                                      file-struct)))
                (if end-col             ; use same line element
                    (compilation-assq end-col loc))))
        (setq loc (compilation-assq col loc))
        ;; If they are new, make the loc(s) reference the file they point to.
        ;; FIXME-omake: there's a problem with timestamps here: the markers
        ;; relative to which we computed the current `marker' have a timestamp
        ;; almost guaranteed to be different from compilation-buffer-modtime, so if
        ;; we use their timestamp, we'll never use `loc' since the timestamp won't
        ;; match compilation-buffer-modtime, and if we use
        ;; compilation-buffer-modtime then we have different timestamps for
        ;; locations that were computed together, which doesn't make sense either.
        ;; I think this points to a fundamental problem in our approach to the
        ;; "omake -P" problem.  --Stef
        (or (cdr loc)
            (setcdr loc (compilation--make-cdrloc line file-struct marker)))
        (if end-loc
            (or (cdr end-loc)
                (setcdr end-loc
                        (compilation--make-cdrloc (or end-line line) file-struct
                                                  end-marker))))

        ;; Must start with face
        `(font-lock-face ,compilation-message-face
                         compilation-message ,(compilation--make-message loc type end-loc)
                         help-echo ,(if col
                                        "mouse-2: visit this file, line and column"
                                        (if line
                                            "mouse-2: visit this file and line"
                                          "mouse-2: visit this file"))
                         keymap compilation-button-map
                         mouse-face compilation-mouseover)))
  (defun compilation-internal-error-properties
      (file line end-line col end-col type fmts)
    "Get the meta-info that will be added as text-properties.
LINE, END-LINE, COL, END-COL are integers or nil.
TYPE can be 0, 1, or 2, meaning error, warning, or just info.
FILE should be (FILENAME) or (RELATIVE-FILENAME . DIRNAME) or nil.
FMTS is a list of format specs for transforming the file name.
 (See `compilation-error-regexp-alist'.)"
    (unless file (setq file '("*unknown*")))
    (let* ((file-struct (compilation-get-file-structure file fmts))
           ;; Get first already existing marker (if any has one, all have one).
           ;; Do this first, as the compilation-assq`s may create new nodes.
           (marker-line (car (cddr file-struct))) ; a line structure
           (marker (nth 3 (cadr marker-line)))    ; its marker
           (compilation-error-screen-columns compilation-error-screen-columns)
           end-marker loc end-loc)
      (if (not (and marker (marker-buffer marker)))
          (setq marker nil)    ; no valid marker for this file
        (setq loc (or line 1)) ; normalize no linenumber to line 1
        (catch 'marker         ; find nearest loc, at least one exists
          (dolist (x (nthcdr 3 file-struct)) ; loop over remaining lines
            (if (> (car x) loc)              ; still bigger
                (setq marker-line x)
              (if (> (- (or (car marker-line) 1) loc)
                     (- loc (car x)))   ; current line is nearer
                  (setq marker-line x))
              (throw 'marker t))))
        (setq marker (nth 3 (cadr marker-line))
              marker-line (or (car marker-line) 1))
        (with-current-buffer (marker-buffer marker)
          (save-excursion
            (save-restriction
              (widen)
              (goto-char (marker-position marker))
              (when (or end-col end-line)
                (beginning-of-line (- (or end-line line) marker-line -1))
                (if (or (null end-col) (< end-col 0))
                    (end-of-line)
                  (compilation-move-to-column
                   end-col compilation-error-screen-columns))
                (setq end-marker (list (point-marker))))
              (beginning-of-line (if end-line
                                     (- line end-line -1)
                                   (- loc marker-line -1)))
              (if col
                  (compilation-move-to-column
                   col compilation-error-screen-columns)
                (forward-to-indentation 0))
              (setq marker (list (point-marker)))))))

      (setq loc (compilation-assq line (cdr file-struct)))
      (if end-line
          (setq end-loc (compilation-assq end-line (cdr file-struct))
                end-loc (compilation-assq end-col end-loc))
        (if end-col                     ; use same line element
            (setq end-loc (compilation-assq end-col loc))))
      (setq loc (compilation-assq col loc))
      ;; If they are new, make the loc(s) reference the file they point to.
      (or (cdr loc) (setcdr loc `(,line ,file-struct ,@marker)))
      (if end-loc
          (or (cdr end-loc)
              (setcdr end-loc `(,(or end-line line) ,file-struct ,@end-marker))))

      ;; Must start with face
      `(face ,compilation-message-face
             message (,loc ,type ,end-loc)
             ,@(if compilation-debug
                   `(debug (,(assoc (with-no-warnings matcher) font-lock-keywords)
                             ,@(match-data))))
             help-echo ,(if col
                            "mouse-2: visit this file, line and column"
                            (if line
                                "mouse-2: visit this file and line"
                              "mouse-2: visit this file"))
             keymap compilation-button-map
             mouse-face compilation-mouseover))))


;;; REPLACE ORIGINAL defined in `compile.el'.
;;; Use face `compilation-mouseover', not `highlight'.
;;;
;;; Note that they also renamed this function, adding an extra `-'.
;;;
(if (> emacs-major-version 23)
    (defun compilation--compat-error-properties (err)
      "Map old-style error ERR to new-style message."
      ;; Old-style structure is (MARKER (FILE DIR) LINE COL) or
      ;; (MARKER . MARKER).
      (let ((dst (cdr err)))
        (if (markerp dst)
            `(compilation-message ,(compilation--make-message
                                    (cons nil (compilation--make-cdrloc
                                               nil nil dst))
                                    2 nil)
                                  help-echo "mouse-2: visit the source location"
                                  keymap compilation-button-map
                                  mouse-face compilation-mouseover)
          ;; Too difficult to do it by hand: dispatch to the normal code.
          (let* ((file (pop dst))
                 (line (pop dst))
                 (col (pop dst))
                 (filename (pop file))
                 (dirname (pop file))
                 (fmt (pop file)))
            (compilation-internal-error-properties
             (cons filename dirname) line nil col nil 2 fmt)))))
  (defun compilation-compat-error-properties (err)
    "Map old-style error ERR to new-style message."
    ;; Old-style structure is (MARKER (FILE DIR) LINE COL) or
    ;; (MARKER . MARKER).
    (let ((dst (cdr err)))
      (if (markerp dst)
          ;; Must start with a face, for font-lock.
          `(face nil
                 message ,(list (list nil nil nil dst) 2)
                 help-echo "mouse-2: visit the source location"
                 keymap compilation-button-map
                 mouse-face compilation-mouseover)
        ;; Too difficult to do it by hand: dispatch to the normal code.
        (let* ((file (pop dst))
               (line (pop dst))
               (col (pop dst))
               (filename (pop file))
               (dirname (pop file))
               (fmt (pop file)))
          (compilation-internal-error-properties
           (cons filename dirname) line nil col nil 2 fmt))))))

;;;;;;;;;;;;;;;;;;

(provide 'compile+)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; compile+.el ends here
