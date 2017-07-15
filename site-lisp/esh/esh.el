;;; esh.el --- Use Emacs to highlight snippets in LaTeX and HTML documents -*- lexical-binding: t; -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; Package-Requires: ((emacs "24.3"))
;; Package-Version: 0.1
;; Keywords: faces
;; URL: https://github.com/cpitclaudel/esh

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; ESH is an extensible framework for exporting Emacs' syntax highlighting to
;; other languages, and for using Emacs to highlight code snippets embedded in
;; documents.  Its LaTeX backend is a replacement for lstlistings, minted, etc.\
;; that uses Emacs' major-modes to syntax-highlight code blocks in your
;; documents.
;;
;; See URL `https://github.com/cpitclaudel/esh' for usage instructions.

;;; Code:

;; Can't depend on external packages
(require 'color)
(require 'tabify)
(require 'cl-lib)
(require 'esh-intervals)

(defconst esh--script-full-path
  (or (and load-in-progress load-file-name)
      (bound-and-true-p byte-compile-current-file)
      (buffer-file-name))
  "Full path of this script.")

(defconst esh--directory
  (file-name-directory esh--script-full-path)
  "Full path to directory of this script.")

;;; Misc utils

(defmacro esh--interactive-export (&rest body)
  "Temporarily bump GC limits to let ESH do its thing in BODY.
Also kill temp buffers after completing BODY."
  (declare (indent 0) (debug t))
  `(let ((gc-cons-threshold (expt 2 26)))
     (unwind-protect
         (progn ,@body)
       (esh--kill-temp-buffers))))

(defun esh--find-auto-mode (fpath)
  "Find mode for FPATH.
There's no way to use the standard machinery (`set-auto-mode')
without also initializing the mode, which prevents us from
reusing the same buffer to process multiple source files.
Instead, go through `auto-mode-alist' ourselves."
  (let ((mode (assoc-default fpath auto-mode-alist 'string-match)))
    (unless mode
      (error "No mode found for %S in auto-mode-alist" fpath))
    (when (consp mode)
      (error "Unexpected auto-mode spec for %S: %S" mode fpath))
    mode))

(defun esh--filter-cdr (val alist)
  "Remove conses in ALIST whose `cdr' is VAL."
  ;; FIXME phase this out once Emacs 25 is everywhere
  (let ((kept nil))
    (while alist
      (let ((top (pop alist)))
        (when (not (eq (cdr top) val))
          (push top kept))))
    (nreverse kept)))

(defvar esh-name-to-mode-alist nil
  "Alist of block name → mode function.")

(defun esh-add-language (language mode)
  "Teach ESH about a new LANGUAGE, highlighted with MODE.
For example, calling (esh-add-language \"ocaml\" \\='tuareg-mode)
allows you to use `tuareg-mode' for HTML blocks tagged
“src-ocaml”, or for LaTeX blocks tagged “ESH: ocaml”."
  (unless (stringp language)
    (user-error "`esh-add-language': language %S should be a string" language))
  (unless (symbolp mode)
    (user-error "`esh-add-language': mode %S should be a function" mode))
  (add-to-list 'esh-name-to-mode-alist (cons language mode)))

(defun esh--resolve-mode-fn (fn-name)
  "Translate FN-NAME to a function symbol.
Uses `esh-name-to-mode-alist'."
  (or (cdr (assoc fn-name esh-name-to-mode-alist))
      (intern (concat fn-name "-mode"))))

(defun esh-add-keywords (forms &optional how)
  "Pass FORMS and HOW to `font-lock-add-keywords'.
See `font-lock-keywords' for information about the format of
elements of FORMS.  This function does essentially the same thing
as `font-lock-add-keywords', with nicer indentation, a simpler
call signature, and a workaround for an Emacs bug."
  (declare (indent 0))
  ;; Work around Emacs bug #24176
  (setq font-lock-major-mode major-mode)
  (font-lock-add-keywords nil forms how))

(defun esh--remove-final-newline ()
  "Hide last newline of current buffer, if present.
The line is hidden, rather than removed entirely, because it may
have interesting text properties (e.g. `line-height')."
  (goto-char (point-max))
  ;; There may not be a final newline in standalone mode
  (when (eq (char-before) ?\n)
    (put-text-property (1- (point)) (point) 'invisible t)))

(defun esh--insert-file-contents (fname)
  "Like (`insert-file-contents' FNAME), but allow all local variables."
  (let ((enable-local-variables :all))
    (insert-file-contents fname)))

(defun esh--merge-sorted (s1 s2 pred)
  "Merge two lists S1 S2 sorted by PRED."
  (let ((acc nil))
    (while (or s1 s2)
      (cond
       ((and s1 s2)
        (if (funcall pred (car s1) (car s2))
            (push (pop s1) acc)
          (push (pop s2) acc)))
       (s1 (push (pop s1) acc))
       (s2 (push (pop s2) acc))))
    (nreverse acc)))

(defun esh--insert (&rest strs)
  "Insert all non-nil elements of STRS."
  (dolist (str strs)
    (when str
      (insert str))))

(defmacro esh--pp (x)
  "Pretty-print X and its value, then return the value."
  (declare (debug t))
  (let ((xx (make-symbol "x")))
    `(progn (prin1 ',x)
            (princ "\n")
            (let ((,xx ,x))
              (pp ,xx)
              (princ "\n")
              ,xx))))

(defun esh--join (strs sep)
  "Joins STRS with SEP."
  (mapconcat #'identity strs sep))

(defmacro esh--doplist (bindings &rest body)
  "Bind PROP and VAR to pairs in PLIST and run BODY.
BINDINGS should be a list (PROP VAL PLIST).

\(fn (PROP VAL PLIST) BODY...)"
  (declare (indent 1) (debug ((symbolp symbolp form) body)))
  (pcase-let ((plist (make-symbol "plist"))
              (`(,prop ,val ,plist-expr) bindings))
    `(let ((,plist ,plist-expr))
       (while ,plist
         (let ((,prop (pop ,plist))
               (,val (pop ,plist)))
           ,@body)))))

(defun esh--filter-plist (plist props)
  "Remove PROPS from PLIST."
  (let ((filtered nil))
    (esh--doplist (prop val plist)
      (unless (memq prop props)
        (push prop filtered)
        (push val filtered)))
    (nreverse filtered)))

(defun esh--plist-keys (plist)
  "Get the keys of PLIST."
  (let ((keys nil))
    (esh--doplist (k _ plist)
      (push k keys))
    (nreverse keys)))

;;; Copying buffers

(defun esh--number-or-0 (x)
  "Return X if X is a number, 0 otherwise."
  (if (numberp x) x 0))

(defun esh--augment-overlay (ov)
  "Return a list of three values: the priorities of overlay OV, and OV."
  (let ((pr (overlay-get ov 'priority)))
    (if (consp pr)
        (list (esh--number-or-0 (car pr)) (esh--number-or-0 (cdr pr)) ov)
      (list (esh--number-or-0 pr) 0 ov))))

(defun esh--augmented-overlay-< (ov1 ov2)
  "Compare two lists OV1 OV2 produced by `esh--augment-overlay'."
  (or (< (car ov1) (car ov2))
      (and (= (car ov1) (car ov2))
           (< (cadr ov1) (cadr ov2)))))

(defun esh--buffer-overlays (buf)
  "Collects overlays of BUF, in order of increasing priority."
  (let* ((ovs (with-current-buffer buf (overlays-in (point-min) (point-max))))
         (augmented (mapcar #'esh--augment-overlay ovs))
         (sorted (sort augmented #'esh--augmented-overlay-<)))
    (mapcar #'cl-caddr sorted)))

(defconst esh--overlay-specific-props
  '(after-string before-string evaporate isearch-open-invisible
                 isearch-open-invisible-temporary priority window)
  "Properties that only apply to overlays.")

(defun esh--plists-get (prop plist1 plist2)
  "Read property PROP from PLIST1, falling back to PLIST2."
  (let ((mem (plist-member plist1 prop)))
    (if mem (cadr mem) (plist-get plist2 prop))))

(defun esh--commit-overlays (buf)
  "Copy overlays of BUF into current buffer's text properties.
We need to do this, because get-char-text-property considers at
most one overlay."
  (let ((pt-min-diff (- (with-current-buffer buf (point-min)) (point-min))))
    (dolist (ov (esh--buffer-overlays buf))
      (let* ((start (max (point-min) (- (overlay-start ov) pt-min-diff)))
             (end (min (point-max) (- (overlay-end ov) pt-min-diff)))
             (ov-props (overlay-properties ov))
             (cat-props (let ((symbol (plist-get ov-props 'category)))
                          (and symbol (symbol-plist symbol))))
             (before-str (esh--plists-get 'before-string ov-props cat-props))
             (after-str (esh--plists-get 'after-string ov-props cat-props))
             (face (esh--plists-get 'face ov-props cat-props))
             (props (esh--filter-plist (append cat-props ov-props)
                                    (cons 'face esh--overlay-specific-props))))
        (when face
          (font-lock-prepend-text-property start end 'face face))
        (when before-str
          (font-lock-prepend-text-property start end 'esh--before before-str))
        (when after-str
          (font-lock-append-text-property start end 'esh--after after-str))
        (add-text-properties start end props)))))

(defun esh--copy-buffer (buf)
  "Copy contents and overlays of BUF into current buffer."
  (insert-buffer-substring buf)
  (esh--commit-overlays buf)
  (dolist (var '(tab-width buffer-display-table buffer-invisibility-spec))
    (set (make-local-variable var) (buffer-local-value var buf))))

(defmacro esh--with-copy-of-current-buffer (&rest body)
  "Run BODY in a temporary copy of the current buffer."
  (declare (indent 0) (debug t))
  (let ((buf (make-symbol "buf")))
    `(let ((,buf (current-buffer)))
       (with-temp-buffer
         (esh--copy-buffer ,buf)
         ,@body))))

;;; Segmenting buffers

(defun esh--buffer-ranges-from (start prop)
  "Create a stream of buffer ranges from START.
Ranges are pairs of START..END positions in which all characters
have the same value of PROP or, if PROP is nil, of all
properties."
  (let ((ranges nil)
        (end nil))
    (while (setq end (if prop (next-single-property-change start prop)
                       (next-property-change start)))
      (push (cons start end) ranges)
      (setq start end))
    (push (cons start (point-max)) ranges)
    (nreverse ranges)))

(defun esh--buffer-ranges (&optional prop)
  "Create a stream of buffer ranges.
Ranges are pairs of START..END positions in which all characters
have the same value of PROP or, if PROP is nil, of all
properties."
  (esh--buffer-ranges-from 1 prop))

;;; Extracting faces and properties

(defun esh--extract-props (props pos)
  "Read PROPS from POS as an ALIST of (PROP . VAL)."
  (let ((alist nil))
    (esh--doplist (prop val (text-properties-at pos))
      (when (and (memq prop props) val)
        (push (cons prop val) alist)))
    (nreverse alist)))

(defun esh--face-get (face attribute)
  "Read ATTRIBUTE from (potentially anonymous) FACE.
Does not take inheritance into account."
  (cond ((listp face)
         (if (plist-member face attribute)
             (plist-get face attribute)
           'unspecified))
        (t (face-attribute face attribute))))

(defun esh--single-face-attribute (face attribute)
  "Read ATTRIBUTE from (potentially anonymous) FACE.
Takes inheritance into account."
  (let* ((attr (esh--face-get face attribute))
         (rel-p (face-attribute-relative-p attribute attr))
         (inherit (esh--face-get face :inherit)))
    (if (and rel-p
             (not (eq inherit 'default))
             (or (listp inherit) (facep inherit)))
        (let ((merge-with (esh--single-face-attribute inherit attribute)))
          (merge-face-attribute attribute attr merge-with))
      attr)))

(defun esh--faces-attribute (faces attribute)
  "Read ATTRIBUTE from FACES.
Faces is a list of (possibly anonymous) faces."
  (let ((attr 'unspecified))
    (while (and faces (face-attribute-relative-p attribute attr))
      (let ((merge-with (esh--single-face-attribute (pop faces) attribute)))
        (setq attr (merge-face-attribute attribute attr merge-with))))
    attr))

(defun esh--as-list (x)
  "Wrap X in a list, if needed."
  (if (listp x) x (list x)))

(defun esh--faces-at-point (pos)
  "Compute list of faces at POS."
  ;; No need to consider overlay properties here, since they've been converted
  ;; to text properties in previous steps.
  (esh--as-list (get-text-property pos 'face)))

;; Caching this function speeds things up by about 5%
(defun esh--extract-face-attributes (face-attributes faces)
  "Extract FACE-ATTRIBUTES from FACES."
  (esh--filter-cdr 'unspecified
                (mapcar (lambda (attr) (cons attr (esh--faces-attribute faces attr)))
                        face-attributes)))

(defun esh--extract-pos-face-attributes (face-attributes pos)
  "Extract FACE-ATTRIBUTES from POS."
  (let ((faces (esh--faces-at-point pos)))
    (and faces ;; Empty list of faces → no face attributes
         (esh--extract-face-attributes face-attributes faces))))

(defvar-local esh--invisible-replacement-string nil)

(defun esh--glyph-to-string (c)
  "Convert glyph C to char."
  (propertize (char-to-string (glyph-char c)) 'face (glyph-face c)))

(defun esh--invisible-replacement-string ()
  "Compute or return string to display for invisible regions."
  (or esh--invisible-replacement-string
      (setq-local
       esh--invisible-replacement-string
       (mapconcat #'esh--glyph-to-string
                  (or (char-table-extra-slot buffer-display-table 4)
                      (char-table-extra-slot standard-display-table 4)) ""))))

(defun esh--invisible-p (val)
  "Determine whether invisible:VAL makes text invisible.
Returns either nil (not invisible), or a string (the text that
the invisible range is replaced with)."
  (let ((invisible (invisible-p val)))
    (pcase invisible
      (`t "")
      (`nil nil)
      (_ (esh--invisible-replacement-string)))))

;;; Massaging properties

(defun esh--replace-region (from to str prop)
  "Replace FROM .. TO with STR, keeping all props but PROP."
  (let* ((str-keys (esh--plist-keys (text-properties-at 0 str)))
         (plist (esh--filter-plist (text-properties-at from) `(,prop ,@str-keys))))
    (goto-char from)
    (delete-region from to)
    (insert str)
    (add-text-properties from (+ from (length str)) plist)))

(defun esh--parse-composition (components)
  "Translate composition COMPONENTS into a string."
  (let ((chars (list (aref components 0)))
        (nrules (/ (length components) 2)))
    (dotimes (nrule nrules)
      (let* ((rule (aref components (+ 1 (* 2 nrule))))
             (char (aref components (+ 2 (* 2 nrule)))))
        (pcase rule
          (`(Br . Bl) (push char chars))
          (_ (error "Unsupported composition COMPONENTS")))))
    (concat (nreverse chars))))

(defun esh--commit-compositions ()
  "Apply compositions in current buffer.
This replaces each composed string by its composition, forgetting
the original string."
  (pcase-dolist (`(,from . ,to) (nreverse (esh--buffer-ranges 'composition)))
    (let ((comp-data (find-composition from nil nil t)))
      (when comp-data
        (pcase-let* ((`(,_ ,_ ,components ,relative-p ,_ ,_) comp-data)
                     (str (if relative-p (concat components)
                            (esh--parse-composition components))))
          (esh--replace-region from to str '(composition)))))))

(defun esh--commit-replacing-display-specs ()
  "Apply replacing display specs in current buffer."
  (pcase-dolist (`(,from . ,to) (nreverse (esh--buffer-ranges 'display)))
    (let ((display (get-text-property from 'display)))
      (when (stringp display)
        (esh--replace-region from to display 'display)))))

(defun esh--commit-before-strings ()
  "Apply before-string specs in current buffer."
  (pcase-dolist (`(,from . ,_) (nreverse (esh--buffer-ranges 'esh--before)))
    (let ((strs (get-text-property from 'esh--before)))
      (goto-char from)
      (insert (mapconcat #'identity strs "")))))

(defun esh--commit-after-strings ()
  "Apply after-string specs in current buffer."
  (pcase-dolist (`(,from . ,to) (nreverse (esh--buffer-ranges 'esh--after)))
    (let ((strs (get-text-property from 'esh--after)))
      (goto-char to)
      (insert (mapconcat #'identity strs "")))))

(defun esh--commit-specs ()
  "Commit various text properties as concrete text in the buffer."
  (esh--commit-before-strings)
  (esh--commit-after-strings)
  (esh--commit-replacing-display-specs)
  (esh--commit-compositions))

(defun esh--mark-newlines (&optional additional-props)
  "Add `esh--newline' and ADDITIONAL-PROPS text properties to each \\n.
The value of `esh--newline' is either `empty' or `non-empty' (we
need this to add a dummy element on empty lines to prevent LaTeX
from complaining about underful hboxes).  Adding these properties
also makes it easy to group ranges by line, which yields a
significant speedup when processing long files (compared to
putting all lines in one large interval tree)."
  (goto-char (point-min))
  (while (search-forward "\n" nil t)
    ;; (point-at-bol 0) is beginning of previous line
    ;; (match-beginning 0) is end of previous line
    ;; Inclusion of (point) prevents collapsing of adjacent properties
    (let* ((empty (= (point-at-bol 0) (match-beginning 0)))
           (newline (cons (point) (if empty 'empty 'non-empty))))
      (add-text-properties (match-beginning 0) (match-end 0)
                           `(esh--newline ,newline ,@additional-props)))))

(defun esh--translate-invisibility (range)
  "Replace value of `invisible' text property in RANGE by a string.
The string indicates what the corresponding text should be
replaced with.  It is nil if the text should in fact be visible."
  (let* ((alist (cl-caddr range))
         (invisible (assq 'invisible (cl-caddr range))))
    (when invisible
      (let ((repl (esh--invisible-p (cdr invisible))))
        (if repl (setf (cdr invisible) repl)
          (setf (cl-caddr range) (assq-delete-all 'invisible alist)))))))

;;; Constructing a stream of events

(defun esh--annotate-ranges (ranges text-props face-attrs)
  "Annotate each range in RANGES with a property alist.
Returns a list of (START END ALIST); the keys of ALIST are
properties in TEXT-PROPS or face attributes in FACE-ATTRS; its
values are the values of these properties.  START is inclusive;
END is exclusive."
  (let ((acc nil))
    (pcase-dolist (`(,start . ,end) ranges)
      (let* ((props-alist (esh--extract-props text-props start))
             (attrs-alist (esh--extract-pos-face-attributes face-attrs start))
             (merged-alist (nconc attrs-alist props-alist)))
        (push (list start end merged-alist) acc)))
    (nreverse acc)))

(defun esh--ranges-to-events (ranges props)
  "Generate opening and closing events from annotated RANGES.
Each returned element has one of the following forms:
  (\\='open POSITION (PROPERTY . VALUE))
  (\\='close POSITION (PROPERTY . VALUE))
Each PROPERTY is one of PROPS."
  (let ((events nil)
        (prev-alist nil)
        (prev-end nil))
    (pcase-dolist (`(,start ,end ,alist) ranges)
      (let ((break-here (or (assq 'esh--break prev-alist) (assq 'esh--break alist))))
        (dolist (prop props)
          (let ((old (assq prop prev-alist))
                (new (assq prop alist)))
            (unless (and (not break-here) (equal (cdr old) (cdr new)))
              (when old
                (push `(close ,start ,old) events))
              (when new
                (push `(open ,start ,new) events))))))
      (setq prev-end end)
      (setq prev-alist alist))
    (dolist (pair prev-alist)
      (push `(close ,prev-end ,pair) events))
    (nreverse events)))

(defun esh--event-property (event)
  "Read property changed by EVENT."
  (car (nth 2 event)))

;;; Building property trees

(defun esh--events-to-intervals (events ranking)
  "Parse sequence of EVENTS into lists of intervals.
Returns a list of lists suitable for consumption by
`esh-intervals-make-doctree' and containing one entry per
property in RANKING."
  (let ((ints-tbl (make-hash-table :test #'eq)))
    (dolist (property ranking)
      (puthash property nil ints-tbl))
    (dolist (event events)
      (pcase event
        (`(open ,pos ,annot)
         ;; `car' of (gethash … …) becomes a partially constructed interval…
         (push `(,pos nil . ,annot) (gethash (car annot) ints-tbl)))
        (`(close ,pos ,annot)
         ;; …which gets completed here:
         (esh-assert (equal annot (cddr (car (gethash (car annot) ints-tbl)))))
         (setf (cadr (car (gethash (car annot) ints-tbl))) pos))))
    (let ((int-lists nil))
      (dolist (property ranking)
        (push (nreverse (gethash property ints-tbl)) int-lists))
      (nreverse int-lists))))

;;; High-level interface to tree-related code

(defun esh--buffer-to-document-tree
    (text-props face-attrs ranking range-filter merge-annots)
  "Construct a property trees from the current buffer.
TEXT-PROPS and FACE-ATTRS specify which properties to keep track
of.  RANKING ranks all these properties in order of tolerance to
splitting (if a property comes late in this list, ESH will try to
preserve this property's spans when resolving conflicts).
RANGE-FILTER is applied to the list of (annotated) ranges in the
buffer before constructing property trees.  Splitting is needed
because in Emacs text properties can overlap in ways that are not
representable as a tree.  MERGE-ANNOTS: see
`esh-intervals-ints-to-document'."
  (let* ((ranges (esh--buffer-ranges))
         (ann-ranges (esh--annotate-ranges ranges text-props face-attrs)))
    (dolist (range ann-ranges)
      (funcall range-filter range))
    (let* ((events (esh--ranges-to-events ann-ranges ranking))
           (ints (esh--events-to-intervals events ranking))
           (doctree (esh-intervals-make-doctree
                     ints (point-min) (point-max) merge-annots)))
      (esh-intervals-doctree-map-annots #'esh--normalize-suppress-defaults doctree)
      doctree)))

;;; Fontifying

(defun esh--font-lock-ensure ()
  "Wrapper around `font-lock-ensure'."
  (if (fboundp 'font-lock-ensure)
      (font-lock-ensure)
    (with-no-warnings (font-lock-fontify-buffer))))

(defconst esh--missing-mode-template
  (concat ">>> (void-function %S); did you forget to `require'"
          " a dependency, or to restart the server? <<<%s"))

(defun esh--missing-mode-error-msg (mode)
  "Construct an error message about missing MODE."
  (propertize (format esh--missing-mode-template mode "  ")
              'face 'error 'font-lock-face 'error))

(defvar esh--temp-buffers nil
  "Alist of (MODE . BUFFER).
These are temporary buffers, used for highlighting.")

(defun esh--kill-temp-buffers ()
  "Kill buffers in `esh--temp-buffers'."
  (mapc #'kill-buffer (mapcar #'cdr esh--temp-buffers))
  (setq esh--temp-buffers nil))

(defun esh--make-temp-buffer (mode)
  "Get temp buffer for MODE from `esh--temp-buffers'.
If no such buffer exist, create one and add it to BUFFERS.  In
all cases, the buffer is erased, and a message is added to it if
the required mode isn't available."
  (save-match-data
    (let ((buf (cdr (assq mode esh--temp-buffers)))
          (mode-boundp (fboundp mode)))
      (unless buf
        (setq buf (generate-new-buffer " *temp*"))
        (with-current-buffer buf
          (funcall (if mode-boundp mode #'fundamental-mode)))
        (push (cons mode buf) esh--temp-buffers))
      (with-current-buffer buf
        (erase-buffer)
        (unless mode-boundp
          (insert (esh--missing-mode-error-msg mode))))
      buf)))

(defvar esh-pre-highlight-hook nil)
(defvar esh-post-highlight-hook nil) ;; FIXME document these

(defun esh--export-buffer (export-fn)
  "Refontify current buffer, then invoke EXPORT-FN.
EXPORT-FN should do the actual exporting."
  (run-hook-with-args 'esh-pre-highlight-hook)
  (esh--font-lock-ensure)
  (run-hook-with-args 'esh-post-highlight-hook)
  (funcall export-fn))

(defun esh--export-str (str mode-fn export-fn)
  "Fontify STR in a MODE-FN buffer, then invoke EXPORT-FN.
EXPORT-FN should do the actual exporting."
  (with-current-buffer (esh--make-temp-buffer mode-fn)
    (insert str)
    (esh--export-buffer export-fn)))

(defun esh--export-file (source-path export-fn)
  "Fontify contents of SOURCE-PATH, then invoke EXPORT-FN."
  (let ((mode-fn (esh--find-auto-mode source-path)))
    (with-current-buffer (esh--make-temp-buffer mode-fn)
      (esh--insert-file-contents source-path)
      (esh--export-buffer export-fn))))

;;; Cleaning up face attributes and text properties

(defun esh--normalize-color (color)
  "Return COLOR as a hex string.
`color-rgb-to-hex', used to work fine, until it got broken in
7b00e956b485d8ade03c870cbdd0ae086348737b."
  (unless (member color '("unspecified-fg" "unspecified-bg" "" nil))
    (upcase (if (= (aref color 0) ?#)
                (substring color 1)
              (pcase-let ((`(,r ,g ,b) (color-name-to-rgb color)))
                (format "%02x%02x%02x" (* 255 r) (* 255 g) (* 255 b)))))))

(defun esh--normalize-underline (underline)
  "Normalize UNDERLINE."
  (pcase underline
    (`nil nil)
    (`t '(nil . line))
    ((pred stringp) `(,(esh--normalize-color underline) . line))
    ((pred listp) `(,(esh--normalize-color (plist-get underline :color)) .
                    ,(or (plist-get underline :style) 'line)))
    (_ (error "Unexpected underline %S" underline))))

(defun esh--normalize-weight (weight)
  "Normalize WEIGHT."
  (pcase weight
    ((or `thin `ultralight `ultra-light) 100)
    ((or `extralight `extra-light) 200)
    ((or `light) 300)
    ((or `demilight `semilight `semi-light `book) 400)
    ((or `normal `medium `regular) 500)
    ((or `demi `demibold `semibold `semi-bold) 600)
    ((or `bold) 700)
    ((or `extrabold `extra-bold `black) 800)
    ((or `ultrabold `ultra-bold) 900)
    (_ (error "Unexpected weight %S" weight))))

(defun esh--normalize-height (height)
  "Normalize HEIGHT to a relative (float) height."
  (let* ((default-height (face-attribute 'default :height))
         (height (merge-face-attribute :height height default-height)))
    (unless (eq height default-height)
      (/ height (float default-height)))))

(defun esh--normalize-slant (slant)
  "Normalize SLANT."
  (pcase slant
    ((or `italic `oblique `normal) slant)
    (_ (error "Unexpected slant %S" slant))))

(defun esh--normalize-box (box)
  "Normalize face attribute BOX.
Numeric values are undocumented, but `face-attribute' sometimes
returns 1 instead of t."
  (pcase box
    (`nil nil)
    (`t `(1 nil nil))
    ((pred stringp) `(1 ,(esh--normalize-color box) nil))
    ((pred numberp) `(,box nil nil))
    ((pred listp) `(,(or (plist-get box :line-width) 1)
                    ,(esh--normalize-color (plist-get box :color))
                    ,(plist-get box :style)))
    (_ (error "Unexpected box %S" box))))

(defun esh--normalize-attribute (property value)
  "Normalize VALUE of PROPERTY."
  (pcase property
    (:foreground (esh--normalize-color value))
    (:background (esh--normalize-color value))
    (:underline (esh--normalize-underline value))
    (:weight (esh--normalize-weight value))
    (:height (esh--normalize-height value))
    (:slant (esh--normalize-slant value))
    (:box (esh--normalize-box value))
    (_ value)))

(defun esh--normalize-suppress-defaults (annotation)
  "Normalize VALUE of PROPERTY (both in ANNOTATION).
`:foreground' and `:background' values that match the `default'
face are suppressed.

\(fn (PROPERTY . VALUE))"
  (pcase-let ((`(,property . ,value) annotation))
    (setq value (esh--normalize-attribute property value))
    (unless (and (memq property '(:foreground :background))
                 (let* ((default (face-attribute 'default property)))
                   (equal value (esh--normalize-attribute property default))))
      (cons property value))))

(defun esh--normalize-defaults (annotation)
  "Normalize the pair ANNOTATION of the `default' face.
Useful when exporting the properties of the default face,
e.g. when rendering a buffer as HTML, htmlfontify-style.

\(fn (PROPERTY . VALUE))"
  (pcase-let ((`(,property . ,value) annotation))
    (unless (eq property :height)
      (setq value (esh--normalize-attribute property value)))
    (unless (equal value (pcase property
                           (:weight 500)
                           (:slant 'normal)))
      (cons property value))))

;;; Producing LaTeX

(defconst esh--latex-props
  '(display invisible line-height esh--newline esh--break))
(defconst esh--latex-face-attrs
  '(:underline :background :foreground :weight :slant :box :height))

(defconst esh--latex-priorities
  `(;; Fine to split
    ,@'(esh--break line-height :underline :foreground :weight :height :background)
    ;; Should not split
    ,@'(:slant :box display esh--newline invisible))
  "Priority order for text properties in LaTeX export.
See `esh--resolve-event-conflicts'.")

(eval-and-compile
  (defconst esh--latex-specials
    '(;; Special characters
      (?$ . "\\$") (?% . "\\%") (?& . "\\&")
      (?{ . "\\{") (?} . "\\}") (?_ . "\\_") (?# . "\\#")
      ;; http://tex.stackexchange.com/questions/67997/
      (?\\ . "\\textbackslash{}") (?^ . "\\textasciicircum{}")
      (?~ . "\\textasciitilde{}")
      ;; A few ligatures
      (?` . "{`}") (?' . "{'}") (?< . "{<}") (?> . "{>}")
      ;; Characters that behave differently in inline and block modes
      (?\s . "\\ESHSpace{}") (?- . "\\ESHDash{}"))))

(defconst esh--latex-specials-re
  (eval-when-compile
    (regexp-opt-charset (mapcar #'car esh--latex-specials))))

(defconst esh--latex-specials-vector
  (eval-when-compile
    (let* ((max-idx (apply #'max (mapcar #'car esh--latex-specials)))
           (vect (make-vector (1+ max-idx) nil)))
      (pcase-dolist (`(,from . ,to) esh--latex-specials)
        (aset vect from to))
      vect)))

(defun esh--latex-substitute-specials (beg)
  "Escape LaTeX specials in BEG .. `point-max'."
  (goto-char beg)
  (while (re-search-forward esh--latex-specials-re nil t)
    (let ((special (char-after (match-beginning 0))))
      (replace-match (aref esh--latex-specials-vector special) t t))))

(defvar esh--latex-escape-alist nil
  "Alist of additional ‘char → LaTeX string’ mappings.")

(defun esh-latex-add-unicode-substitution (char-str latex-cmd)
  "Register an additional ‘unicode char → LaTeX command’ mapping.
CHAR-STR is a one-character string; LATEX-CMD is a latex command."
  (unless (and (stringp char-str) (eq (length char-str) 1))
    (user-error "%S: %S should be a one-character string"
                'esh-latex-add-unicode-substitution char-str))
  (add-to-list 'esh--latex-escape-alist (cons (aref char-str 0) latex-cmd)))

(defun esh--latex-escape-1 (char)
  "Escape CHAR for use with pdfLaTeX."
  (unless (featurep 'esh-latex-escape)
    (load-file (expand-file-name "esh-latex-escape.el" esh--directory)))
  (or (cdr (assq char esh--latex-escape-alist))
      (let ((repl (gethash char (with-no-warnings esh-latex-escape-table))))
        (and repl (format "\\ESHMathSymbol{%s}" repl)))))

(defun esh--latex-escape-unicode-char (c)
  "Replace character C with an equivalent LaTeX command."
  (let* ((translation (esh--latex-escape-1 c)))
    (unless translation
      (error "No LaTeX equivalent found for %S.
Use (esh-latex-add-unicode-substitution %S \"\\someCommand\") to add one" c c))
    (format "\\ESHUnicodeSubstitution{%s}" translation)))

(defun esh--latex-wrap-special-char (char)
  "Wrap CHAR in \\ESHSpecialChar{…}."
  (format "\\ESHSpecialChar{%c}" char))

(defvar esh-substitute-unicode-symbols nil
  "If non-nil, attempt to substitute Unicode symbols in code blocks.
Symbols are replaced by their closest LaTeX equivalent.  This
option is most useful with pdfLaTeX; with XeLaTeX or LuaLaTeX, it
should probably be turned off (customize \\ESHFallbackFont
instead).")

(defun esh--latex-wrap-non-ascii (beg)
  "Wrap non-ASCII characters in BEG .. `point-max'.
If `esh-substitute-unicode-symbols' is nil, wrap non-ASCII characters into
\\ESHSpecialChar{}.  Otherwise, replace them by their LaTeX equivalents
and wrap them in \\ESHUnicodeSubstitution{}."
  ;; TODO benchmark against trivial loop
  (let* ((range "[^\000-\177]")
         (fun (if esh-substitute-unicode-symbols
                  #'esh--latex-escape-unicode-char
                #'esh--latex-wrap-special-char)))
    (goto-char beg)
    (while (re-search-forward range nil t)
      (replace-match (funcall fun (char-after (match-beginning 0))) t t))))

(defun esh--mark-non-ascii ()
  "Tag non-ASCII characters of current buffer.
Puts text property `non-ascii' on non-ascii characters."
  (goto-char (point-min))
  (while (re-search-forward "[^\000-\177]" nil t)
    ;; Need property values to be distinct, hence (point)
    (put-text-property (match-beginning 0) (match-end 0) 'non-ascii (point))))

(defun esh--latex-range-filter (range)
  "Filter properties of RANGE.
Remove most of the properties on ranges marked with
`esh--newline' (keep only `invisible' and `line-height'
properties), and remove `line-height' properties on others."
  (esh--translate-invisibility range)
  (let ((alist (cl-caddr range)))
    (cond
     ((assq 'esh--newline alist)
      (let ((new-alist nil))
        (dolist (pair alist)
          (when (memq (car pair) '(invisible line-height esh--newline esh--break))
            (push pair new-alist)))
        (setf (cl-caddr range) new-alist)))
     ((assq 'line-height alist)
      (setf (cl-caddr range) (assq-delete-all 'line-height alist))))))

(defvar esh--latex-source-buffer-for-export nil
  "Buffer that text nodes point to.")

(defun esh--latex-insert-substituted (str)
  "Insert STR, escaped for LaTeX.
Point must be at end of buffer."
  (let ((pt (point)))
    (insert str)
    (esh--latex-substitute-specials pt)
    (esh--latex-wrap-non-ascii pt)
    (goto-char (point-max))))

(defun esh--latex-export-plain-text (start end)
  "Insert escaped text from range START..END.
Text is read from `esh--latex-source-buffer-for-export'.  Point
must be at end of buffer."
  (esh--latex-insert-substituted
   (with-current-buffer esh--latex-source-buffer-for-export
     (buffer-substring-no-properties start end))))

(defun esh--latex-export-subtrees (l r trees)
  "Export TREES to LaTeX.
L .. R is the range covered by TREES; if TREES is nil, this
function exports a plain text range."
  (if (null trees) (esh--latex-export-plain-text l r)
    (dolist (tree trees)
      (esh--latex-export-doctree tree))))

(defun esh--latex-export-wrapped (before l r trees after)
  "Export TREES, wrapped in BEFORE and AFTER.
L .. R is the range covered by TREES."
  (insert before)
  (esh--latex-export-subtrees l r trees)
  (insert after))

(defun esh--latex-export-wrapped-if (val before-fmt l r trees after)
  "Export TREES, possibly wrapped.
If VAL is non-nil, wrap SUBTREES in (format BEFORE-FMT VAL) and
AFTER.  L .. R is the range covered by TREES."
  (declare (indent 1))
  (if (null val)
      (esh--latex-export-subtrees l r trees)
    (esh--latex-export-wrapped (format before-fmt val) l r trees after)))

(defun esh--latex-export-doctree-1 (property val l r subtrees)
  "Export SUBTREES wrapped in a LaTeX implementation of PROPERTY: VAL.
L .. R is the range covered by SUBTREES (if SUBTREES is nil, then
PROPERTY and VAL apply directly to a text range)."
  (pcase property
    (:foreground
     (esh--latex-export-wrapped-if val
       "\\textcolor[HTML]{%s}{" l r subtrees "}"))
    (:background
     ;; FIXME: Force all lines to have the the same height?
     ;; Could use \\vphantom{'g}\\smash{…}
     (esh--latex-export-wrapped-if val
       "\\ESHColorBox{%s}{" l r subtrees "}"))
    (:weight
     (esh--latex-export-wrapped
      (cond
       ((< val 500) "\\ESHWeightLight{")
       ((> val 500) "\\ESHWeightBold{")
       (t "\\ESHWeightRegular{"))
      l r subtrees "}"))
    (:height
     (esh--latex-export-wrapped-if val
       "\\textscale{%0.2g}{" l r subtrees "}"))
    (:slant
     (esh--latex-export-wrapped
      (pcase val
        (`italic "\\ESHSlantItalic{")
        (`oblique "\\ESHSlantOblique{")
        (`normal "\\ESHSlantNormal{"))
      l r subtrees "}"))
    (:underline
     (esh--latex-export-wrapped
      (pcase val
        (`(,color . ,type)
         ;; There are subtle spacing issues with \\ESHUnder, so don't
         ;; use it unless the underline needs to be colored.
         (let* ((prefix (if color "\\ESHUnder" "\\u"))
                (command (format "%s%S" prefix type))
                (arg (if color (format "{\\color[HTML]{%s}}" color) "")))
           (format "%s%s{" command arg))))
      l r subtrees "}"))
    (:box
     (esh--latex-export-wrapped
      (pcase val
        (`(,line-width ,color ,style)
         (unless (eq style nil)
           (error "Unsupported box style %S" style))
         (format "\\ESHBox{%s}{%.2fpt}{" (or color ".") (abs line-width)))
        (_ (error "Unexpected box %S" val)))
      l r subtrees "}"))
    (`display
     (pcase val
       (`(raise ,amount)
        (esh--latex-export-wrapped-if amount
          "\\ESHRaise{%.2f}{" l r subtrees "}"))
       (_ (error "Unexpected display property %S" val))))
    (`invisible
     (when val (insert val)))
    (`line-height
     (unless (floatp val)
       (error "Unexpected line-height property %S" val))
     (esh--latex-export-wrapped-if val
       "\\ESHStrut{%.2g}" l r subtrees ""))
    (`esh--newline
     ;; Add an mbox to prevent TeX from complaining about underfull boxes.
     (esh--latex-export-wrapped-if (eq (cdr val) 'empty)
       "\\mbox{}" l r subtrees ""))
    (`esh--break (esh--latex-export-subtrees l r subtrees))
    (_ (error "Unexpected property %S" property))))

(defun esh--latex-export-doctree (doctree)
  "Export DOCTREE to LaTeX."
  (pcase (esh-intervals-int-annot doctree)
    (`(,prop . ,val) ;; FIXME what happens if val is nil?
     ;; FIXME merge these two cases
     (esh--latex-export-doctree-1 prop val
                               (esh-intervals-int-l doctree)
                               (esh-intervals-int-r doctree)
                               (esh-intervals-int-children doctree)))
    (`nil (esh--latex-export-subtrees (esh-intervals-int-l doctree)
                                   (esh-intervals-int-r doctree)
                                   (esh-intervals-int-children doctree)))))

(defun esh--latexify-protect-bols ()
  "Prefix each line of current buffer with a call to \\ESHBol{}.
This used to only be needed for lines starting with whitespace,
but leading dashes sometimes behave strangely; it's simpler (and
safer) to prefix all lines.  \\ESHBol is a no-op in inline mode."
  (goto-char (point-min))
  (while (re-search-forward "^" nil t)
    (replace-match "\\ESHBol{}" t t)))

(defun esh--latexify-protect-eols ()
  "Suffix each line of current buffer with a call to \\ESHEol.
Do this instead of using catcodes, for robustness.  Including a
brace pair after \\ESHEol would break alignment of continuation
lines in inline blocks."
  (goto-char (point-min))
  (while (search-forward "\n" nil t)
    (replace-match "\\ESHEol\n" t t)))

(defun esh--latex-export-buffer ()
  "Export current buffer to LaTeX."
  (let ((inhibit-modification-hooks t))
    (setq-local buffer-undo-list t)
    (untabify (point-min) (point-max))
    (esh--commit-overlays (current-buffer))
    (esh--remove-final-newline)
    (esh--commit-specs)
    (esh--mark-newlines '(esh--break t)))
  (let ((tree (esh--buffer-to-document-tree
               esh--latex-props
               esh--latex-face-attrs
               esh--latex-priorities
               #'esh--latex-range-filter nil))
        (esh--latex-source-buffer-for-export (current-buffer)))
    (with-temp-buffer
      (esh--latex-export-doctree tree)
      (esh--latexify-protect-eols)
      (esh--latexify-protect-bols)
      (buffer-string))))

(defun esh--latexify-insert-preamble ()
  "Read ESH's LaTeX preamble from disk and insert it at point."
  (insert-file-contents (expand-file-name "etc/esh-preamble.tex" esh--directory)))

(defvar esh--latexify-preamble-marker "^%%[ \t]*ESH-preamble-here[ \t]*$")

(defun esh--latexify-add-preamble ()
  "Expand `esh--latexify-preamble-marker', if present."
  (goto-char (point-min))
  (when (re-search-forward esh--latexify-preamble-marker nil t)
    (delete-region (match-beginning 0) (match-end 0))
    (esh--latexify-insert-preamble)))

(defconst esh--latex-block-begin
  (concat "^[ \t]*%%[ \t]*\\(ESH\\(?:\\(?:Inline\\)?Block\\)?\\)\\b\\([^:]*\\): \\([^ \t\n]+\\)[ \t]*\n"
          "[ \t]*\\\\begin{\\(.+?\\)}.*\n"))

(defconst esh--latex-block-end
  "\n[ \t]*\\\\end{%s}")

(defun esh--latex-match-block ()
  "Find the next ESH block, if any."
  (when (re-search-forward esh--latex-block-begin nil t)
    (let* ((beg (match-beginning 0))
           (code-beg (match-end 0))
           (block-type (match-string-no-properties 1))
           (block-opts (match-string-no-properties 2))
           (mode (match-string-no-properties 3))
           (env (match-string-no-properties 4))
           (end-re (format esh--latex-block-end (regexp-quote env))))
      (when (string= "" mode)
        (error "Invalid ESH header: %S" (match-string-no-properties 0)))
      (when (re-search-forward end-re nil t)
        (let* ((code-end (match-beginning 0))
               (code (buffer-substring-no-properties code-beg code-end)))
          (list block-type mode block-opts code beg (match-end 0)))))))

(defun esh--latexify-inline-verb-matcher (re)
  "Search for a \\verb-like delimiter from point.
That is, a match of the form RE?...? where ? is any
character."
  (when (and re (re-search-forward re nil t))
    (let ((form-beg (match-beginning 0))
          (command (match-string 0))
          (delimiter (char-after))
          (code-beg (1+ (point))))
      (unless delimiter
        (error "No delimiter found after use of `%s'" command))
      (goto-char code-beg)
      (if (search-forward (char-to-string delimiter) (point-at-eol) t)
          (list form-beg (point) code-beg (1- (point)) command)
        (error "No matching delimiter found after use of `%s%c'"
               command delimiter)))))

(defun esh--latexify-beginning-of-document ()
  "Go past \\begin{document}."
  (goto-char (point-min))
  (unless (search-forward "\\begin{document}" nil t)
    (goto-char (point-min))))

(defvar esh-latex-inline-macro-alist nil
  "Alist of inline ESH marker → mode function.

This list maps inline verb-like markers to modes.  For example,
it could contain (\"@ocaml \\\\verb\" . tuareg-mode) to recognize
all instances of “@ocaml \\verb|...|” as OCaml code to be
highlighted with `tuareg-mode'.  This list is ignored in HTML
mode.  See the manual for more information.")

(defun esh-latex-add-inline-verb (verb mode)
  "Teach ESH about an inline VERB, highlighted with MODE.
For example (esh-latex-add-inline-verb \"\\\\ocaml\" \\='tuareg-mode)
recognizes all instances of “\\ocaml|...|” as OCaml code to be
highlighted with `tuareg-mode'."
  (add-to-list 'esh-latex-inline-macro-alist (cons verb mode)))

(defconst esh--latexify-inline-template "\\ESHInline{%s}")
(defconst esh--latexify-block-template "\\begin{ESHBlock}%s\n%s\n\\end{ESHBlock}")
(defconst esh--latexify-inline-block-template "\\begin{ESHInlineBlock}%s\n%s\n\\end{ESHInlineBlock}")

(defvar esh--latex-pv
  "Whether to build and dump a table of highlighted inline code.")

(defvar-local esh--latex-pv-highlighting-map nil
  "List of (macro VERB CODE TEX) lists.
Each entry corresponds to one code snippet CODE, introduced by
\\VERB, and highlighted into TEX.")

(defun esh--latex-pv-record-snippet (verb code tex)
  "Record highlighting of VERB|CODE| as TEX."
  (when esh--latex-pv
    (unless (string-match "\\\\\\([a-zA-Z]+\\)" verb)
      (error "%S isn't compatible with --precompute-verbs-map.
To work reliably, ESH-pv verb macros must be in the form \\[a-zA-Z]+" verb))
    (push (list 'macro (match-string 1 verb) code tex)
          esh--latex-pv-highlighting-map)))

(defconst esh--latex-pv-delimiters
  (mapcar (lambda (c)
            (cons c (regexp-quote (char-to-string c))))
          (string-to-list "|`/!=~+-,;:abcdefghijklmnopqrstuvwxyz"))
  "Alist of character → regexp matching that character.")

(defun esh--latex-pv-find-delimiter (code)
  "Find a delimiter that does not appear in CODE."
  (let ((candidates esh--latex-pv-delimiters)
        (delim nil))
    (while (not delim)
      (unless candidates
        (error "No delimiter found to wrap %S" code))
      (pcase-let* ((`(,char . ,re) (pop candidates)))
        (when (not (string-match-p re code))
          (setq delim char))))
    delim))

(defconst esh--latex-pv-def-template "\\DeclareRobustCommand*{\\%s}{\\ESHpvLookupVerb{%s}}\n")
(defconst esh--latex-pv-push-template "\\ESHpvDefineVerb{%s}%c%s%c{%s}\n")

(defun esh--latex-pv-export-macro (verb code tex decls)
  "Insert an \\ESHpvDefine form for (macro VERB CODE TEX).
DECLS accumulates existing declarations."
  (let* ((dl (esh--latex-pv-find-delimiter code))
         (decl (format esh--latex-pv-push-template verb dl code dl tex)))
    (unless (gethash decl decls) ;; Remove duplicates
      (puthash decl t decls)
      (insert decl))))

(defun esh--latex-pv-export-latex (map)
  "Prepare \\ESHpvDefine forms for all records in MAP.
Records must match the format of `esh--latex-pv-highlighting-map'."
  (with-temp-buffer
    (let ((verbs (make-hash-table :test #'equal))
          (decls (make-hash-table :test #'equal)))
      (pcase-dolist (`(macro ,verb ,code ,tex) map)
        (puthash verb t verbs)
        (esh--latex-pv-export-macro verb code tex decls))
      (maphash (lambda (verb _)
                 (insert (format esh--latex-pv-def-template verb verb)))
               verbs))
    (buffer-string)))

(defun esh--latexify-do-inline-macros ()
  "Latexify sources in ESH inline macros."
  (let* ((modes-alist esh-latex-inline-macro-alist)
         (envs-re (when modes-alist (regexp-opt (mapcar #'car modes-alist)))))
    (esh--latexify-beginning-of-document)
    (let ((match-info nil))
      (while (setq match-info (esh--latexify-inline-verb-matcher envs-re))
        (pcase match-info
          (`(,beg ,end ,code-beg ,code-end ,cmd)
           (let* ((mode-fn (cdr (assoc cmd modes-alist)))
                  (code (buffer-substring-no-properties code-beg code-end))
                  (tex (esh--export-str code mode-fn #'esh--latex-export-buffer))
                  (wrapped (format esh--latexify-inline-template tex)))
             (goto-char beg)
             (delete-region beg end)
             (esh--latex-pv-record-snippet cmd code wrapped)
             (insert wrapped))))))))

(defconst esh--latex-block-templates
  `(("ESH" . ,esh--latexify-block-template)
    ("ESHBlock" . ,esh--latexify-block-template)
    ("ESHInlineBlock" . ,esh--latexify-inline-block-template)))

(defun esh--latexify-do-block-envs ()
  "Latexify sources in esh block environments."
  (goto-char (point-min))
  (let ((match nil))
    (while (setq match (esh--latex-match-block))
      (pcase-let* ((`(,block-type ,mode-str ,block-opts ,code ,beg ,end) match)
                   (mode-fn (esh--resolve-mode-fn mode-str))
                   (template (cdr (assoc block-type esh--latex-block-templates))))
        (delete-region beg end)
        (let* ((tex (esh--export-str code mode-fn #'esh--latex-export-buffer))
               (wrapped (format template block-opts tex)))
          (insert wrapped))))))

(defun esh2tex-current-buffer ()
  "Fontify contents of all ESH environments.
Replace the ESH-Latexify sources in environments delimited by
`esh-latexify-block-envs' and user-defined inline groups."
  (interactive)
  (esh--interactive-export
    (save-excursion
      (progn
        (esh--latexify-add-preamble)
        (esh--latexify-do-inline-macros)
        (esh--latexify-do-block-envs)))))

(defun esh2tex-tex-file (path)
  "Fontify contents of all ESH environments in PATH."
  (with-temp-buffer
    (esh--insert-file-contents path)
    (esh2tex-current-buffer)
    (buffer-string)))

(defun esh2tex-tex-file-pv (path)
  "Find and highlight inline ESH macros in PATH.
Return a document consisting of “snippet → highlighted
code” pairs (in \\ESHpvDefine form)."
  (let ((esh--latex-pv t))
    (with-temp-buffer
      (esh--insert-file-contents path)
      (esh2tex-current-buffer)
      (esh--latex-pv-export-latex esh--latex-pv-highlighting-map))))

(defun esh2tex-source-file (source-path)
  "Fontify contents of SOURCE-PATH.
Return result as a LaTeX string."
  (esh--export-file source-path #'esh--latex-export-buffer))

;;; Producing HTML

(defconst esh--html-specials '((?< . "&lt;")
                            (?> . "&gt;")
                            (?& . "&amp;")
                            (?\" . "&quot;")))

(defconst esh--html-specials-re
  (regexp-opt-charset (mapcar #'car esh--html-specials)))

(defun esh--html-substitute-special (m)
  "Get replacement for HTML special M."
  (cdr (assq (aref m 0) esh--html-specials)))

(defun esh--html-substitute-specials (str)
  "Escape HTML specials in STR."
  (replace-regexp-in-string
   esh--html-specials-re #'esh--html-substitute-special str t t))

(defconst esh--html-void-tags '(area base br col embed hr img input
                                  link menuitem meta param source track wbr))

(defun esh--html-serialize (node escape-specials)
  "Write NODE as HTML string to current buffer.
With non-nil ESCAPE-SPECIALS, quote special HTML characters in
NODE's body.  If ESCAPE-SPECIALS is nil, NODE must be a string."
  (pcase node
    ((pred stringp)
     (insert (if escape-specials
                 (esh--html-substitute-specials node)
               node)))
    (`(comment nil ,comment)
     ;; "--" isn't allowed in comments, so no need for escaping
     (insert "<!--" comment "-->"))
    (`(,tag ,attributes . ,children)
     (unless escape-specials
       (error "Must escape specials in %S" tag))
     (let ((tag-name (symbol-name tag))
           (escape-specials (not (memq tag '(script style)))))
       (insert "<" tag-name)
       (pcase-dolist (`(,attr . ,val) attributes)
         (insert " " (symbol-name attr) "=\"")
         (esh--html-serialize val escape-specials)
         (insert "\""))
       (if (memq tag esh--html-void-tags)
           (insert " />")
         (insert ">")
         (dolist (c children)
           (esh--html-serialize c escape-specials))
         (insert "</" tag-name ">"))))
    (_ (error "Unprintable node %S" node))))

(defconst esh--html-props
  '(display invisible non-ascii line-height esh--newline))
(defconst esh--html-face-attrs
  '(:underline :background :foreground :weight :slant :box :height))

(defconst esh--html-priorities
  `( ;; Fine to split
    ,@'(line-height :underline :foreground :weight :height :background)
    ;; Should not split
    ,@'(:slant :box display esh--newline non-ascii invisible))
  "Priority order for text properties in HTML export.
See `esh--resolve-event-conflicts'.")

(defun esh--html-range-filter (range)
  "Remove incorrectly placed line-height properties of RANGE."
  (esh--translate-invisibility range)
  (let ((alist (cl-caddr range)))
    (when (and (assq 'line-height range)
               (not (assq 'esh--newline range)))
      (setf (cl-caddr range) (assq-delete-all 'line-height alist)))))

(defun esh--html-wrap-children (styles non-ascii children &optional tag)
  "Apply STYLES and NON-ASCII markup to CHILDREN.
STYLES are applied using a new TAG node."
  (when non-ascii ;; Aligning wide characters properly requires 3 nested spans
    (setq children `((span nil (span nil ,@children)))))
  (if (or styles non-ascii tag)
      (let ((style (mapconcat (lambda (p) (concat (car p) ":" (cdr p))) styles ";")))
        `((,(or tag 'span) (,@(when styles `((style . ,style)))
                            ,@(when non-ascii `((class . "esh-non-ascii"))))
           ,@children)))
    children))

(defun esh--html-make-strut (height)
  "Construct an HTML node implementing a strut of height HEIGHT."
  `(span ((class . "esh-strut") (style . ,(format "height: %.2gem" height)))))

(defun esh--html-export-doctree-1 (attributes children &optional tag)
  "Wrap CHILDREN in a HTML implementation of ATTRIBUTES.
Return an HTML AST; the root is a TAG node (default: span)."
  (let ((styles nil)
        (raised nil)
        (non-ascii nil)
        (line-height nil))
    (pcase-dolist (`(,property . ,val) attributes)
      (when val
        (pcase property
          (:foreground
           (push (cons "color" (concat "#" val)) styles))
          (:background
           (push (cons "background-color" (concat "#" val)) styles))
          (:weight
           (push (cons "font-weight" (format "%d" val)) styles))
          (:height
           (let ((height (if (floatp val) (format "%d%%" (* val 100))
                           (format "%.2gpt" (/ val 10.0)))))
             (push (cons "font-size" height) styles)))
          (:slant
           (push (cons "font-style" (symbol-name val)) styles))
          (:underline
           (pcase-let* ((`(,color . ,type) val)
                        (ul-style `("underline"
                                    ,@(when (eq type 'wave) `("wavy"))
                                    ,@(when color `(,(concat "#" color))))))
             (push (cons "text-decoration" (esh--join ul-style " ")) styles)))
          (:box
           (pcase-let ((`(,line-width ,color ,style) val))
             (unless (eq style nil)
               (error "Unsupported box style %S" style))
             (let ((box-style `(,(format "%dpt" (abs line-width))
                                ,(pcase style
                                   (`released-button "outset")
                                   (`pressed-button "inset")
                                   (_ "solid"))
                                ,@(when color `(,(concat "#" color))))))
               (push (cons "border" (esh--join box-style " ")) styles))))
          (`display
           (pcase val
             (`(raise ,amount)
              (setq raised t)
              (push (cons "bottom" (format "%2gem" amount)) styles))
             (`(space :relative-height ,amount)
              (setq children (list (esh--html-make-strut amount) " ")))
             (_ (error "Unexpected display property %S" val))))
          (`invisible
           (setq children (if (equal val "") nil (list val))))
          (`line-height
           (unless (floatp val)
             (error "Unexpected line-height property %S" val))
           (setq line-height val))
          (`non-ascii
           (when val (setq non-ascii t)))
          (`esh--newline)
          (_ (error "Unexpected property %S" property)))))
    (cond
     ((null children) nil)
     (raised
      `((,(or tag 'span) ((class . "esh-raised"))
         (span ((class . "esh-raised-contents"))
               ,@(esh--html-wrap-children styles non-ascii children))
         (span ((class . "esh-raised-placeholder"))
               ,@(esh--html-wrap-children nil non-ascii children)))))
     (line-height
      ;; CSS line-height property shouldn't cover newlines
      (cons (esh--html-make-strut line-height)
            (esh--html-wrap-children styles non-ascii children tag)))
     (t
      (esh--html-wrap-children styles non-ascii children tag)))))

(defun esh--html-export-subtrees (l r trees)
  "Export TREES to HTML.
L .. R is the range covered by TREES; if TREES is nil, this
function exports a plain text range."
  (if trees (esh--html-export-trees trees)
    (list (buffer-substring-no-properties l r))))

(defun esh--html-export-doctree (doctree)
  "Export DOCTREE to HTML."
  (esh--html-export-doctree-1
   (esh-intervals-int-annot doctree)
   (esh--html-export-subtrees (esh-intervals-int-l doctree)
                           (esh-intervals-int-r doctree)
                           (esh-intervals-int-children doctree))))

(defun esh--html-export-trees (trees)
  "Export TREES to HTML."
  (cl-mapcan #'esh--html-export-doctree trees))

(defun esh--html-export-buffer ()
  "Export current buffer to HTML AST.
This may modify to the current buffer."
  (let ((inhibit-modification-hooks t))
    (setq-local buffer-undo-list t)
    (untabify (point-min) (point-max))
    (esh--commit-overlays (current-buffer))
    (esh--remove-final-newline)
    (esh--commit-specs)
    (esh--mark-newlines)
    (esh--mark-non-ascii))
  (let ((tree (esh--buffer-to-document-tree
               esh--html-props
               esh--html-face-attrs
               esh--html-priorities
               #'esh--html-range-filter t)))
    (esh--html-export-doctree tree)))

(defvar esh--html-src-class-prefix "src-"
  "HTML class prefix indicating a fontifiable tag.")

(defvar esh--html-src-class-re nil
  "Regexp matching classes of tags to be processed by ESH.
Dynamically set.")

(defvar esh-html-default-languages-alist nil
  "Alist of tag → language string.
For example, (code . \"emacs-lisp\") would highlight all `code'
tags with no ESH attribute as Emacs Lisp.")

(defun esh--htmlify-guess-lang (tag attributes)
  "Guess highlighting language based on TAG and ATTRIBUTES."
  (or (let ((class (cdr (assq 'class attributes))))
        (when (and class (string-match esh--html-src-class-re class))
          (match-string 1 class)))
      (cdr (assq tag esh-html-default-languages-alist))))

(defun esh--htmlify-do-tree (node)
  "Highlight code in annotated descendants of NODE."
  (pcase node
    ((pred stringp) node)
    (`(,tag ,attributes . ,children)
     (let ((lang (esh--htmlify-guess-lang tag attributes)))
       (if lang
           (let* ((mode-fn (esh--resolve-mode-fn lang))
                  (code (car children)))
             (unless (and (stringp code) (null (cdr children)))
               (error "Code block has children: %S" node))
             `(,tag ,attributes
                    ,@(esh--export-str code mode-fn #'esh--html-export-buffer)))
         `(,tag ,attributes
                ,@(mapcar (lambda (c) (esh--htmlify-do-tree c)) children)))))))

(defvar esh-html-before-parse-hook nil
  "Hook called before parsing input HTML.
Hook may e.g. make modifications to the buffer.")

(defun esh--html-read-tag (tag)
  "Read HTML TAG at point in current buffer."
  (when (looking-at (format "<%s [^>]+>" (regexp-quote tag)))
    (goto-char (match-end 0))
    (skip-chars-forward " \n\t")
    (buffer-substring-no-properties (match-beginning 0) (point))))

(defun esh--html-parse-buffer ()
  "Parse HTML document in current buffer."
  (run-hook-with-args 'esh-html-before-parse-hook)
  (goto-char (point-min))
  (let* ((xml-decl (esh--html-read-tag "?xml"))
         (doctype (esh--html-read-tag "!doctype"))
         (tree (libxml-parse-html-region (point) (point-max))))
    (list xml-decl doctype tree)))

(defun esh--html-parse-file (path)
  "Parse HTML file PATH."
  (with-temp-buffer
    (insert-file-contents path)
    (esh--html-parse-buffer)))

(defun esh--html-prepare-html-output (&rest tags)
  "Clear current buffer and insert TAGS not handled by libxml."
  (erase-buffer)
  (dolist (tag tags)
    (when tag (insert tag))))

(defun esh2html-current-buffer ()
  "Fontify contents of all ESH blocks in current document.
Highlight sources in any environments containing a class matching
`esh--html-src-class-prefix', such as `src-c', `src-ocaml', etc."
  (interactive)
  (esh--interactive-export
    (pcase-let* ((`(,xml-decl ,doctype ,tree) (esh--html-parse-buffer))
                 (esh--html-src-class-re (format "\\_<%s\\([^ ]+\\)\\_>"
                                              esh--html-src-class-prefix)))
      (esh--html-prepare-html-output xml-decl doctype)
      (esh--html-serialize (esh--htmlify-do-tree tree) t))))

(defun esh2html-html-file (path)
  "Fontify contents of all ESH environments in PATH."
  (with-temp-buffer
    (esh--insert-file-contents path)
    (esh2html-current-buffer)
    (buffer-string)))

;; Exporting a full buffer to HTML (htmlfontify-style)

(defvar esh--html-template-path
  (expand-file-name "etc/esh-standalone-template.html" esh--directory)
  "Path to ESH template for exporting standalone documents.")

(defun esh--html-substitute (ast substitutions)
  "Replace (FROM . TO) pairs from SUBSTITUTIONS in AST."
  (pcase ast
    ((pred stringp) ast)
    (`(,tag ,attrs . ,children)
     (or (cdr (assq tag substitutions))
         (let* ((subst-fun (lambda (c) (esh--html-substitute c substitutions)))
                (children (mapcar subst-fun children)))
           `(,tag ,attrs . ,children))))))

(defun esh--html-pre (children)
  "Construct a PRE tag and wrap CHILDREN into it."
  `((pre ((class . "esh-standalone")
          (style . ,(format "font-family: %S, monospace;"
                            (face-attribute 'default :family))))
         ,@children)))

(defun esh--html-wrap-in-body-tag (children)
  "Wrap CHILDREN in <body> and <pre> tags."
  (let* ((attrs (esh--extract-face-attributes esh--html-face-attrs '(default)))
         (normalized (esh-intervals-int-map-annots #'esh--normalize-defaults attrs)))
    (esh--html-export-doctree-1 normalized (esh--html-pre children) 'body)))

(defun esh--html-export-wrapped-1 ()
  "Render the current buffer as an HTML AST wrapped in a body tag."
  (esh--with-copy-of-current-buffer
    (car (esh--html-wrap-in-body-tag (esh--html-export-buffer)))))

(defun esh--html-export-wrapped ()
  "Render the current buffer as an HTML AST.
Unlike `esh--html-export-buffer', this produces a complete
webpage: the result of exporting is inserted into a template
found at `esh--html-template-path'.  Returns a 3-elements
list: (XML-HEADER DOCTYPE AST)."
  (pcase-let* ((body (esh--html-export-wrapped-1))
               (title (format "ESH: %s" (buffer-name)))
               (`(,xml ,dt ,template) (esh--html-parse-file esh--html-template-path))
               (substitutions `((esh-title . ,title) (body . ,body)))
               (document (esh--html-substitute template substitutions)))
    (list xml dt document)))

(defun esh-htmlfontify-buffer ()
  "Render the current buffer as a webpage."
  (interactive)
  (esh--interactive-export
    (pcase-let* ((`(,xml ,dt ,document) (esh--html-export-wrapped))
                 (out-buf-name (format "*esh-htmlfontify: %s*" (buffer-name))))
      (with-current-buffer (generate-new-buffer out-buf-name)
        (esh--html-prepare-html-output xml dt)
        (esh--html-serialize document t)
        (html-mode)
        (pop-to-buffer (current-buffer))))))

(defun esh-htmlfontify-display ()
  "Open rendering of current buffer in browser."
  (interactive)
  (esh--interactive-export
    (pcase-let* ((`(,xml ,dt ,document) (esh--html-export-wrapped))
                 (fname (make-temp-file "esh" nil ".html"))
                 (fdir (file-name-directory fname)))
      (with-temp-file fname
        (copy-file (expand-file-name "etc/esh-preamble.css" esh--directory)
                   (expand-file-name "esh-preamble.css" fdir) t)
        (esh--html-prepare-html-output xml dt)
        (esh--html-serialize document t)
        (browse-url fname)))))

(defun esh--htmlfontify-to-string ()
  "Render the current buffer as a webpage.
Returns HTML source code as a string."
  (pcase-let* ((`(,xml ,dt ,document) (esh--html-export-wrapped)))
    (with-temp-buffer
      (esh--html-prepare-html-output xml dt)
      (esh--html-serialize document t)
      (buffer-string))))

(defun esh2html-source-file (source-path)
  "Fontify contents of SOURCE-PATH.
Return result as a LaTeX string."
  (esh--export-file source-path #'esh--htmlfontify-to-string))

;; Local Variables:
;; checkdoc-arguments-in-order-flag: nil
;; End:

(provide 'esh)
;;; esh.el ends here
