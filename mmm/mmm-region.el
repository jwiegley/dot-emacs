;;; mmm-region.el --- Manipulating and behavior of MMM submode regions

;; Copyright (C) 2000 by Michael Abraham Shulman

;; Author: Michael Abraham Shulman <mas@kurukshetra.cjb.net>
;; Version: $Id$

;;{{{ GPL

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;}}}

;;; Commentary:

;; This file provides the functions and variables to create, delete,
;; and inspect submode regions, as well as functions that make them
;; behave like the submode with respect to syntax tables, local maps,
;; font lock, etc.

;;; Code:

(require 'cl)
(require 'font-lock)
(require 'mmm-compat)
(require 'mmm-utils)
(require 'mmm-auto)
(require 'mmm-vars)

;; INSPECTION
;;{{{ Current Overlays

;; Emacs counts an overlay starting at POS as "at" POS, but not an
;; overlay ending at POS. XEmacs is more sensible and uses beg- and
;; end-stickiness to determine whether an endpoint is within an
;; extent. Here we want to act like XEmacs does.

(defun mmm-overlay-at (&optional pos type)
  "Return the highest-priority MMM Mode overlay at POS.
TYPE is passed on to `mmm-overlays-at', which see."
  (car (mmm-overlays-at (or pos (point)) type)))

(defun mmm-overlays-at (&optional pos type)
  "Return a list of the MMM overlays at POS, in decreasing priority.
TYPE should be nil, `beg', `end', `none', or `all'. If `none', return
only overlays strictly including POS. If nil, return overlays starting
at POS only if they are beg-sticky, and those ending at POS only if
they are end-sticky. If `beg', return all overlays starting at POS but
none ending at POS, if `end', return all overlays ending at POS
but none starting at POS, and if `all', return both."
  (or pos (setq pos (point)))
  (remove-if-not #'(lambda (ovl)
                     (mmm-included-p ovl pos type))
                 (mmm-overlays-in (1- pos) (1+ pos))))

(defun mmm-included-p (ovl pos type)
  (cond ((eql (overlay-start ovl) pos)
         (case type
           ((none end) nil)
           ((nil) (overlay-get ovl 'beg-sticky))
           ((beg all) t)))
        ((eql (overlay-end ovl) pos)
         (case type
           ((none beg) nil)
           ((nil) (overlay-get ovl 'end-sticky))
           ((end all) t)))
        (t t)))

(defun mmm-overlays-in (start stop &optional strict delim)
  "Return the MMM overlays in START to STOP, in decreasing priority.
If STRICT is non-nil, include only those overlays which are entirely
contained in the region.  In this case, if DELIM is non-nil, the
region delimiters, if any, must also be included."
  (mmm-sort-overlays
   (remove-if-not #'(lambda (ovl)
                      (and (overlay-get ovl 'mmm)
                           (or (not strict)
                               (>= stop (if delim
                                            (mmm-back-end ovl)
                                          (overlay-end ovl)))
                               (<= start (if delim
                                             (mmm-front-start ovl)
                                           (overlay-start ovl))))))
                  (overlays-in (max start (point-min))
                               (min stop (point-max))))))

(defun mmm-sort-overlays (overlays)
  "Sort OVERLAYS in order of decreasing priority."
  (sort (copy-list overlays)
        #'(lambda (x y) (> (or (overlay-get x 'priority) 0)
                           (or (overlay-get y 'priority) 0)))))

;;}}}
;;{{{ Current Submode

(defvar mmm-current-overlay nil
  "What submode region overlay we think we are currently in.
May be out of date; call `mmm-update-current-submode' to correct it.")
(make-variable-buffer-local 'mmm-current-overlay)

(defvar mmm-previous-overlay nil
  "What submode region overlay we were in just before this one.
Set by `mmm-update-current-submode'.")
(make-variable-buffer-local 'mmm-previous-overlay)

(defvar mmm-current-submode nil
  "What submode we think we are currently in.
May be out of date; call `mmm-update-current-submode' to correct it.")
(make-variable-buffer-local 'mmm-current-submode)

(defvar mmm-previous-submode nil
  "What submode we were in just before this one.
Set by `mmm-update-current-submode'.")
(make-variable-buffer-local 'mmm-previous-submode)

(defun mmm-update-current-submode (&optional pos)
  "Update current and previous position variables to POS.
Return non-nil if the current region changed."
  (let ((ovl (mmm-overlay-at (or pos (point)))))
    (if (eq ovl mmm-current-overlay)
        nil
      (setq mmm-previous-overlay mmm-current-overlay
            mmm-previous-submode mmm-current-submode)
      (setq mmm-current-overlay ovl
            mmm-current-submode (if ovl (overlay-get ovl 'mmm-mode)))
      t)))

(defun mmm-set-current-submode (mode &optional pos)
  "Set the current submode to MODE and the current region to whatever
region of that mode is present at POS, or nil if none."
  (setq mmm-previous-overlay mmm-current-overlay
        mmm-previous-submode mmm-current-submode)
  (setq mmm-current-submode mode
        mmm-current-overlay
        (find-if #'(lambda (ovl)
                     (eq (overlay-get ovl 'mmm-mode) mode))
                 (mmm-overlays-at (or pos (point)) 'all))))

(defun mmm-submode-at (&optional pos type)
  "Return the submode at POS \(or point), or NIL if none.
TYPE is passed on to `mmm-overlays-at', which see."
  (let ((ovl (mmm-overlay-at (or pos (point)) type)))
    (if ovl (overlay-get ovl 'mmm-mode))))

;;}}}
;;{{{ Match Front & Back

(defun mmm-match-front (ovl)
  "Return non-nil if the front delimiter of OVL matches as it should.
Sets the match data to the front delimiter, if it is a regexp,
otherwise calls it as a function with point at the beginning of the
overlay and one argument being the overlay. The function should return
non-nil if the front delimiter matches correctly, and set the match
data appropriately."
  (let ((front (overlay-get ovl 'front)))
    (save-excursion
      (goto-char (overlay-start ovl))
      (if (stringp front)
          ;; It's a regexp
          (mmm-looking-back-at front)
        ;; It's a function
        (funcall front ovl)))))

(defun mmm-match-back (ovl)
  "Return non-nil if the back delimiter of OVL matches as it should.
Sets the match data to the back delimiter, if it is a regexp,
otherwise calls it as a function with point at the end of the overlay
and one argument being the overlay. The function should return non-nil
if the back delimiter matches correctly, and set the match data
appropriately."
  (let ((back (overlay-get ovl 'back)))
    (save-excursion
      (goto-char (overlay-end ovl))
      (if (stringp back)
          ;; It's a regexp
          (looking-at back)
        (funcall back ovl)))))

;;}}}
;;{{{ Delimiter Boundaries

(defun mmm-front-start (ovl)
  "Return the position at which the front delimiter of OVL starts.
If OVL is not front-bounded correctly, return its start position."
  (save-match-data
    (if (mmm-match-front ovl)
        (match-beginning 0)
      (overlay-start ovl))))

(defun mmm-back-end (ovl)
  "Return the position at which the back delimiter of OVL ends.
If OVL is not back-bounded correctly, return its end position."
  (save-match-data
    (if (mmm-match-back ovl)
        (match-end 0)
      (overlay-end ovl))))

;;}}}

;; CREATION & DELETION
;;{{{ Markers

(defun mmm-make-marker (pos beg-p sticky-p)
  "Make a marker at POS that is or isn't sticky.
BEG-P represents whether the marker delimits the beginning of a
region \(or the end of it). STICKY-P is whether it should be sticky,
i.e. whether text inserted at the marker should be inside the region."
  (let ((mkr (set-marker (make-marker) pos)))
    (set-marker-insertion-type mkr (if beg-p (not sticky-p) sticky-p))
    mkr))

;;}}}
;;{{{ Make Submode Regions

(defun* mmm-make-region
    (submode beg end &rest rest &key (front "") (back "")
             (beg-sticky t) (end-sticky t) face creation-hook
             &allow-other-keys
             )
  "Make a submode region from BEG to END of SUBMODE in FACE.
FRONT and BACK are regexps or functions to match the correct
delimiters--see `mmm-match-front' and `mmm-match-back'.  BEG-STICKY
and END-STICKY determine whether the front and back of the region,
respectively, are sticky with respect to new insertion.  CREATION-HOOK
should be a function to run after the region is created.  All other
keyword arguments are stored as properties of the overlay,
un-keyword-ified."
  (setq rest (append rest (list :front front :back back :beg-sticky
                                beg-sticky :end-sticky end-sticky)))
  (mmm-mode-on)
  ;; For now, complain about overlapping regions. Most callers should
  ;; trap this and continue on. In future, submode regions will be
  ;; allowed to sit inside others.
  (when (mmm-overlays-in beg end)
    (signal 'mmm-invalid-parent nil))
  (setq submode (mmm-modename->function submode))
  (when submode
    (mmm-update-mode-info submode))
  ;; Conditionally sticky overlays are by default sticky. Then the
  ;; insert-in-front and -behind functions fix them.
  (let ((ovl (make-overlay beg end nil (not beg-sticky) end-sticky)))
    ;; Put our properties on the overlay
    (dolist (prop '(front back beg-sticky end-sticky))
      (overlay-put ovl prop (symbol-value prop)))
    ;; Put anything else the caller wants on the overlay
    (loop for (var val) on rest by #'cddr
          do (overlay-put ovl (intern (substring (symbol-name var) 1)) val))
    (mapcar #'(lambda (pair) (overlay-put ovl (car pair) (cadr pair)))
            `((mmm t)           ; Mark our overlays
              (mmm-mode ,submode)
              (mmm-local-variables
               ;; Have to be careful to make new list structure here
               ,(list* (list 'font-lock-cache-state nil)
                       (list 'font-lock-cache-position (make-marker))
                       (copy-tree (cdr (assq submode mmm-region-saved-locals-defaults)))))
              ;; These have special meaning to Emacs
              (,mmm-evaporate-property t)
              (face ,(mmm-get-face face submode))
              ))
    (save-excursion
      (goto-char (overlay-start ovl))
      (mmm-set-current-submode submode)
      (mmm-set-local-variables submode)
      (mmm-run-submode-hook submode)
      (when creation-hook
        (funcall creation-hook))
      (mmm-save-changed-local-variables ovl submode))
    (setq mmm-previous-submode submode
          mmm-previous-overlay ovl)
    (mmm-update-submode-region)
    ovl))

(defun mmm-get-face (face submode)
  (case mmm-submode-decoration-level
    ((0) nil)
    ((1) (when submode
           'mmm-default-submode-face))
    ((2) (or face
             (when submode
               'mmm-default-submode-face)))))

;;}}}
;;{{{ Clear Overlays

;; See also `mmm-clear-current-region'.

(defun mmm-clear-overlays (&optional start stop strict)
  "Clears all MMM overlays between START and STOP.
If STRICT, only clear those strictly included, rather than partially."
  (mapcar #'delete-overlay
        (mmm-overlays-in (or start (point-min))
                         (or stop (point-max))
                         strict))
  (mmm-update-current-submode))

;;}}}

;; BASIC UPDATING
;;{{{ Submode Info

(defun mmm-update-mode-info (mode &optional force)
  "Save the global-saved and buffer-saved variables for MODE.
Global saving is done on properties of the symbol MODE and buffer
saving in `mmm-buffer-saved-locals'.  This function must be called for
both the dominant mode and all submodes, in each file.  Region-saved
variables are initialized from `mmm-region-saved-locals-defaults',
which is set here as well.  See `mmm-save-local-variables'.  If FORCE
is non-nil, don't quit if the info is already there."
  (let ((buffer-entry (assq mode mmm-buffer-saved-locals))
        (region-entry (assq mode mmm-region-saved-locals-defaults))
        global-vars buffer-vars region-vars
        ;; kludge for XEmacs 20
        (html-helper-build-new-buffer nil))
    (unless (and (not force)
                 (get mode 'mmm-local-variables)
                 buffer-entry
                 region-entry)
      (save-excursion
        (let ((filename (buffer-file-name)))
          ;; On errors, the temporary buffers don't get deleted, so here
          ;; we get rid of any old ones that may be hanging around.
          (when (buffer-live-p (get-buffer mmm-temp-buffer-name))
            (save-excursion
              (set-buffer (get-buffer mmm-temp-buffer-name))
              (set-buffer-modified-p nil)
              (kill-buffer (current-buffer))))
          ;; Now make a new temporary buffer.
          (set-buffer (mmm-make-temp-buffer (current-buffer)
                                            mmm-temp-buffer-name))
          (if (memq mode mmm-set-file-name-for-modes)
              (setq buffer-file-name filename)))
        (funcall mode)
        (when (featurep 'font-lock)
          ;; XEmacs doesn't have global-font-lock-mode (or rather, it
          ;; has nothing but global-font-lock-mode).
          (when (or mmm-xemacs
                    ;; Code copied from font-lock.el to detect when font-lock
                    ;; should be on via global-font-lock-mode.
                    (and (or font-lock-defaults
                             (assq major-mode font-lock-defaults-alist)
                             (assq major-mode font-lock-keywords-alist))
                         (or (eq font-lock-global-modes t)
                             (if (eq (car-safe font-lock-global-modes) 'not)
                                 (not (memq major-mode
                                            (cdr font-lock-global-modes)))
                               (memq major-mode font-lock-global-modes)))))
            ;; Don't actually fontify, but note that we should.
            (put mode 'mmm-font-lock-mode t))
          ;; Get the font-lock variables
          (when mmm-font-lock-available-p
            ;; To fool `font-lock-add-keywords'
            (let ((font-lock-mode t))
              (mmm-set-font-lock-defaults)))
          ;; These can't be in the local variables list, because we
          ;; replace their actual values, but we want to use their
          ;; original values elsewhere.
          (unless (and mmm-xemacs (= emacs-major-version 20))
            ;; XEmacs 20 doesn't have this variable.  This effectively
            ;; prevents the MMM font-lock support from working, but we
            ;; just ignore it and go on, to prevent an error message.
            (put mode 'mmm-fontify-region-function
                 font-lock-fontify-region-function))
          (put mode 'mmm-beginning-of-syntax-function
               font-lock-beginning-of-syntax-function))
        ;; Get variables
        (setq global-vars (mmm-get-locals 'global)
              buffer-vars (mmm-get-locals 'buffer)
              region-vars (mmm-get-locals 'region))
        (put mode 'mmm-mode-name mode-name)
        (set-buffer-modified-p nil)
        (kill-buffer (current-buffer)))
      (put mode 'mmm-local-variables global-vars)
      (if buffer-entry
          (setcdr buffer-entry buffer-vars)
        (push (cons mode buffer-vars) mmm-buffer-saved-locals))
      (if region-entry
          (setcdr region-entry region-vars)
        (push (cons mode region-vars)
              mmm-region-saved-locals-defaults)))))

;;}}}
;;{{{ Updating Hooks

(defun mmm-update-submode-region ()
  "Update all MMM properties correctly for the current position.
This function and those it calls do the actual work of setting the
different keymaps, syntax tables, local variables, etc. for submodes."
  (when (mmm-update-current-submode)
    (mmm-save-changed-local-variables mmm-previous-overlay
                                      mmm-previous-submode)
    (let ((mode (or mmm-current-submode mmm-primary-mode)))
      (mmm-update-mode-info mode)
      (mmm-set-local-variables mode)
      (mmm-enable-font-lock mode))
    (if mmm-current-submode
        (setq mode-name
              (mmm-format-string
               mmm-submode-mode-line-format
               `(("~M" . ,(get mmm-primary-mode 'mmm-mode-name))
                 ("~m" . ,(get mmm-current-submode 'mmm-mode-name)))))
      (setq mode-name (get mmm-primary-mode 'mmm-mode-name)))
    (force-mode-line-update)))

(defun mmm-add-hooks ()
  (make-local-hook 'post-command-hook)
  (add-hook 'post-command-hook 'mmm-update-submode-region nil 'local))

(defun mmm-remove-hooks ()
  (remove-hook 'post-command-hook 'mmm-update-submode-region 'local))

;;}}}
;;{{{ Local Variables

(defun mmm-get-local-variables-list (type mode)
  "Filter `mmm-save-local-variables' to match TYPE and MODE.
Return a list \(VAR ...).  In some cases, VAR will be a cons cell
\(GETTER . SETTER) -- see `mmm-save-local-variables'."
  (mapcan #'(lambda (element)
              (and (if (and (consp element)
                            (cdr element)
                            (cadr element))
                       (eq (cadr element) type)
                     (eq type 'global))
                   (if (and (consp element)
                            (cddr element)
                            (not (eq (caddr element) t)))
                       (if (functionp (caddr element))
                           (funcall (caddr element))
                         (member mode (caddr element)))
                     t)
                   (list (if (consp element) (car element) element))))
          mmm-save-local-variables))

(defun mmm-get-locals (type)
  "Get the local variables and values for TYPE from this buffer.
Return \((VAR VALUE) ...).  In some cases, VAR will be of the form
\(GETTER . SETTER) -- see `mmm-save-local-variables'."
  (mapcan #'(lambda (var)
              (if (consp var)
                  `((,var ,(funcall (car var))))
                (and (boundp var)
                     ;; This seems logical, but screws things up.
                     ;;(local-variable-p var)
                     `((,var ,(symbol-value var))))))
          (mmm-get-local-variables-list type major-mode)))

(defun mmm-get-saved-local (mode var)
  "Get the value of the local variable VAR saved for MODE, if any."
  (cadr (assq var (mmm-get-saved-local-variables mode))))

(defun mmm-set-local-variables (mode)
  "Set all the local variables saved for MODE.
Looks up both global, buffer, and region saves."
  (mapcar #'(lambda (var)
              ;; (car VAR) may be (GETTER . SETTER)
              (if (consp (car var))
                  (funcall (cdar var) (cadr var))
                (make-local-variable (car var))
                (set (car var) (cadr var))))
          (mmm-get-saved-local-variables mode)))

(defun mmm-get-saved-local-variables (mode)
  (append (get mode 'mmm-local-variables)
          (cdr (assq mode mmm-buffer-saved-locals))
          (let ((ovl (mmm-overlay-at (point))))
            (if ovl
                (overlay-get ovl 'mmm-local-variables)
              mmm-region-saved-locals-for-dominant))))

(defun mmm-save-changed-local-variables (ovl mode)
  "Save by-buffer and by-region variables for OVL and MODE.
Called when we move to a new submode region, with OVL and MODE the
region and mode for the previous position."
  (let ((buffer-vars (cdr (assq (or mode mmm-primary-mode)
                                mmm-buffer-saved-locals)))
        (region-vars (if ovl
                         (overlay-get ovl 'mmm-local-variables)
                       mmm-region-saved-locals-for-dominant))
        (set-local-value
         #'(lambda (var)
             (setcar (cdr var)
                     ;; (car VAR) may be (GETTER . SETTER)
                     (if (consp (car var))
                         (funcall (caar var))
                       (symbol-value (car var)))))))
    (mapc set-local-value buffer-vars)
    (mapc set-local-value region-vars)))

(defun mmm-clear-local-variables ()
  "Clear all buffer- and region-saved variables for current buffer."
  (setq mmm-buffer-saved-locals ()
        mmm-region-saved-locals-defaults ()
        mmm-region-saved-locals-for-dominant ()))

;;}}}

;; FONT LOCK
;;{{{ Enable Font Lock

(defun mmm-enable-font-lock (mode)
  "Turn on font lock if it is not already on and MODE enables it."
  (mmm-update-mode-info mode)
  (and mmm-font-lock-available-p
       (not font-lock-mode)
       (get mode 'mmm-font-lock-mode)
       (font-lock-mode 1)))

(defun mmm-update-font-lock-buffer ()
  "Turn on font lock iff any mode in the buffer enables it."
  (when mmm-font-lock-available-p
    (if (some #'(lambda (mode)
                  (get mode 'mmm-font-lock-mode))
              (remove-duplicates
               (cons mmm-primary-mode
                     (mapcar #'(lambda (ovl)
                                 (overlay-get ovl 'mmm-mode))
                             (mmm-overlays-in (point-min) (point-max))))))
        (font-lock-mode 1)
      (font-lock-mode 0))))

(defun mmm-refontify-maybe (&optional start stop)
  "Re-fontify from START to STOP, or entire buffer, if enabled."
  (and font-lock-mode
       (if (or start stop)
           (font-lock-fontify-region (or start (point-min))
                                     (or stop (point-max)))
         (font-lock-fontify-buffer))))

;;}}}
;;{{{ Get Submode Regions

(defun mmm-submode-changes-in (start stop)
  "Return a list of all submode-change positions from START to STOP.
The list is sorted in order of increasing buffer position, and the
boundary positions are included."
  (sort (remove-duplicates
         (list* start stop
                (mapcan #'(lambda (ovl)
                            `(,(overlay-start ovl)
                              ,(overlay-end ovl)))
                        (mmm-overlays-in start stop t t))))

        #'<))

(defun mmm-regions-in (start stop)
  "Return a list of regions of the form (MODE BEG END) whose disjoint
union covers the region from START to STOP."
  (let ((regions 
         (maplist #'(lambda (pos-list)
                      (if (cdr pos-list)
                          (list (or (mmm-submode-at (car pos-list) 'beg)
                                    mmm-primary-mode)
                                (car pos-list) (cadr pos-list))))
                  (mmm-submode-changes-in start stop))))
    (setcdr (last regions 2) nil)
    regions))


(defun mmm-regions-alist (start stop)
  "Return a list of lists of the form \(MODE . REGIONS) where REGIONS
is a list of elements of the form \(BEG END). The disjoint union all
of the REGIONS covers START to STOP."
  (let ((regions (mmm-regions-in start stop)))
    (mapcar #'(lambda (mode)
                (cons mode
                      (mapcan #'(lambda (region)
                                  (if (eq mode (car region))
                                      (list (cdr region))))
                              regions)))
            ;; All the modes
            (remove-duplicates (mapcar #'car regions)))))

;;}}}
;;{{{ Fontify Regions

(defun mmm-fontify-region (start stop &optional loudly)
  "Fontify from START to STOP keeping track of submodes correctly."
  (when loudly
    (message "Fontifying %s with submode regions..." (buffer-name)))
  ;; Necessary to catch changes in font-lock cache state and position.
  (mmm-save-changed-local-variables
   mmm-current-overlay mmm-current-submode)
  ;; For some reason `font-lock-fontify-block' binds this to nil, thus
  ;; preventing `mmm-beginning-of-syntax' from doing The Right Thing.
  ;; I don't know why it does this, but let's undo it here.
  (let ((font-lock-beginning-of-syntax-function 'mmm-beginning-of-syntax))
    (mapcar #'(lambda (elt)
                (when (get (car elt) 'mmm-font-lock-mode)
                  (mmm-fontify-region-list (car elt) (cdr elt))))
            (mmm-regions-alist start stop)))
  (mmm-update-submode-region)
  (when loudly (message nil)))

(defun mmm-fontify-region-list (mode regions)
  "Fontify REGIONS, each like \(BEG END), in mode MODE."
  (save-excursion
    (let (;(major-mode mode)
          (func (get mode 'mmm-fontify-region-function)))
      (mapcar #'(lambda (reg)
                  (goto-char (car reg))
                  ;; Here we do the same sort of thing that
                  ;; `mmm-update-submode-region' does, but we force it
                  ;; to use a specific mode, and don't save anything,
                  ;; fontify, or change the mode line.
                  (mmm-set-current-submode mode)
                  (mmm-set-local-variables mode)
                  (funcall func (car reg) (cadr reg) nil)
                  ;; Catch changes in font-lock cache.
                  (mmm-save-changed-local-variables
                   mmm-current-overlay mmm-current-submode))
              regions))))

;;}}}
;;{{{ Beginning of Syntax

(defun mmm-beginning-of-syntax ()
  (goto-char
   (let ((ovl (mmm-overlay-at (point)))
         (func (get (or mmm-current-submode mmm-primary-mode)
                    'mmm-beginning-of-syntax-function)))
     (max (if ovl (overlay-start ovl) (point-min))
          (if func (progn (funcall func) (point)) (point-min))
          (point-min)))))

;;}}}

(provide 'mmm-region)

;;; mmm-region.el ends here