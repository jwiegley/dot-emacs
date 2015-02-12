;;; anchored-transpose.el --- Transposes a phrase around an anchor phrase

;; Copyright (C) 2004 Free Software Foundation, Inc.

;; Author: Rick Bielawski <rbielaws@i1.net>
;; Keywords: tools convenience

;; This file is free software; you can redistribute it and/or modify it under
;; the terms of the GNU General Public License as published by the Free
;; Software Foundation; either version 2, or (at your option) any later
;; version.

;; This file is distributed in the hope that it will be useful, but WITHOUT
;; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
;; FITNESS FOR A PARTICULAR PURPOSE. See the GNU General Public License for
;; more details.

;;; Commentary:

;; `anchored-transpose' is an interactive autoload function to transpose
;; portions of a region around an anchor phrase.  In other words it swaps
;; two regions.
;;
;; See C-h f anchored-transpose <ret> for a complete description.

;;; Installing:

;; 1) Put anchored-transpose.el on your load path.
;; 2) Put the following 2 lines in your .emacs
;;    (global-set-key [?\C-x ?t] 'anchored-transpose)
;;    (autoload 'anchored-transpose "anchored-transpose" nil t)

;;; History:

;; 2004-09-24 RGB Seems useable enough to release.
;; 2004-10-15 RGB Only comments and doc strings were updated.
;; 2004-10-22 RGB Added support for 2 phrase selection.
;; 2004-12-01 RGB Added secondary selection support.
;; 2005-07-21 RGB Updated help text and comments.
;;                Added support for A  C B  D and C  A D  B selection.
;;                Fixed bug affecting multi line selections.
;; 2005-09-28 RGB Allow swapping regions with no anchor text between.
;; 2005-10-17 RGB Fix bug in fuzzy logic which turned off fuzziness.

;;; Code:

(defvar anchored-transpose-anchor ()
  "begin/end when `anchored-transpose' is in progress else nil")

;;;###autoload
(defun anchored-transpose (beg1 end1 flg1 &optional beg2 end2 flg2)
  "Transpose portions of the region around an anchor phrase.

`this phrase but not that word'    can be transposed into
`that word but not this phrase'

I want this phrase but not that word.
       |----------------------------|. .This is the entire phrase.
                  |-------|. . . . . . .This is the anchor phrase.

First select the entire phrase and type \\[anchored-transpose].  Then select
the anchor phrase and type \\[anchored-transpose] again.  By default the
anchor phrase will automatically include any surrounding whitespace even if
you don't explicitly select it.  Also, it won't include certain trailing
punctuation.  See `anchored-transpose-do-fuzzy' for details.  A prefix arg
prior to either selection means `no fuzzy logic, use selections literally'.

You can select the anchor phrase first followed by the entire phrase if more
convenient.  Typing \\[anchored-transpose] with nothing selected clears any
prior selection.  If both primary and secondary selections are active this
command swaps the 2 selections immediately.

I want this phrase but not that word.
       |----------|       |---------|   Separate phrase selection.

You can also select the phrases to be swapped separately in any order.
"
  (interactive `(,(region-beginning) ,(region-end)
                 ,current-prefix-arg
                 ,@anchored-transpose-anchor))
  (setq anchored-transpose-anchor nil deactivate-mark t)
  (when (and mouse-secondary-overlay
             mark-active
             (eq (overlay-buffer mouse-secondary-overlay)
                 (current-buffer)
             )
             (/= (overlay-start mouse-secondary-overlay)
                 (overlay-end mouse-secondary-overlay)
             )
        )
    (setq beg2 (overlay-start mouse-secondary-overlay))
    (setq end2 (overlay-end mouse-secondary-overlay))
    (setq flg2 flg1)
    (delete-overlay mouse-secondary-overlay)
  )
  (if mark-active
      (if end2                     ; then both regions are marked.  swap them.
          (if (and (< beg1 beg2)        ;A  C B  D
                   (< end1 end2)
                   (> end1 beg2))
              (apply 'anchored-transpose-swap
                     (anchored-transpose-do-fuzzy
                      beg1 beg2 end1 end2 flg1 flg2 flg1 flg2))
            (if (and (> beg1 beg2)      ;C  A D  B
                     (> end1 end2)
                     (> end2 beg1))
                (apply 'anchored-transpose-swap
                       (anchored-transpose-do-fuzzy
                        beg2 beg1 end2 end1 flg2 flg1 flg2 flg1))
              (if (and (< beg1 beg2)    ;A  C D  B
                       (> end1 end2))
                  (apply 'anchored-transpose-swap
                         (anchored-transpose-do-fuzzy
                          beg1 beg2 end2 end1 flg1 flg2 flg2 flg1))
                (if (and (> beg1 beg2)  ;C  A B  D
                         (< end1 end2))
                    (apply 'anchored-transpose-swap
                           (anchored-transpose-do-fuzzy
                            beg2 beg1 end1 end2 flg2 flg1 flg1 flg2))
                  (if (<= end1 beg2)    ;A B  C D
                      (apply 'anchored-transpose-swap
                             (anchored-transpose-do-fuzzy
                              beg1 end1 beg2 end2 flg1 flg1 flg2 flg2))
                    (if (<= end2 beg1)  ;C D A B
                        (apply 'anchored-transpose-swap
                               (anchored-transpose-do-fuzzy
                                beg2 end2 beg1 end1 flg2 flg2 flg1 flg1))
                      (error "Regions have invalid overlap")))))))
        ;; 1st of 2 regions.  Save it and wait for the other.
        (setq anchored-transpose-anchor (list beg1 end1 flg1))
        (message "Select other part (anchor or region)"))
    (error "Command requires a marked region")))

(defun anchored-transpose-do-fuzzy (r1beg r1end r2beg r2end
                                          lit1 lit2 lit3 lit4)
"Returns the first 4 arguments after adjusting their value if necessary.

I want this phrase but not that word.
       |----------------------------|. .This is the entire phrase.
                  |-------|. . . . . . .This is the anchor phrase.
     R1BEG      R1END   R2BEG     R2END

R1BEG and R1END define the first region and R2BEG and R2END the second.

The flags, LIT1 thru LIT4 indicate if fuzzy logic should be applied to the
beginning of R1BEG, the end of R1END, the beginning of R2BEG, the end of R2END
respectively.  If any flag is nil then fuzzy logic will be applied.  Otherwise
the value passed should be returned LITerally (that is, unchanged).

See `anchored-transpose-fuzzy-begin' and `anchored-transpose-fuzzy-end' for
specifics on what adjustments these routines will make when LITx is nil."
  (list
   (if lit1 r1beg
     (anchored-transpose-fuzzy-begin r1beg r1end "[\t ]+"))
   (if lit2 r1end
     (anchored-transpose-fuzzy-end   r1beg r1end "\\s +"))
   (if lit3 r2beg
     (anchored-transpose-fuzzy-begin r2beg r2end "[\t ]+"))
   (if lit4 r2end
     (anchored-transpose-fuzzy-end   r2beg r2end "\\s *[.!?]"))))

(defun anchored-transpose-fuzzy-end (beg end what)
  "Returns END or new value for END based on the regexp WHAT.
BEG and END are buffer positions defining a region.  If that region ends
with WHAT then the value for END is adjusted to exclude that matching text.

NOTE: The regexp is applied differently than `looking-back' applies a regexp.

Example: if (buffer-string beg end) contains `1234' the regexp `432' matches
it, not `234' as `looking-back' would.  Also, your regexp never sees the char
at BEG so the match will always leave at least 1 character to transpose.
The reason for not using looking-back is that it's not greedy enough.
(looking-back \" +\") will only match one space no matter how many exist."
  (let ((str (concat
              (reverse (append (buffer-substring (1+ beg) end) nil)))))
    (if (string-match (concat "\\`" what) str)
        (- end (length (match-string 0 str)))
      end)))

(defun anchored-transpose-fuzzy-begin (beg end what)
  "Returns BEG or a new value for BEG based on the regexp WHAT.
BEG and END are buffer positions defining a region.  If the region begins
with WHAT then BEG is adjusted to exclude the matching text.

NOTE: Your regexp never sees the last char defined by beg/end.  This insures
at least 1 char is always left to transpose."
  (let ((str (buffer-substring beg (1- end))))
    (if (string-match (concat "\\`" what) str)
        (+ beg (length (match-string 0 str)))
      beg)))

(defun anchored-transpose-swap (r1beg r1end r2beg r2end)
  "Swaps region r1beg/r1end with r2beg/r2end. Flags are currently ignored.
Point is left at r1end."
  (let ((reg1 (buffer-substring r1beg r1end))
        (reg2 (delete-and-extract-region r2beg r2end)))
    (goto-char r2beg)
    (insert reg1)
    (save-excursion  ;; I want to leave point at the end of phrase 2.
      (goto-char r1beg)
      (delete-region r1beg r1end)
      (insert reg2))))

(provide 'anchored-transpose)

;; Because I like it this way.  So there!
;;; Local Variables: ***
;;; fill-column:78 ***
;;; emacs-lisp-docstring-fill-column:78 ***
;;; End: ***
;;; anchored-transpose.el ends here.
