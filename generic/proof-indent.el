;; proof-indent.el Generic Indentation for Proof Assistants
;;
;; Authors:	   Markus Wenzel, David Aspinall
;; License:        GPL (GNU GENERAL PUBLIC LICENSE)
;;
;; $Id$
;;

(require 'proof)                        ; loader
(require 'proof-script)                 ; indent code is for script editing


(defun proof-indent-indent ()
  "Determine indentation caused by syntax element at current point."
  (cond
   ((proof-looking-at-safe proof-indent-open-regexp)
    proof-indent)
   ((proof-looking-at-safe proof-indent-close-regexp)
    (- proof-indent))
   (t 0)))

(defun proof-indent-offset ()
  "Determine offset of syntax element at current point"
  (cond
   ((proof-looking-at-syntactic-context)
    proof-indent)
   ((proof-looking-at-safe proof-indent-inner-regexp)
    proof-indent)
   ((proof-looking-at-safe proof-indent-enclose-regexp)
    proof-indent-enclose-offset)
   ((proof-looking-at-safe proof-indent-open-regexp)
    proof-indent-open-offset)
   ((proof-looking-at-safe proof-indent-close-regexp)
    proof-indent-close-offset)
   ((proof-looking-at-safe proof-indent-any-regexp) 0)
   ((proof-looking-at-safe "\\s-*$") 0)
   (t proof-indent)))

(defun proof-indent-inner-p ()
  "Check if current point is between actual indentation elements."
  (or
   (proof-looking-at-syntactic-context)
   (proof-looking-at-safe proof-indent-inner-regexp)
   (not
    (or (proof-looking-at-safe proof-indent-any-regexp)
        (proof-looking-at-safe "\\s-*$")))))

(defun proof-indent-goto-prev ()   ; Note: may change point, even in case of failure!
  "Goto to previous syntax element for script indentation, ignoring string/comment contexts."
  (and
   (proof-re-search-backward proof-indent-any-regexp nil t)
   (or (not (proof-looking-at-syntactic-context))
       (proof-indent-goto-prev))))

(defun proof-indent-calculate (indent inner)  ; Note: may change point!
  "Calculate proper indentation level at current point"
  (let*
      ((current (point))
       (found-prev (proof-indent-goto-prev)))
    (if (not found-prev) (goto-char current))   ; recover position
    (cond
     ((and found-prev (or proof-indent-hang (= (current-indentation) (current-column))))
      (+ indent
         (current-column)
         (if (and inner (not (proof-indent-inner-p))) 0 (proof-indent-indent))
         (- (proof-indent-offset))))
     ((not found-prev) 0)         ;FIXME mmw: improve this case!?
     (t
      (proof-indent-calculate
       (+ indent (if inner 0 (proof-indent-indent))) inner)))))


;;;###autoload
(defun proof-indent-line ()
  "Indent current line of proof script, if indentation enabled."
  (interactive)
  (unless (not (proof-ass script-indent))
          (if (< (point) (proof-locked-end))
              (if (< (current-column) (current-indentation))
                  (skip-chars-forward "\t "))
            (save-excursion
              (indent-line-to
               (max 0 (save-excursion
                        (back-to-indentation)
                        (proof-indent-calculate (proof-indent-offset) (proof-indent-inner-p))))))
            (if (< (current-column) (current-indentation))
                (back-to-indentation))))
  (if proof-indent-pad-eol
      (proof-indent-pad-eol)))
      


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Useless spaces
;;

(defun proof-indent-pad-eol (&optional col)
  "Add padding to end of current line to match the previous line or COL.
This function adds useless space to buffers, but it cleans up the appearance
of locked regions in XEmacs."
  ;; A hook for TAB?
  (interactive)
  (save-excursion
    (let ((descol (or col
		     (save-excursion
		       (end-of-line 0)
		       (current-column)))))
      (save-excursion
	(end-of-line 1)
	(if (or (equal (current-column) 0) ;; special case for empty lines
		(> descol (current-column)))
	    (progn
	      (insert-char ?\   (- descol (current-column)))))))))

(defun proof-indent-pad-eol-region (start end)
  "Pad a region with extra spaces to the length of the longest line."
  (interactive)
  ;; Find the longest line..
  ;; pad others to the same length
  )
	  





(provide 'proof-indent)
