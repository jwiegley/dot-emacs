;; proof-depends.el  Theorem-theorem and theorem-definition dependencies.
;;
;; Copyright (C) 2000-2002 University of Edinburgh. 
;; Authors:      David Aspinall <da@dcs.ed.ac.uk>
;;	           Earlier version by Fiona McNeil.
;; License:     GPL (GNU GENERAL PUBLIC LICENSE)
;; Status:      Experimental code
;;
;; $Id$
;; 
;; Based on Fiona McNeill's MSc project on analysing dependencies
;; within proofs.  Code rewritten by David Aspinall.
;; 

(require 'span)

;; Variables

(defvar proof-thm-names-of-files nil
  "A list of file and theorems contained within.
A list of lists; the first element of each list is a file-name, the
second element a list of all the thm names in that file.
i.e.: ((file-name-1 (thm1 thm2 thm3)) (file-name-2 (thm1 thm2 thm3)))")

(defvar proof-def-names-of-files nil
  "A list of files and defs contained within.
A list of lists; the first element of each list is a file-name, the
second element a list of all the def names in that file.
i.e.: ((file-name-1 (def1 def2 def3)) (file-name-2 (def1 def2 def3)))")


;; Utility functions

(defun proof-depends-module-name-for-buffer ()
  "Return a module name for the current buffer.
This is a name that the prover prefixes all item names with.
For example, in isabelle, a file Stuff.ML contains theorems with
fully qualified names of the form Stuff.theorem1, etc.
For other provers, this function may need modifying."
  (if buffer-file-name
      (file-name-nondirectory 
       (file-name-sans-extension buffer-file-name)) ""))

(defun proof-depends-module-of (name)
  "Return a pair of a module name and base name for a given item name.
Assumes module name is given by dotted prefix."
  (let ((dot (string-match "\\." name)))
    (if dot 
	(cons (substring name 0 dot) (substring name (+ dot 1)))
      (cons "" name))))

(defun proof-depends-names-in-same-file (names)
  "Return subset of list NAMES which are guessed to occur in same file.
This is done using `proof-depends-module-name-for-buffer' and
`proof-depends-module-of'."
  (let ((filemod  (proof-depends-module-name-for-buffer))
	samefile)
    (while names
      (let ((splitname (proof-depends-module-of (car names))))
	(if (equal filemod (car splitname))
	    (setq samefile (cons (cdr splitname) samefile))))
      (setq names (cdr names)))
    ;; NB: reversed order
    samefile))
	       

;;
;; proof-depends-process-dependencies: the main entry point.
;;
;;;###autoload    
(defun proof-depends-process-dependencies (name gspan)
  "Process dependencies reported by prover, for NAME in span GSPAN.
Called from `proof-done-advancing' when a save is processed and
proof-last-theorem-dependencies is set."

  (set-span-property gspan 'dependencies
		     proof-last-theorem-dependencies)

  (let* ((samefilenames    (proof-depends-names-in-same-file
			   proof-last-theorem-dependencies))

	 ;; Find goalsave spans earlier in this file which this
	 ;; one depends on; update their list of dependents,
	 ;; and return resulting list paired up with names.
	 (depspans    
	  (apply 'append
		 (mapcar-spans 
		  (lambda (depspan)
		    (let ((dname (span-property depspan 'name)))
		      (if (and
			   (eq (span-property depspan 'type) 'goalsave)
			   (member dname samefilenames))
			  (let ((forwarddeps 
				 (span-property depspan 'dependents)))
			    (set-span-property depspan 'dependents
					       (cons
						(list name gspan) forwarddeps))
			    ;; return list of args for menu fun: name and span
			    (list (list dname depspan))))))
		  (point-min)
		  (span-start gspan)
		  'type))))
    
    (set-span-property gspan 'dependencies-within-file depspans)
    (setq proof-last-theorem-dependencies nil)))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Menu Functions
;;
;; The following functions set up the menus which are the key way in
;; which the dependency information is used.


(defun proof-dependency-in-span-context-menu (span)
  "Make a portion of a context-sensitive menu showing proof dependencies." 
  (list
   "-------------"
   (proof-dep-make-submenu "Local Dependency..."
			   (lambda (namespan) (car namespan))
			   'proof-goto-dependency
			   (span-property span 'dependencies-within-file))
   (proof-make-highlight-depts-menu "Highlight Dependencies"
				    'proof-highlight-depcs
				    span 'dependencies-within-file)
   (proof-dep-make-submenu "Local Dependents..."
			   (lambda (namepos) (car namepos))
			   'proof-goto-dependency
			   (span-property span 'dependents))
   (proof-make-highlight-depts-menu "Highlight Dependents"
				    'proof-highlight-depts
				    span 'dependents)
   ["Unhighlight all" proof-dep-unhighlight t]
   "-------------"
   (proof-dep-make-submenu "All Dependencies..." 
			   (lambda (name) (car name))
			   'proof-show-dependency 
			   (mapcar 'list (span-property span 'dependencies)))))


(defun proof-dep-make-submenu (name namefn appfn list)
  "Make menu items for a submenu NAME, using appfn applied to each elt in LIST.
If LIST is empty, return a disabled menu item with NAME."
  (if list
      (cons name 
	    (mapcar `(lambda (l) 
		       (vector (,namefn l) 
			       (cons (quote ,appfn) l) t)) list))
    (vector name nil nil)))

(defun proof-make-highlight-depts-menu (name fn span prop)
  "Return a menu item that for highlighting dependents/depencies of SPAN."
  (let ((deps (span-property span prop)))
    (vector name `(,fn ,(span-property span 'name) (quote ,deps)) (not (not deps)))))


;;
;; Functions triggered by menus 
;;

(defun proof-goto-dependency (name span)
  ;; FIXME: check buffer is right one.  Later we'll allow switching buffer
  ;; here and jumping to different files.
  (goto-char (span-start span))
  (skip-chars-forward " \t\n"))

(defun proof-show-dependency (thm)
  ;; FIXME: make this prover independent with new regexp for print command!!
  (proof-shell-invisible-command (format "thm \"%s\";" thm)))

(defun proof-highlight-depcs (name nmspans)
  (let ((helpmsg  (concat "This item is a dependency (ancestor) of " name)))
    (while nmspans
      (let ((span (cadar nmspans)))
	(set-span-property span 'face 'proof-highlight-dependency-face)
	(set-span-property span 'mouse-highlight nil)
	(set-span-property span 'help-echo helpmsg))
      (setq nmspans (cdr nmspans)))))

(defun proof-highlight-depts (name nmspans)
  (let ((helpmsg  (concat "This item depends on (is a child of) " name)))
    (while nmspans
      (let ((span (cadar nmspans)))
	(set-span-property span 'face 'proof-highlight-dependent-face)
	(set-span-property span 'mouse-highlight nil)
	(set-span-property span 'help-echo helpmsg)
	(set-span-property span 'balloon-help helpmsg))
      (setq nmspans (cdr nmspans)))))

(defun proof-dep-unhighlight ()
  "Returned all highlighted spans in file to the proof-locked-face highlighting."
  (interactive)
  ;; FIXME: not quite right!  Will highlight spans in queue as locked too,
  ;; and covers too many spans.
  (save-excursion
    (let ((span (span-at (point-min) 'type)))
      (while span
	(pg-set-span-helphighlights span 'nohighlight)
	(set-span-property span 'face 'proof-locked-face)
	(setq span (next-span span 'type))))))




(provide 'proof-depends)
;; proof-depends.el ends here
