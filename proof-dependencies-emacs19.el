; This file is an attempt to abstract away from the differences between
; XEmacs and FSF Emacs. Everything that is done differently between one
; or other version should be appropriately wrapped in here.

; This is currently under development for emacs19.

(defvar proof-locked-hwm nil
  "Upper limit of the locked region")

(defvar proof-queue-loose-end nil
  "Limit of the queue region that is not equal to proof-locked-hwm.")

(defvar last-span nil
  "Start of backwards-linked list of spans")

;; We build lists of spans both in the pbp buffer and in the scripting
;; buffer.
(make-variable-buffer-local 'last-span)


(defsubst span-start (span)
  (overlay-start span))

(defsubst span-end (span)
  (overlay-end span))

(defun add-span (span l)
  (cond (l (if (< (span-start span) (span-start l))
	       (progn
		 (overlay-put l 'before
			      (add-span span (overlay-get l 'before)))
		 l)
	     (overlay-put span 'before l)
	     span))
	(t span)))

(defsubst make-span (start end)
  (setq last-span (add-span (make-overlay start end) last-span)))

(defsubst set-span-endpoints (span start end)
  (move-overlay span start end))

(defsubst set-span-start (span value)
  (overlay-start span value))

(defsubst set-span-end (span value)
  (overlay-end span value))

(defsubst span-property (span name)
  (overlay-get span name))

(defsubst set-span-property (span name value)
  (overlay-put span name value))

;; relies on only being called from delete-span, and so resets value
;; of last-span
(defun remove-span (span l)
  (cond ((not l) ())
	((eq span l) (setq last-span (span-property l 'before)))
	((eq span (span-property l 'before))
	 (set-span-property l 'before (span-property span 'before))
	 l)
	(t (remove-span span (span-property l 'before)))))

(defsubst delete-span (span)
  (remove-span span last-span)
  (delete-overlay span))

(defun spans-at (start end)
  (let ((overlays nil) (pos start) (os nil))
    (while (< pos end)
      (setq os (overlays-at pos))
      (while os
	(if (not (memq (car os) overlays))
	    (setq overlays (cons (car os) overlays)))
	(setq os (cdr os)))
      (setq pos (next-overlay-change pos)))
    overlays))

(defun spans-at-prop (start end prop)
  (let ((f (cond
	    (prop (lambda (spans span)
		    (if (span-property span prop) (cons span spans)
		      spans)))
	    (t (lambda (spans span) (cons span spans))))))
    (foldl f nil (spans-at start end))))

(defun type-prop (spans span)
  (if (span-property span 'type) (cons span spans) spans))

(defun spans-at-type (start end)
  (foldl 'type-prop nil (spans-at start end)))

(defsubst delete-spans (start end prop)
  (mapcar 'delete-span (spans-at-prop start end prop)))

(defun map-spans-aux (f l)
  (cond (l (cons (funcall f l) (map-spans-aux f (span-property l 'before))))
	(t ())))

(defsubst map-spans (f)
  (map-spans-aux f last-span))

;; extent-at gives "smallest" extent at pos
;; we're assuming right now that spans don't overlap
(defun span-at (pt prop)
  (car (spans-at-prop pt (+ pt 1) prop)))

(defun find-span-aux (prop-p l)
  (cond ((not l) ())
	((funcall prop-p l) l)
	(t (find-span-aux prop-p (span-property l 'before)))))

(defun find-span (prop-p)
  (find-span-aux prop-p last-span))

(defun span-at-before (pt prop)
  (let ((prop-pt-p
	 (cond (prop (lambda (span)
		       (and (> pt (span-start span))
			    (span-property span prop))))
	       (t (lambda (span) (> pt (span-end span)))))))
    (find-span prop-pt-p)))
  
(defun prev-span (span prop)
  (let ((prev-prop-p
	 (cond (prop (lambda (span) (span-property span prop)))
	       (t (lambda (span) t)))))
    (find-span-aux prev-prop-p (span-property span 'before))))

(defun next-span-aux (prop spans)
  (cond ((not spans) nil)
	((span-property (car spans) prop) (car spans))
	(t (next-span-aux prop (cdr spans)))))

;; overlays are [start, end)
(defun next-span (span prop)
  (next-span-aux prop
		 (overlays-at (next-overlay-change (overlay-start span)))))

(defvar proof-locked-span nil
  "Upper limit of the locked region")

(defvar proof-queue-span nil
  "Upper limit of the locked region")

(defun proof-init-segmentation ()
  (setq proof-queue-loose-end nil)
  (setq proof-queue-span (make-span 0 0))
  (set-span-property proof-queue-span 'start-closed t)
  (set-span-property proof-queue-span 'end-open t)
  (set-span-property proof-queue-span 'read-only t)
  (make-face 'proof-queue-face)

;; Whether display has color or not
  (cond (running-xemacs
	 (if (eq (device-class (frame-device)) 'color)
	     (set-face-background 'proof-queue-face "mistyrose")))
	(running-emacs19
	 (if (and window-system (x-display-color-p))
	     (set-face-background 'proof-queue-face "mistyrose")))
        (t (progn
	     (set-face-background 'proof-queue-face "Black")
	     (set-face-foreground 'proof-queue-face "White"))))

  (set-span-property proof-queue-span 'face 'proof-queue-face)
  
  (setq proof-locked-hwm nil)
  (setq proof-locked-span (make-span 0 0))
  (set-span-property proof-locked-span 'start-closed t)
  (set-span-property proof-locked-span 'end-open t)
  (set-span-property proof-locked-span 'read-only t)
;; don't know how to know if it has color or not
;; Whether display has color or not
  (cond (running-xemacs
	 (if (eq (device-class (frame-device)) 'color)
	     (progn (make-face 'proof-locked-face)
		    (set-face-background 'proof-locked-face "lavender")
		    (set-span-property proof-locked-span 'face
				       'proof-locked-face))))
	(running-emacs19
	 (if (and window-system (x-display-color-p))
	     (progn (make-face 'proof-locked-face)
		    (set-face-background 'proof-locked-face "lavender")
		    (set-span-property proof-locked-span 'face
				       'proof-locked-face))))
        (t (set-span-property proof-locked-span 'face 'underline))))

;; for read-only, not done:
(defsubst proof-lock-unlocked ()
;;  (set-span-property proof-locked-span 'read-only t)
  ())

;; for read-only, not done:
(defsubst proof-unlock-locked ()
;;  (set-span-property proof-locked-span 'read-only nil)
  ())

(defsubst proof-set-queue-endpoints (start end)
  (set-span-endpoints proof-queue-span start end))

(defsubst proof-detach-queue ()
  (if proof-queue-span
      (proof-set-queue-endpoints 0 0)))

(defsubst proof-set-queue-start (start)
  (set-span-endpoints proof-queue-span start (span-end proof-queue-span)))

(defsubst proof-set-queue-end (end)
  (set-span-endpoints proof-queue-span (span-start proof-queue-span) end))

(defun proof-detach-segments ()
  (if proof-queue-span
      (set-span-endpoints proof-queue-span 0 0))
  (if proof-locked-span
      (set-span-endpoints proof-locked-span 0 0)))

(defsubst proof-set-locked-end (end)
  (set-span-endpoints proof-locked-span (point-min) end))

(defsubst proof-locked-end ()
  (or (and proof-locked-span (span-end proof-locked-span))
      (point-min)))

(defsubst proof-end-of-queue ()
  (span-end proof-queue-span))

(defun proof-dont-show-annotations ()
  (let ((disp (make-display-table))
	(i 128))
	(while (< i 256)
;; This is different from xemacs:
	  (aset disp i [])
	  (incf i))
;; I believe the following sets display table of current buffer:
	(setq buffer-display-table disp)))

;; in case Emacs is not aware of read-shell-command-map
(defvar read-shell-command-map
  (let ((map (make-sparse-keymap)))
    (if (not (fboundp 'set-keymap-parents))
        (setq map (append minibuffer-local-map map))
      (set-keymap-parents map minibuffer-local-map)
      (set-keymap-name map 'read-shell-command-map))
    (define-key map "\t" 'comint-dynamic-complete)
    (define-key map "\M-\t" 'comint-dynamic-complete)
    (define-key map "\M-?" 'comint-dynamic-list-completions)
    map)
  "Minibuffer keymap used by shell-command and related commands.")


;; in case Emacs is not aware of the function read-shell-command
(or (fboundp 'read-shell-command)
    ;; from minibuf.el distributed with XEmacs 19.11
    (defun read-shell-command (prompt &optional initial-input history)
      "Just like read-string, but uses read-shell-command-map:
\\{read-shell-command-map}"
      (let ((minibuffer-completion-table nil))
        (read-from-minibuffer prompt initial-input read-shell-command-map
                              nil (or history
                              'shell-command-history)))))



(provide 'proof-dependencies-emacs19)
