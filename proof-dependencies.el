; This file is an attempt to abstract away from the differences between
; XEmacs and FSF Emacs. Everything that is done differently between one
; or other version should be appropriately wrapped in here.

; This is currently configured for XEmacs, because at the moment Emacs19
; doesn't have enough functionality to implement nested extents.


(defvar proof-locked-hwm nil
  "Upper limit of the locked region")

(defvar proof-queue-loose-end nil
  "Limit of the queue region that is not equal to proof-locked-hwm.")


(defsubst make-span (start end)
  (make-extent start end))

(defsubst set-span-endpoints (span start end)
  (set-extent-endpoints span start end))

(defsubst set-span-start (span value)
  (set-extent-endpoints span value (extent-end-position span)))

(defsubst set-span-end (span value)
  (set-extent-endpoints span (extent-start-position span) value))

(defsubst span-property (span name)
  (extent-property span name))

(defsubst set-span-property (span name value)
  (set-extent-property span name value))

(defsubst delete-span (span)
  (delete-extent span))

(defsubst delete-spans (start end prop)
  (mapcar-extents 'delete-extent nil (current-buffer) start end  nil prop))

(defsubst span-at (pt prop)
  (extent-at pt nil prop))

(defsubst span-at-before (pt prop)
  (extent-at pt nil prop nil 'before))
  
(defsubst span-start (span)
  (extent-start-position span))

(defsubst span-end (span)
  (extent-end-position span))

(defsubst prev-span (span prop)
  (extent-at (extent-start-position span) nil prop nil 'before))

(defsubst next-span (span prop)
  (extent-at (extent-end-position span) nil prop nil 'after))

(defvar proof-locked-ext nil
  "Upper limit of the locked region")

(defvar proof-queue-ext nil
  "Upper limit of the locked region")

(defun proof-init-segmentation ()
  (setq proof-queue-loose-end nil)
  (setq proof-queue-ext (make-extent nil nil (current-buffer)))
  (set-extent-property proof-queue-ext 'start-closed t)
  (set-extent-property proof-queue-ext 'end-open t)
  (set-extent-property proof-queue-ext 'read-only t)
  (make-face 'proof-queue-face)
  (if (eq (device-class (frame-device)) 'color)
	     (set-face-background 'proof-queue-face "mistyrose")
    (set-face-background 'proof-queue-face "Black")
    (set-face-foreground 'proof-queue-face "White"))
  (set-extent-property proof-queue-ext 'face 'proof-queue-face)
  
  (setq proof-locked-hwm nil)
  (setq proof-locked-ext (make-extent nil nil (current-buffer)))
  (set-extent-property proof-locked-ext 'start-closed t)
  (set-extent-property proof-locked-ext 'end-open t)
  (set-extent-property proof-locked-ext 'read-only t)
  (if (eq (device-class (frame-device)) 'color)
      (progn (make-face 'proof-locked-face)
	     (set-face-background 'proof-locked-face "lavender")
	     (set-extent-property proof-locked-ext 'face 'proof-locked-face))
    (set-extent-property proof-locked-ext 'face 'underline)))

(defsubst proof-lock-unlocked ()
  (set-extent-property proof-locked-ext 'read-only t))

(defsubst proof-unlock-locked ()
  (set-extent-property proof-locked-ext 'read-only nil))

(defsubst proof-detach-queue ()
  (if proof-queue-ext
      (detach-extent proof-queue-ext)))

(defsubst proof-set-queue-endpoints (start end)
  (set-extent-endpoints proof-queue-ext start end))

(defsubst proof-set-queue-start (start)
  (set-extent-endpoints proof-queue-ext start 
			(extent-end-position proof-queue-ext)))

(defsubst proof-set-queue-end (end)
  (set-extent-endpoints proof-queue-ext (extent-start-position proof-queue-ext)
			end)) 

(defsubst proof-detach-segments ()
  (if proof-queue-ext
      (detach-extent proof-queue-ext))
  (if proof-locked-ext
      (detach-extent proof-locked-ext)))

(defsubst proof-set-locked-end (end)
  (set-extent-endpoints proof-locked-ext (point-min) end))

(defsubst proof-locked-end ()
  (or (and proof-locked-ext (extent-end-position proof-locked-ext))
      (point-min)))

(defsubst proof-end-of-queue ()
  (extent-end-position proof-queue-ext))

;(defsubst proof-have-color ()
;  (eq (device-class) 'color))

(defun proof-dont-show-annotations ()
  (let ((disp (make-display-table))
	(i 128))
	(while (< i 256)
	  (aset disp i "")
	  (incf i))
	(add-spec-to-specifier current-display-table disp (current-buffer))))

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
v

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



(provide 'proof-dependencies)
