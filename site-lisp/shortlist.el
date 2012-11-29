;;; shortlist.el

(defvar SL-list nil "List of buffers for ShortList.")

(defun SL-show ()
  "Bring up short list of buffers and intercepts the next key stroke:
    [left] [right] - move through list.  Buffers will be instantly displayed.
    [kp-0] - display the complete list of buffers (bs- style)
    number next to buffer - display buffer associated with the number."
  (interactive)
  (let (loop-fl ndx ky kys) 
    (setq loop-fl t)
    (if (not SL-list) ;; if no buffers in list, bring up bs list immediately
	(bs-show-page)
      (while loop-fl  ;; else allow user to use the short list
	(setq loop-fl nil)
	(setq ndx (SL-show-line))
	(setq ky (read-key-sequence-vector nil))
	(setq kys (format "%S" ky))
	(cond
	 ((string-match "\\[7\\]" kys) ; ^G quitting
	  (setq quit-flag t)) 
 	 ((string-match "\\[32\\]" kys)  ; space bar quits loop without inserting the space
	  t)
	 ((string-match (concat "\\[48\\]\\|\\[49\\]\\|\\[50\\]\\|\\[51\\]\\|\\[52\\]\\|"
				"\\[53\\]\\|\\[54\\]\\|\\[55\\]\\|\\[56\\]\\|\\[57\\]") kys)
	  (switch-to-buffer (nth (- (aref ky 0) 48) SL-list)) (setq loop-fl t))  ; number key - load numbered buffer
	 ((string-match "\\[kp-0\\]" kys)  ; hitting buffer list key twice brings up bs list
	  (bs-show-page))
	 ((string-match "\\[left\\]" kys)  ; move left and right through list
	  (setq ndx (SL-next-ndx ndx -1))
	  (switch-to-buffer (nth ndx SL-list))
	  (setq loop-fl t))  ; repeat loop
	 ((string-match "\\[right\\]" kys)
	  (setq ndx (SL-next-ndx ndx 1))
	  (switch-to-buffer (nth ndx SL-list))
	  (setq loop-fl t))  ; repeat loop
	 (t    ; something else: push back the typed character, exit loop, and let the parent mode handle it
	  (setq unread-command-events (append (listify-key-sequence ky) unread-command-events))))))))

(defun SL-curbuf-active()
  "Return index of current-buffer if it exists in the ShortList array, else return -1."
  (interactive)
  (let (SL-cur-active)
    (setq SL-cur-active -1)
    (dotimes (i (length SL-list))
      (if (eq (nth i SL-list) (current-buffer)) (setq SL-cur-active i)))
    SL-cur-active))

(defun SL-next-ndx (ndx direction)
  "Return index of the ShortList array for the next non-missing entry after (before) NDX.  If at end,
return the last entry.  DIRECTION is +1 to find next highest entry, -1 to find next lowest entry.  
Return -1 if entire array is nil."
  (interactive)
  ;; check for missing array
  (let (rv)
    (if (not (nth 0 SL-list)) (setq rv -1)
      (setq rv (+ ndx direction))
      (if (< rv 0) (setq rv 0)
	(if (>= rv (length SL-list)) (setq rv (- (length SL-list) 1)))))
    rv))

(defun SL-del(&optional slshow)
  "Delete current-buffer (if it exists in ShortList) from the ShortList array"
  (interactive)
  (let (ndx)
    (setq ndx (SL-curbuf-active))
    (setq SL-list (append (butlast SL-list (- (length SL-list) ndx)) (nthcdr (+ ndx 1) SL-list)))
    (if (and SL-list (>= ndx 0) slshow) (SL-show))))

(defun SL-del-key ()
  "Map ShortList del key to this."
  (interactive)
  (SL-del t))

(defun SL-add (&optional slshow)
  "Add the current buffer to the ShortList list.  Don't add buffer if already present in array."
  (interactive)
  (if (= -1 (SL-curbuf-active))
      (progn
	(setq SL-list (append SL-list (list (current-buffer))))))
  (if slshow (SL-show)))

(defun SL-add-key ()
  "Map ShortList add key to this."
  (interactive)
  (SL-add t))

(defun SL-add-bs-buf ()
  "In BS, directly add buffer at the cursor to the SL-list."
  (interactive)
  (set-buffer (bs--current-buffer))
  (SL-add)
  (SL-show))
(define-key bs-mode-map [?\M-a] 'SL-add-bs-buf)

(defun SL-show-line ( )
  "Format buffer names and display them in the echo area.  Return the index to the entry for the current buffer."
  (let (line nm hilite)
    (setq line "")
    (setq hilite (SL-curbuf-active))
    ;; we know we want to switch a buffer, so show first buffer from list in current not in list - less confusing
    (if (and (= hilite -1) SL-list)
	(progn
	  (setq hilite 0)
	  (switch-to-buffer (nth 0 SL-list))))
    (dotimes (i (length SL-list))
      (setq nm (concat (format "%d:" i) (buffer-name (nth i SL-list))))
      (if (= hilite i) (add-text-properties 0 (length nm) '(face gnus-emphasis-underline-bold-italic) nm))
      (setq line (concat line nm "  ")))
    (if (string= line "") (setq line "empty buffer list"))
    (message "%s" line)
    hilite))

;; Hook function to delete the buffer from SL-list when killing a buffer.
(defun SL-kill-buffer-hook () (SL-del))
(add-hook 'kill-buffer-hook 'SL-kill-buffer-hook)

(defadvice find-alternate-file (around SL-update-list activate)
  "Advice for updating the SL-list with the new buffer when performing a find-alternate-file function."
  (let (SL-vis)
    (setq SL-vis (SL-curbuf-active))
    (SL-del)
    ad-do-it
    (if (>= SL-vis 0) (SL-add t))))

(provide 'shortlist)
