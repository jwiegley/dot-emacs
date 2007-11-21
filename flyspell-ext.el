(eval-after-load "flyspell"
  '(progn
     (defun flyspell-highlight-incorrect-region (beg end poss)
       "Set up an overlay on a misspelled word, in the buffer from BEG to END."
       (let ((inhibit-read-only t))
	 (unless (run-hook-with-args-until-success
		  'flyspell-incorrect-hook beg end poss)
	   (if (or flyspell-highlight-properties
		   (not (flyspell-properties-at-p beg)))
	       (progn
		 ;; we cleanup current overlay at the same position
		 (if (and (not flyspell-persistent-highlight)
			  (overlayp flyspell-overlay))
		     (delete-overlay flyspell-overlay)
		   (let ((overlays (overlays-at beg)))
		     (while (consp overlays)
		       (if (flyspell-overlay-p (car overlays))
			   (delete-overlay (car overlays)))
		       (setq overlays (cdr overlays)))))
		 ;; now we can use a new overlay
		 (setq flyspell-overlay
		       (make-flyspell-overlay
			beg end 'flyspell-incorrect-face
			'highlight)))))))

     (defun flyspell-highlight-duplicate-region (beg end poss)
       "Set up an overlay on a duplicated word, in the buffer from BEG to END."
       (let ((inhibit-read-only t))
	 (unless (run-hook-with-args-until-success
		  'flyspell-incorrect-hook beg end poss)
	   (if (or flyspell-highlight-properties
		   (not (flyspell-properties-at-p beg)))
	       (progn
		 ;; we cleanup current overlay at the same position
		 (if (and (not flyspell-persistent-highlight)
			  (overlayp flyspell-overlay))
		     (delete-overlay flyspell-overlay)
		   (let ((overlays (overlays-at beg)))
		     (while (consp overlays)
		       (if (flyspell-overlay-p (car overlays))
			   (delete-overlay (car overlays)))
		       (setq overlays (cdr overlays)))))
		 ;; now we can use a new overlay
		 (setq flyspell-overlay
		       (make-flyspell-overlay
			beg end 'flyspell-duplicate-face 'highlight)))))))))
