;;; presenter-mode.el --- Prepare the current buffer for a presentation -*- lexical-binding: t -*-

;;; Commentary:
;; A collection of utility functions to step through code as if it were slides.

;;; Code:

(require 'dash)

(defvar-local presenter-mode nil)

(defvar-local presenter-centered-lines-delimiters '(("(*** " . " ***)")
                                           ("(*+ " . " +*)")
                                           ("(*! " . " !*)"))
  "Markers indicating centered lines.")

(defvar-local presenter-hidden-block-delimiters
  '(("(* begin hide *)" . "(* end hide *)")))

(defconst presenter--auto-inserted-symbol 'presenter--auto-inserted)
(defconst presenter--marker-symbol 'presenter--marker)
(defconst presenter--hiding-symbol 'hiding)
(defconst presenter--centering-symbol 'centering)
(defconst presenter--separator-symbol 'separator)
(defconst presenter--narrowing-symbol 'narrowing)

(defvar-local presenter--narrowing-left-overlay nil
  "Overlay used to narrow the buffer on the left.")

(defvar-local presenter--narrowing-right-overlay nil
  "Overlay used to narrow the buffer on the right.")

(defconst presenter-zero-width-space (propertize "​" 'face 'default))

(defun presenter--hide-for-narrowing-left (end)
  "Hide 1 .. END, simulating narrowing."
  (unless presenter--narrowing-left-overlay
    (setq presenter--narrowing-left-overlay (make-overlay (point-min) end nil nil nil)))
  (overlay-put presenter--narrowing-left-overlay presenter--marker-symbol presenter--narrowing-symbol)
  (overlay-put presenter--narrowing-left-overlay 'priority 1000)
  (overlay-put presenter--narrowing-left-overlay 'display presenter-zero-width-space)
  (move-overlay presenter--narrowing-left-overlay (point-min) end))

(defun presenter--hide-for-narrowing-right (beg)
  "Hide BEG .. ‘point-max’, simulating narrowing."
  (unless presenter--narrowing-right-overlay
    (setq presenter--narrowing-right-overlay (make-overlay beg (point-max) nil t t)))
  (overlay-put presenter--narrowing-right-overlay presenter--marker-symbol presenter--narrowing-symbol)
  (overlay-put presenter--narrowing-right-overlay 'priority 1000)
  (overlay-put presenter--narrowing-right-overlay 'display presenter-zero-width-space)
  (if (> beg (point-max))
      (delete-overlay presenter--narrowing-right-overlay)
    (move-overlay presenter--narrowing-right-overlay beg (point-max))))

(defun presenter--narrowed-region ()
  "Compute the currently shown region."
  (cons (or (when presenter--narrowing-left-overlay
              (overlay-end presenter--narrowing-left-overlay))
            (point-min))
        (or (when presenter--narrowing-right-overlay
              (overlay-start presenter--narrowing-right-overlay))
            (point-max))))

(defmacro presenter--with-widening (&rest body)
  "Run BODY without overlay-based narrowing.
Do not modify the contents of the buffer in BODY."
  (declare (indent defun))
  (let ((region-sym (make-symbol "region")))
    `(let ((,region-sym (presenter--narrowed-region)))
       (presenter-widen)
       (unwind-protect
           ,@body
         (presenter--narrow-to-region (car ,region-sym) (cdr ,region-sym))))))

(defun presenter-widen ()
  "Remove the custom narrowing that we introduced."
  (interactive)
  (dolist (ov (list presenter--narrowing-left-overlay presenter--narrowing-right-overlay))
    (when ov (delete-overlay ov))))

(defun presenter--narrow-to-region (beg end)
  "Implement narrowing to BEG .. END using overlays.
Otherwise many packages are broken."
  (presenter-widen)
  (presenter--hide-for-narrowing-left beg)
  (presenter--hide-for-narrowing-right end)) ;; 1+?

(defun presenter--move-point-out-of-narrowing-overlays ()
  "Move point out of narrowing overlays."
  (when presenter-mode
    (let ((narrowed-region (presenter--narrowed-region)))
      (when (< (point) (car narrowed-region))
        (goto-char (car narrowed-region)))
      (when (> (point) (cdr narrowed-region))
        (goto-char (cdr narrowed-region))))))

(defun presenter--auto-inserted-overlay (ov)
  "Check if OV covers text that was inserted by us."
  (overlay-get ov presenter--auto-inserted-symbol))

(defun presenter--own-overlay (ov)
  "Return OV's ‘presenter--marker-symbol’."
  (overlay-get ov presenter--marker-symbol))

(defun presenter--make-overlay (beg end which)
  "Add an overlay on BEG .. END.
Tag the inserted overlay with WHICH."
  ;; front-advance is set so the overlay doesn't extend.
  (let ((ov (make-overlay beg end (current-buffer) t nil)))
    (overlay-put ov presenter--marker-symbol which)
    (overlay-put ov 'priority 0)
    ov))

(defun presenter--add-centering-display-spec (pos spec)
  "Add an overlay at POS with display SPEC.
If POS is a cons (start . end), do not modify the buffer's
contents, and apply the spacing overlay to that region.  If POS
is a number or marker, insert a space and add the overlay to it.
If a space was inserted, mark it such, so it can be
deleted by the next recentering."
  (let* ((beg (if (consp pos) (car pos) pos))
         (end (if (consp pos) (cdr pos) (save-excursion
                                          (goto-char pos)
                                          (insert " ")
                                          (point))))
         (ov (presenter--make-overlay beg end presenter--centering-symbol)))
    (overlay-put ov presenter--auto-inserted-symbol (not (consp pos)))
    (overlay-put ov 'display spec)))

(defun presenter--remove-overlays (beg end &optional which)
  "Remove our own overlays in BEG .. END.
Only remove the overlays whose ‘presenter--marker-symbol’ is
WHICH.  If WHICH is null, remove all of them."
  (dolist (ov (overlays-in beg end))
    (-when-let* ((tag (presenter--own-overlay ov)))
      (when (or (null which) (eq tag which))
        (when (presenter--auto-inserted-overlay ov)
          (delete-region (overlay-start ov) (overlay-end ov)))
        (delete-overlay ov)))))

(defun presenter--remove-all-overlays (&optional which)
  "Remove all of our overlays with tag WHICH."
  (presenter--remove-overlays (point-min) (point-max) which))

(defun presenter--hide-region-for-centering (region)
  "Temporarily hide REGION, ensuring proper width calculations.
If REGION is nil, do nothing."
  (when region
    (presenter--add-centering-display-spec region presenter-zero-width-space)))

(defun presenter--measure-region (beg end)
  "Measure width of string in BEG .. END in pixels."
  (presenter--with-widening
    (car (window-text-pixel-size nil beg end))))

(defun presenter--center-current-line (&optional left-region right-region)
  "Center current line, pixelwise.
If LEFT-REGION or RIGHT-REGION is specified, hide the
corresponding text with an overlay of the right width, without
modifying the buffer's contents.  Otherwise, insert a space and
hide it with an overlay."
  (interactive)
  (presenter--remove-overlays (point-at-bol) (point-at-eol) presenter--centering-symbol)
  (presenter--hide-region-for-centering left-region)
  (presenter--hide-region-for-centering right-region)
  (let* ((title-width (presenter--measure-region (point-at-bol) (point-at-eol)))
         (window-width (window-body-width nil t))
         (padding (max 0 (- window-width title-width)))
         (spacer-spec `(space :width (,(floor (* padding 0.5))))))
    (presenter--remove-overlays (point-at-bol) (point-at-eol) presenter--centering-symbol)
    (presenter--add-centering-display-spec (or left-region (point-at-bol)) spacer-spec)
    (presenter--add-centering-display-spec (or right-region (point-at-eol)) spacer-spec)))

(defun presenter--construct-centering-regexp ()
  "Construct a regexp to find lines to center.
The regexp matches lines that contain both elements of
‘presenter-centered-lines-delimiters’."
  (concat "\\(?:"
          (mapconcat
           (lambda (pair)
             (concat "\\(?:^.*?" "\\(?1:" (regexp-quote (car pair)) "\\s-*\\)"
                     ".*?"
                     "\\(?2:\\s-*" (regexp-quote (cdr pair)) "\\)" ".*?$\\)"))
           presenter-centered-lines-delimiters "\\|")
          "\\)"))

(defvar-local presenter--window-width nil
  "Cache of the current window width.")

(defun presenter--recenter-annotated-lines (&optional beg end)
  "Center all annotated lines in BEG .. END, pixelwise.
BEG .. END covers the whole buffer by default."
  (save-excursion
    (setq beg (or beg (point-min)))
    (setq end (or end (point-max)))
    (when (and (eq beg (point-min)) (eq end (point-max)))
      (setq presenter--window-width (window-width nil t)))
    (let ((re (presenter--construct-centering-regexp)))
      (goto-char beg)
      (while (re-search-forward re end t)
        (presenter--center-current-line
         (cons (match-beginning 1) (match-end 1))
         (cons (match-beginning 2) (match-end 2)))))))

(defun presenter--recenter-annotated-lines-in-all-buffers (&optional frame)
  "Recenter annotated lines all displayed buffers of FRAME."
  (dolist (win (window-list frame 'never))
    (with-selected-window win
      (with-current-buffer (window-buffer)
        (when (and presenter-mode (not (eq (window-width nil t) presenter--window-width)))
          (message "Recentering")
          (presenter--recenter-annotated-lines))))))

(defun presenter--recenter-current-line ()
  "Center current line, if needed, pixelwise."
  (presenter--recenter-annotated-lines (point-at-bol) (point-at-eol)))

(defun presenter--add-invisibility-overlays ()
  "Hide sections delimited by ‘presenter-hidden-block-delimiters’."
  (presenter--remove-all-overlays presenter--hiding-symbol)
  (save-excursion
    (pcase-dolist (`(,beg . ,end) presenter-hidden-block-delimiters)
      (goto-char (point-min))
      (let ((re (concat (regexp-quote beg) "\\([^\0]*?\\)" (regexp-quote end))))
        (while (re-search-forward re nil t)
          (let ((ov (presenter--make-overlay (match-beginning 1) (match-end 1) presenter--hiding-symbol)))
            (overlay-put ov 'invisible 'presenter)))))))

(defconst presenter--invisibility-spec '(presenter . t)
  "Invisibility spec for presenter mode.")

(defun presenter--update-invisibility-spec (turn-on)
  "Update current buffer's invisibility spec.
If TURN-ON is non-nil, add ‘presenter--invisibility-spec’ to it;
otherwise, remove it."
  (if turn-on
      (add-to-invisibility-spec presenter--invisibility-spec)
    (remove-from-invisibility-spec presenter--invisibility-spec)))

(defun presenter-toggle-blocks ()
  "Show or hide hidden blocks in the current buffer."
  (interactive)
  (presenter--update-invisibility-spec (not (memq presenter--invisibility-spec buffer-invisibility-spec))))

(defun presenter-refresh ()
  "Apply all ‘presenter-mode’ prettifications."
  (interactive)
  (presenter--add-invisibility-overlays)
  (presenter--recenter-annotated-lines))

(defvar presenter-slide-separator "(******************************************************************************)\n"
  "String used to separate slides.")

(defun presenter--beginning-of-slide-re ()
  "Compute a regexp describing the beginning of slides."
  ;; Include "." to ensure that the regexp doesn't have 0-width
  (concat "\\(\\`\\|" (regexp-quote presenter-slide-separator) "\\)[^0]"))

(defun presenter--end-of-slide-re ()
  "Compute a regexp describing the end of slides."
  (concat "\\(\\'\\|" (regexp-quote presenter-slide-separator) "\\)"))

(defun presenter--point-at-bos ()
  "Find starting point of current slide.
May return incorrect results at end of slide."
  (save-excursion
    (if (and (looking-at (presenter--beginning-of-slide-re))
             (< (point) (cdr (presenter--narrowed-region))))
        (point)
      (re-search-backward (presenter--beginning-of-slide-re) nil t)
      (match-beginning 1))))

(defun presenter--point-at-eos ()
  "Find end point of current slide."
  (save-excursion
    (when (looking-at (presenter--beginning-of-slide-re))
      (goto-char (match-end 1)))
    (re-search-forward (presenter--end-of-slide-re) nil t)
    (match-beginning 1)))

(defun presenter-beginning-of-slide ()
  "Go to starting point of current slide."
  (interactive)
  (goto-char (presenter--point-at-bos)))

(defun presenter-narrow-to-current-slide ()
  "Narrow buffer to current slide, and hide initial slide marker."
  (presenter--remove-all-overlays presenter--separator-symbol)
  (presenter--narrow-to-region (presenter--point-at-bos) (presenter--point-at-eos))
  (presenter-beginning-of-slide)
  (when (looking-at (regexp-quote presenter-slide-separator))
    (let ((ov (make-overlay (match-beginning 0) (match-end 0) (current-buffer) nil t)))
      (overlay-put ov presenter--marker-symbol presenter--separator-symbol)
      (overlay-put ov 'display presenter-zero-width-space)
      (overlay-put ov 'priority 1))))

(defun presenter-rewind ()
  "Rewind to the first slide of the talk."
  (goto-char (point-min))
  (presenter-narrow-to-current-slide))

(defun presenter-forward (&optional n)
  "Go forward N (default: 1) slides."
  (interactive)
  (presenter-beginning-of-slide)
  (re-search-forward (presenter--beginning-of-slide-re) nil t (1+ (or n 1)))
  (presenter-narrow-to-current-slide))

(defun presenter-backward (&optional n)
  "Go forward N (default: 1) slides."
  (interactive)
  (presenter-beginning-of-slide)
  (re-search-backward (presenter--beginning-of-slide-re) nil t (or n 1))
  (presenter-narrow-to-current-slide))

(defvar presenter-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<f5>") #'presenter-refresh)
    (define-key map (kbd "<prior>") #'presenter-backward)
    (define-key map (kbd "<next>") #'presenter-forward)
    map))

(define-minor-mode presenter-mode
  "Prepare the current buffer for presentations."
  :lighter " 🎥"
  :variable presenter-mode
  :map 'presenter-mode-map
  (presenter-widen)
  (if presenter-mode
      (progn
        (presenter-design-mode -1)
        (add-hook 'window-configuration-change-hook #'presenter--recenter-annotated-lines-in-all-buffers nil t)
        (add-hook 'post-command-hook #'presenter--move-point-out-of-narrowing-overlays nil t)
        (presenter--update-invisibility-spec t)
        (presenter-refresh)
        (goto-char (point-min))
        (presenter-narrow-to-current-slide))
    (presenter--remove-all-overlays)
    (presenter--update-invisibility-spec nil)
    (remove-hook 'post-command-hook #'presenter--move-point-out-of-narrowing-overlays t)
    (remove-hook 'window-configuration-change-hook #'presenter--recenter-annotated-lines-in-all-buffers t)))

(defun presenter-insert-delimiter ()
  "Insert a slide delimiter on the current line."
  (interactive)
  (insert presenter-slide-separator))

(defun presenter-insert-pair (pair)
  "Insert PAIR on the current line."
  (insert (car pair))
  (save-excursion
    (insert (cdr pair))))

(defun presenter-insert-pair-0 ()
  "Insert hidden code delimiters."
  (interactive)
  (presenter-insert-pair (nth 0 presenter-hidden-block-delimiters)))

(defun presenter-insert-pair-1 ()
  "Insert the 1st-level centering delimiters."
  (interactive)
  (presenter-insert-pair (nth 0 presenter-centered-lines-delimiters)))

(defun presenter-insert-pair-2 ()
  "Insert the 2nd-level centering delimiters."
  (interactive)
  (presenter-insert-pair (nth 1 presenter-centered-lines-delimiters)))

(defun presenter-insert-pair-3 ()
  "Insert the 3rd-level centering delimiters."
  (interactive)
  (presenter-insert-pair (nth 2 presenter-centered-lines-delimiters)))

(defvar presenter-design-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C--") #'presenter-insert-delimiter)
    (define-key map (kbd "C-c C-0") #'presenter-insert-pair-0)
    (define-key map (kbd "C-c C-1") #'presenter-insert-pair-1)
    (define-key map (kbd "C-c C-2") #'presenter-insert-pair-2)
    (define-key map (kbd "C-c C-3") #'presenter-insert-pair-3)
    map))

(define-minor-mode presenter-design-mode
  "Work on the current buffer for presentations."
  :lighter " 🎥 -design"
  :map 'presenter-design-mode-map
  (when presenter-design-mode
    (presenter-mode -1)))

(provide 'presenter-mode)
;;; presenter-mode.el ends here
