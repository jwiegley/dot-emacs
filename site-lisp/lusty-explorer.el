;;; lusty-explorer.el --- Dynamic filesystem explorer and buffer switcher
;;
;; Copyright (C) 2008-2010 Stephen Bach <this-file@sjbach.com>
;;
;; Version: 2.4
;; Created: July 27, 2010
;; Keywords: convenience, files, matching
;; Compatibility: GNU Emacs 22 and 23
;;
;; Permission is hereby granted to use and distribute this code, with or
;; without modifications, provided that this copyright notice is copied with
;; it. Like anything else that's free, lusty-explorer.el is provided *as is*
;; and comes with no warranty of any kind, either expressed or implied. In no
;; event will the copyright holder be liable for any damages resulting from
;; the use of this software.

;;; Commentary:
;;  -----------
;;
;; To install, copy this file somewhere in your load-path and add this line to
;; your .emacs:
;;
;;    (require 'lusty-explorer)
;;
;; To launch the explorer, run or bind the following commands:
;;
;;    M-x lusty-file-explorer
;;    M-x lusty-buffer-explorer
;;
;; And then use as you would `find-file' or `switch-to-buffer'. A split window
;; shows the *Lusty-Matches* buffer, which updates dynamically as you type
;; using a fuzzy matching algorithm.  One match is highlighted; you can move
;; the highlight using C-n / C-p (next, previous) and C-f / C-b (next column,
;; previous column).  Pressing TAB or RET will select the highlighted match
;; (with slightly different semantics).
;;
;; To create a new buffer with the given name, press C-x e.  To open dired at
;; the current viewed directory, press C-x d.
;;
;; Note: lusty-explorer.el benefits greatly from byte-compilation.  To byte-
;; compile this library, M-x byte-compile-file and choose lusty-explorer.el.
;; (Ignore any warnings about the cl package.) Then, restart Emacs or
;; M-x load-library and choose the newly generated lusty-explorer.elc file.
;;
;;; Customization:
;;  --------------
;;
;; To modify the keybindings, use something like:
;;
;;   (add-hook 'lusty-setup-hook 'my-lusty-hook)
;;   (defun my-lusty-hook ()
;;     (define-key lusty-mode-map "\C-j" 'lusty-highlight-next))
;;
;; Respects these variables:
;;   completion-ignored-extensions
;;
;; Latest release: <http://www.emacswiki.org/cgi-bin/wiki/LustyExplorer>
;; Development:    <http://github.com/sjbach/lusty/tree/master>
;;

;;; Contributors:
;;
;; Jan Rehders
;; Hugo Schmitt
;; Volkan Yazici
;; René Kyllingstad
;; Alex Schroeder
;;

;;; Code:

;; Used for many functions and macros.
(require 'cl)

;; Used only for its faces (for color-theme).
(require 'font-lock)

(declaim (optimize (speed 3) (safety 0)))

(defgroup lusty-explorer nil
  "Quickly open new files or switch among open buffers."
  :group 'extensions
  :group 'convenience
  :version "23")

(defcustom lusty-setup-hook nil
  "Hook run after the lusty keymap has been setup.
Additional keys can be defined in `lusty-mode-map'."
  :type 'hook
  :group 'lusty-explorer)

(defcustom lusty-idle-seconds-per-refresh 0.05
  "Seconds to wait for additional input before updating matches window.
Can be floating point; 0.05 = 50 milliseconds.  Set to 0 to disable.
Note: only affects `lusty-file-explorer'; `lusty-buffer-explorer' is
always immediate."
  :type 'number
  :group 'lusty-explorer)

(defcustom lusty-buffer-MRU-contribution 0.1
  "How much influence buffer recency-of-use should have on ordering of
buffer names in the matches window; 0.10 = %10."
  :type 'float
  :group 'lusty-explorer)

(defvar lusty-match-face font-lock-function-name-face)
(defvar lusty-directory-face font-lock-type-face)
(defvar lusty-slash-face font-lock-keyword-face)
(defvar lusty-file-face font-lock-string-face)

(defvar lusty-buffer-name " *Lusty-Matches*")
(defvar lusty-prompt ">> ")
(defvar lusty-column-separator "    ")
(defvar lusty-no-matches-string
  (propertize "-- NO MATCHES --" 'face 'font-lock-warning-face))
(defvar lusty-truncated-string
  (propertize "-- TRUNCATED --" 'face 'font-lock-comment-face))

(defvar lusty-mode-map nil
  "Minibuffer keymap for `lusty-file-explorer' and `lusty-buffer-explorer'.")

;;;###autoload
(defun lusty-file-explorer ()
  "Launch the file/directory mode of LustyExplorer."
  (interactive)
  (lusty--define-mode-map)
  (let* ((lusty--active-mode :file-explorer)
         (lusty--ignored-extensions-regex
           (concat "\\(?:" (regexp-opt completion-ignored-extensions) "\\)$"))
         (minibuffer-local-filename-completion-map lusty-mode-map)
         (file
          ;; read-file-name is silly in that if the result is equal to the
          ;; dir argument, it gets converted to the default-filename
          ;; argument.  Set it explicitly to "" so if lusty-launch-dired is
          ;; called in the directory we start at, the result is that directory
          ;; instead of the name of the current buffer.
          (lusty--run 'read-file-name default-directory "")))
    (when file
      (switch-to-buffer
       (find-file-noselect
        (expand-file-name file))))))

;;;###autoload
(defun lusty-buffer-explorer ()
  "Launch the buffer mode of LustyExplorer."
  (interactive)
  (lusty--define-mode-map)
  (let* ((lusty--active-mode :buffer-explorer)
         (minibuffer-local-completion-map lusty-mode-map)
         (buffer (lusty--run 'read-buffer)))
    (when buffer
      (switch-to-buffer buffer))))

;;;###autoload
(defun lusty-highlight-next ()
  "Highlight the next match in *Lusty-Matches*."
  (interactive)
  (when (and lusty--active-mode
             (not (lusty--matrix-empty-p)))
    (destructuring-bind (x . y) lusty--highlighted-coords

      ;; Unhighlight previous highlight.
      (let ((prev-highlight
             (aref (aref lusty--matches-matrix x) y)))
        (lusty-propertize-path prev-highlight))

      ;; Determine the coords of the next highlight.
      (incf y)
      (unless (lusty--matrix-coord-valid-p x y)
        (incf x)
        (setq y 0)
        (unless (lusty--matrix-coord-valid-p x y)
          (setq x 0)))

      ;; Refresh with new highlight.
      (setq lusty--highlighted-coords (cons x y))
      (lusty-refresh-matches-buffer :use-previous-matrix))))

;;;###autoload
(defun lusty-highlight-previous ()
  "Highlight the previous match in *Lusty-Matches*."
  (interactive)
  (when (and lusty--active-mode
             (not (lusty--matrix-empty-p)))
    (destructuring-bind (x . y) lusty--highlighted-coords

      ;; Unhighlight previous highlight.
      (let ((prev-highlight
             (aref (aref lusty--matches-matrix x) y)))
        (lusty-propertize-path prev-highlight))

      ;; Determine the coords of the next highlight.
      (decf y)
      (unless (lusty--matrix-coord-valid-p x y)
        (let ((n-cols (length lusty--matches-matrix))
              (n-rows (length (aref lusty--matches-matrix 0))))
          (decf x)
          (setq y (1- n-rows))
          (unless (lusty--matrix-coord-valid-p x y)
            (setq x (1- n-cols))
            (while (not (lusty--matrix-coord-valid-p x y))
              (decf y)))))

      ;; Refresh with new highlight.
      (setq lusty--highlighted-coords (cons x y))
      (lusty-refresh-matches-buffer :use-previous-matrix))))

;;;###autoload
(defun lusty-highlight-next-column ()
  "Highlight the next column in *Lusty-Matches*."
  (interactive)
  (when (and lusty--active-mode
             (not (lusty--matrix-empty-p)))
    (destructuring-bind (x . y) lusty--highlighted-coords

      ;; Unhighlight previous highlight.
      (let ((prev-highlight
             (aref (aref lusty--matches-matrix x) y)))
        (lusty-propertize-path prev-highlight))

      ;; Determine the coords of the next highlight.
      (incf x)
      (unless (lusty--matrix-coord-valid-p x y)
        (setq x 0)
        (incf y)
        (unless (lusty--matrix-coord-valid-p x y)
          (setq y 0)))

      ;; Refresh with new highlight.
      (setq lusty--highlighted-coords (cons x y))
      (lusty-refresh-matches-buffer :use-previous-matrix))))

;;;###autoload
(defun lusty-highlight-previous-column ()
  "Highlight the previous column in *Lusty-Matches*."
  (interactive)
  (when (and lusty--active-mode
             (not (lusty--matrix-empty-p)))
    (destructuring-bind (x . y) lusty--highlighted-coords

      ;; Unhighlight previous highlight.
      (let ((prev-highlight
             (aref (aref lusty--matches-matrix x) y)))
        (lusty-propertize-path prev-highlight))

      ;; Determine the coords of the next highlight.
      (let ((n-cols (length lusty--matches-matrix))
            (n-rows (length (aref lusty--matches-matrix 0))))
        (if (and (zerop x)
                 (zerop y))
            (progn
              (setq x (1- n-cols)
                    y (1- n-rows))
              (while (not (lusty--matrix-coord-valid-p x y))
                (decf y)))
          (decf x)
          (unless (lusty--matrix-coord-valid-p x y)
            (setq x (1- n-cols))
            (decf y)
            (unless (lusty--matrix-coord-valid-p x y)
              (while (not (lusty--matrix-coord-valid-p x y))
                (decf x))))))

      ;; Refresh with new highlight.
      (setq lusty--highlighted-coords (cons x y))
      (lusty-refresh-matches-buffer :use-previous-matrix))))

;;;###autoload
(defun lusty-open-this ()
  "Open the given file/directory/buffer, creating it if not already present."
  (interactive)
  (when lusty--active-mode
    (if (lusty--matrix-empty-p)
        ;; No matches - open a new buffer/file with the current name.
        (lusty-select-current-name)
      (ecase lusty--active-mode
        (:file-explorer
         (let* ((path (minibuffer-contents-no-properties))
                (last-char (aref path (1- (length path)))))
           (if (and (file-directory-p path)
                   (not (eq last-char ?/))) ; <-- FIXME nonportable?
               ;; Current path is a directory, sans-slash.  Open in dired.
               (lusty-select-current-name)
             ;; Just activate the current match as normal.
             (lusty-select-match))))
        (:buffer-explorer (lusty-select-match))))))

;;;###autoload
(defun lusty-select-match ()
  "Activate the highlighted match in *Lusty-Matches* - recurse if dir, open if file/buffer."
  (interactive)
  (destructuring-bind (x . y) lusty--highlighted-coords
    (when (and lusty--active-mode
               (not (lusty--matrix-empty-p)))
      (assert (lusty--matrix-coord-valid-p x y))
      (let ((selected-match
             (aref (aref lusty--matches-matrix x) y)))
        (ecase lusty--active-mode
          (:file-explorer (lusty--file-explorer-select selected-match))
          (:buffer-explorer (lusty--buffer-explorer-select selected-match)))))))

;;;###autoload
(defun lusty-select-current-name ()
  "Open the given file/buffer or create a new buffer with the current name."
  (interactive)
  (when lusty--active-mode
    (exit-minibuffer)))

;;;###autoload
(defun lusty-launch-dired ()
  "Launch dired at the current directory."
  (interactive)
  (when (eq lusty--active-mode :file-explorer)
    (let* ((path (minibuffer-contents-no-properties))
           (dir (lusty-normalize-dir (file-name-directory path))))
      (lusty-set-minibuffer-text dir)
      (exit-minibuffer))))

;; TODO:
;; - highlight opened buffers in filesystem explorer
;; - FIX: deal with permission-denied
;; - C-e/C-a -> last/first column?
;; - config var: C-x d opens highlighted dir instead of current dir

(defvar lusty--active-mode nil)
(defvar lusty--wrapping-ido-p nil)
(defvar lusty--initial-window-config nil)
(defvar lusty--previous-minibuffer-contents nil)
(defvar lusty--current-idle-timer nil)
(defvar lusty--ignored-extensions-regex
  ;; Recalculated at execution time.
  (concat "\\(?:" (regexp-opt completion-ignored-extensions) "\\)$"))

(defvar lusty--highlighted-coords (cons 0 0))  ; (x . y)

;; Set by lusty--compute-layout-matrix
(defvar lusty--matches-matrix (make-vector 0 nil))
(defvar lusty--matrix-column-widths '())
(defvar lusty--matrix-truncated-p nil)

(when lusty--wrapping-ido-p
  (require 'ido))
(defvar ido-text) ; silence compiler warning

(defsubst lusty--matrix-empty-p ()
  (zerop (length lusty--matches-matrix)))
(defsubst lusty--matrix-coord-valid-p (x y)
  (not (or (minusp x)
           (minusp y)
           (>= x (length lusty--matches-matrix))
           (>= y (length (aref lusty--matches-matrix 0)))
           (null (aref (aref lusty--matches-matrix x) y)))))

(defun lusty-sort-by-fuzzy-score (strings abbrev)
  ;; TODO: case-sensitive when abbrev contains capital letter
  (let* ((strings+scores
          (loop for str in strings
                for score = (LM-score str abbrev)
                unless (zerop score)
                collect (cons str score)))
         (sorted
          (sort* strings+scores '> :key 'cdr)))
    (mapcar 'car sorted)))

(defun lusty-normalize-dir (dir)
  "Clean up the given directory path."
  (if (and dir (plusp (length dir)))
      (setq dir (abbreviate-file-name
                 (expand-file-name
                  (substitute-in-file-name dir))))
    (setq dir "."))
  (and (file-directory-p dir)
       dir))

(defun lusty-complete-env-variable (path)
  "Look for an environment variable in PATH and try to complete it as
much as possible."
  (when (string-match "\$\\([[:word:]_]+\\)" path)
    (let* ((partial-var (match-string 1 path))
           (vars (mapcar (lambda (x)
                           (string-match "^[^=]+" x)
                           (match-string 0 x))
                         (remove-if-not
                          (lambda (x)
                            (string-match (concat "^" partial-var) x))
                          process-environment)))
           (longest-completion (try-completion partial-var vars)))
      (cond ((eq t longest-completion) nil)
            ((null longest-completion) nil)
            ((> (length longest-completion) (length partial-var))
             (replace-regexp-in-string (concat "\$" partial-var)
                                       (concat "\$" longest-completion)
                                       path t t))))))

(defun lusty-filter-buffers (buffers)
  "Return BUFFERS converted to strings with hidden buffers removed."
  (macrolet ((ephemeral-p (name)
               `(eq (string-to-char ,name) ?\ )))
    (loop for buffer in buffers
          for name = (buffer-name buffer)
          unless (ephemeral-p name)
          collect name)))

;; Written kind-of silly for performance.
(defun lusty-filter-files (file-portion files)
  "Return FILES with './' removed and hidden files if FILE-PORTION
does not begin with '.'."
  (macrolet ((leading-dot-p (str)
               `(eq (string-to-char ,str) ?.))
             (pwd-p (str)
               `(string= ,str "./"))
             (ignored-p (name)
               `(string-match lusty--ignored-extensions-regex ,name)))
    (let ((filtered-files '()))
      (if (leading-dot-p file-portion)
          (dolist (file files)
            (unless (or (pwd-p file)
                        (ignored-p file))
              (push file filtered-files)))
        (dolist (file files)
          (unless (or (leading-dot-p file)
                      (ignored-p file))
            (push file filtered-files))))
      (nreverse filtered-files))))

(defun lusty-set-minibuffer-text (&rest args)
  "Sets ARGS into the minibuffer after the prompt."
  (assert (minibufferp))
  (delete-region (minibuffer-prompt-end) (point-max))
  (apply 'insert args))

(defun lusty--file-explorer-select (match)
  (let* ((path (minibuffer-contents-no-properties))
         (var-completed-path (lusty-complete-env-variable path)))
    (if var-completed-path
        ;; We've completed a variable name (at least partially) -- set it and
        ;; leave, since it's confusing to do two kinds of completion at once.
        (lusty-set-minibuffer-text var-completed-path)
      (let* ((dir (file-name-directory path))
             (file-portion (file-name-nondirectory path))
             (normalized-dir (lusty-normalize-dir dir)))
        ;; Clean up the path when selecting, in case we recurse.
        (lusty-set-minibuffer-text normalized-dir match)
        (if (file-directory-p (concat normalized-dir match))
            (progn
              (setq lusty--highlighted-coords (cons 0 0))
              (lusty-refresh-matches-buffer))
          (minibuffer-complete-and-exit))))))

(defun lusty--buffer-explorer-select (match)
  (lusty-set-minibuffer-text match)
  (minibuffer-complete-and-exit))

;; This may seem overkill, but it's the only way I've found to update the
;; matches list for every edit to the minibuffer.  Wrapping the keymap can't
;; account for user bindings or commands and would also fail for viper.
(defun lusty--post-command-function ()
  (assert lusty--active-mode)
  (when (and (minibufferp)
             (or (null lusty--previous-minibuffer-contents)
                 (not (string= lusty--previous-minibuffer-contents
                               (minibuffer-contents-no-properties)))))

    (let ((startup-p (null lusty--initial-window-config)))

      (when startup-p
        (lusty--setup-matches-window))

      (setq lusty--previous-minibuffer-contents
            (minibuffer-contents-no-properties))
      (setq lusty--highlighted-coords
            (cons 0 0))

      ;; Refresh matches.
      (if (or startup-p
              (null lusty-idle-seconds-per-refresh)
              (zerop lusty-idle-seconds-per-refresh)
              (eq lusty--active-mode :buffer-explorer))
          ;; No idle timer on first refresh, and never for buffer explorer.
          (lusty-refresh-matches-buffer)
        (when lusty--current-idle-timer
          (cancel-timer lusty--current-idle-timer))
        (setq lusty--current-idle-timer
              (run-with-idle-timer lusty-idle-seconds-per-refresh nil
                                   'lusty-refresh-matches-buffer))))))

;; Cribbed with modification from tail-select-lowest-window.
(defun lusty-lowest-window ()
  "Return the lowest window on the frame."
  (let* ((current-window (if (minibufferp)
                             (next-window (selected-window) :skip-mini)
                           (selected-window)))
         (lowest-window current-window)
         (bottom-edge (fourth (window-pixel-edges current-window)))
         (last-window (previous-window current-window :skip-mini))
         (window-search-p t))
    (while window-search-p
      (let* ((this-window (next-window current-window :skip-mini))
             (next-bottom-edge (fourth (window-pixel-edges this-window))))
        (when (< bottom-edge next-bottom-edge)
          (setq bottom-edge next-bottom-edge)
          (setq lowest-window this-window))
        (setq current-window this-window)
        (when (eq last-window this-window)
          (setq window-search-p nil))))
    lowest-window))

(defun lusty-max-window-height ()
  "Return the expected maximum allowable height of a window on this frame"
  ;; FIXME: are there cases where this is incorrect?
  (let* ((lusty-window
          (get-buffer-window
           (get-buffer-create lusty-buffer-name)))
         (other-window
          ;; In case the *LustyMatches* window was closed
          (or lusty-window
              (if (minibufferp)
                  (next-window (selected-window) :skip-mini)
                (selected-window))))
         (test-window
          (or lusty-window other-window)))
    (assert test-window)
    (- (frame-height)
       ;; Account for modeline and/or header...
       (- (window-height test-window)
          (window-body-height test-window))
       ;; And minibuffer height.
       (window-height (minibuffer-window)))))

(defun lusty-max-window-width ()
  (frame-width))

(defun lusty--setup-matches-window ()
  (let ((lowest-window (lusty-lowest-window))
        (lusty-buffer (get-buffer-create lusty-buffer-name)))
    (save-selected-window
      (select-window lowest-window)
      (let ((new-lowest
             ;; Create the window for lusty-buffer
             (split-window-vertically)))
        (select-window new-lowest)
        ;; Try to get a window covering the full frame.  Sometimes
        ;; this takes more than one try, but we don't want to do it
        ;; infinitely in case of weird setups.
        (loop repeat 5
              while (< (window-width) (frame-width))
              do
              (condition-case nil
                  (enlarge-window-horizontally (- (frame-width)
                                                  (window-width)))
                (error
                 (return))))
        (set-window-buffer new-lowest lusty-buffer))))
  ;;
  ;; Window configuration may be restored intermittently.
  (setq lusty--initial-window-config (current-window-configuration)))

(defun lusty-refresh-matches-buffer (&optional use-previous-matrix-p)
  "Refresh *Lusty-Matches*."
  (assert (minibufferp))
  (let* ((minibuffer-text (if lusty--wrapping-ido-p
                              ido-text
                            (minibuffer-contents-no-properties))))

    (unless use-previous-matrix-p
      ;; Refresh the matches and layout matrix
      (let ((matches
             (ecase lusty--active-mode
               (:file-explorer
                (lusty-file-explorer-matches minibuffer-text))
               (:buffer-explorer
                (lusty-buffer-explorer-matches minibuffer-text)))))
        (lusty--compute-layout-matrix matches)))

    ;; Update the matches window.
    (let ((lusty-buffer (get-buffer-create lusty-buffer-name)))
      (with-current-buffer lusty-buffer
        (setq buffer-read-only t)
        (let ((buffer-read-only nil))
          (erase-buffer)
          (lusty--display-matches)
          (goto-char (point-min))))

      ;; If only our matches window is open,
      (when (one-window-p t)
        ;; Restore original window configuration before fitting the
        ;; window so the minibuffer won't grow and look silly.
        (set-window-configuration lusty--initial-window-config))
      (fit-window-to-buffer (display-buffer lusty-buffer))
      (set-buffer-modified-p nil))))

(defun lusty-buffer-list ()
  "Return a list of buffers ordered with those currently visible at the end."
  (let ((visible-buffers '()))
    (flet ((add-buffer-maybe (window)
             (let ((b (window-buffer window)))
               (unless (memq b visible-buffers)
                 (push b visible-buffers)))))
      (walk-windows 'add-buffer-maybe nil 'visible))
    (let ((non-visible-buffers
           (loop for b in (buffer-list)
                 unless (memq b visible-buffers)
                 collect b)))
      (nconc non-visible-buffers visible-buffers))))

(defun lusty-buffer-explorer-matches (match-text)
  (let ((buffers (lusty-filter-buffers (lusty-buffer-list))))
    (if (string= match-text "")
        ;; Sort by MRU.
        buffers
      ;; Sort by fuzzy score and MRU order.
      (let* ((score-table
              (loop with MRU-factor-step = (/ lusty-buffer-MRU-contribution
                                              (length buffers))
                    for b in buffers
                    for step from 0.0 by MRU-factor-step
                    for score = (LM-score b match-text)
                    for MRU-factor = (- 1.0 step)
                    unless (zerop score)
                    collect (cons b (* score MRU-factor))))
             (sorted
              (sort* score-table '> :key 'cdr)))
        (mapcar 'car sorted)))))

;; FIXME: return an array instead of a list?
(defun lusty-file-explorer-matches (path)
  (let* ((dir (lusty-normalize-dir (file-name-directory path)))
         (file-portion (file-name-nondirectory path))
         (files
          (and dir
               ; NOTE: directory-files is quicker but
               ;       doesn't append slash for directories.
               ;(directory-files dir nil nil t)
               (file-name-all-completions "" dir)))
         (filtered (lusty-filter-files file-portion files)))
    (if (or (string= file-portion "")
            (string= file-portion "."))
        (sort filtered 'string<)
      (lusty-sort-by-fuzzy-score filtered file-portion))))

(defsubst lusty-propertize-path (path)
  "Propertize the given PATH like so: <dir></> or <file>.
Uses `lusty-directory-face', `lusty-slash-face', `lusty-file-face'"
  (let ((last (1- (length path))))
    ;; Note: shouldn't get an empty path, so for performance
    ;; I'm not going to check for that case.
    (if (eq (aref path last) ?/) ; <-- FIXME nonportable?
        (progn
          ;; Directory
          (put-text-property 0 last 'face lusty-directory-face path)
          (put-text-property last (1+ last) 'face lusty-slash-face path))
      (put-text-property 0 (1+ last) 'face lusty-file-face path)))
  path)

(defun lusty--compute-layout-matrix (items)
  (let* ((max-visible-rows (1- (lusty-max-window-height)))
         (max-width (lusty-max-window-width))
         (upper-bound most-positive-fixnum)
         (n-items (length items))
         (lengths-v (make-vector n-items 0))
         (separator-length (length lusty-column-separator)))

    (let ((length-of-longest-name 0)) ; used to determine upper-bound

      ;; Initialize lengths-v
      (loop for i from 0
            for item in items
            for len = (length item)
            do
            (aset lengths-v i len)
            (setq length-of-longest-name
                  (max length-of-longest-name len)))

      ;; Calculate upper-bound
      (let ((width (+ length-of-longest-name
                      separator-length))
            (columns 1)
            (sorted-shortest (sort (append lengths-v nil) '<)))
        (dolist (item-len sorted-shortest)
          (incf width item-len)
          (when (> width max-width)
            (return))
          (incf columns)
          (incf width separator-length))
        (setq upper-bound (* columns max-visible-rows))))

    ;; Determine optimal row count.
    (multiple-value-bind (optimal-n-rows truncated-p)
        (cond ((endp items)
               (values 0 nil))
              ((< upper-bound n-items)
               (values max-visible-rows t))
              ((<= (reduce (lambda (a b) (+ a separator-length b))
                           lengths-v)
                   max-width)
               ;; All fits in a single row.
               (values 1 nil))
              (t
               (lusty--compute-optimal-row-count lengths-v)))
      (let ((n-columns 0)
            (column-widths '()))

        ;; Calculate n-columns and column-widths
        (loop with total-width = 0
              for start = 0 then end
              for end = optimal-n-rows then
                        (min (length lengths-v)
                             (+ end optimal-n-rows))
              while (< start end)
              for col-width = (reduce 'max lengths-v
                                      :start start
                                      :end end)
              do
              (incf total-width col-width)
              (when (> total-width max-width)
                (return))
              (incf n-columns)
              (push col-width column-widths)
              (incf total-width separator-length))
        (setq column-widths (nreverse column-widths))

        (let ((matrix
               ;; Create an empty matrix.
               (let ((col-vec (make-vector n-columns nil)))
                 (dotimes (i n-columns)
                   (aset col-vec i
                         (make-vector optimal-n-rows nil)))
                 col-vec)))

          ;; Fill the matrix with propertized matches.
          (unless (zerop n-columns)
            (let ((x 0)
                  (y 0)
                  (col-vec (aref matrix 0)))
              (dolist (item items)
                (aset col-vec y (lusty-propertize-path item))
                (incf y)
                (when (>= y optimal-n-rows)
                  (incf x)
                  (if (>= x n-columns)
                      (return)
                    (setq col-vec (aref matrix x)))
                  (setq y 0)))))

          (setq lusty--matches-matrix matrix
                lusty--matrix-column-widths column-widths
                lusty--matrix-truncated-p truncated-p))))))

;; Returns number of rows and whether this truncates the matches.
(defun* lusty--compute-optimal-row-count (lengths-v)
  ;;
  ;; Binary search; find the lowest number of rows at which we
  ;; can fit all the strings.
  ;;
  (let* ((separator-length (length lusty-column-separator))
         (n-items (length lengths-v))
         (max-visible-rows (1- (lusty-max-window-height)))
         (available-width (lusty-max-window-width))
         (lengths-h
          ;; Hashes by cons, e.g. (0 . 2), representing the width
          ;; of the column bounded by the range of [0..2].
          (make-hash-table :test 'equal
                           ; not scientific
                           :size n-items))
         ;; We've already failed for a single row, so start at two.
         (lower 1)
         (upper (1+ max-visible-rows)))

    (while (/= (1+ lower) upper)
      (let* ((n-rows (/ (+ lower upper) 2)) ; Mid-point
             (col-start-index 0)
             (col-end-index (1- n-rows))
             (total-width 0))

        (block :column-widths
          (while (< col-end-index (length lengths-v))
            (incf total-width
                  (lusty--compute-column-width
                   col-start-index col-end-index
                   lengths-v lengths-h))

            (when (> total-width available-width)
              ;; Early exit.
              (setq total-width most-positive-fixnum)
              (return-from :column-widths))

            (incf total-width separator-length)

            (incf col-start-index n-rows)
            (incf col-end-index n-rows)

            (when (and (>= col-end-index (length lengths-v))
                       (< col-start-index (length lengths-v)))
              ;; Remainder; last iteration will not be a full column.
              (setq col-end-index (1- (length lengths-v))))))

        ;; The final column doesn't need a separator.
        (decf total-width separator-length)

        (if (<= total-width available-width)
            ;; This row count fits.
            (setq upper n-rows)
          ;; This row count doesn't fit.
          (setq lower n-rows))))

    (if (> upper max-visible-rows)
        ;; No row count can accomodate all entries; have to truncate.
        ;; (-1 for the truncate indicator)
        (values (1- max-visible-rows) t)
      (values upper nil))))

(defsubst lusty--compute-column-width (start-index end-index lengths-v lengths-h)
  (if (= start-index end-index)
      ;; Single-element remainder
      (aref lengths-v start-index)
    (let* ((range (cons start-index end-index))
           (width (gethash range lengths-h)))
      (or width
          (let* ((split-point
                  (+ start-index
                     (ash (- end-index start-index) -1)))
                 (first-half
                  (lusty--compute-column-width
                   start-index split-point
                   lengths-v lengths-h))
                 (second-half
                  (lusty--compute-column-width
                   (1+ split-point) end-index
                   lengths-v lengths-h)))
            (puthash (cons start-index end-index)
                     (max first-half second-half)
                     lengths-h))))))

(defun* lusty--display-matches ()

  (when (lusty--matrix-empty-p)
    (lusty--print-no-matches)
    (return-from lusty--display-matches))

  (let* ((n-columns (length lusty--matches-matrix))
         (n-rows (length (aref lusty--matches-matrix 0))))

    ;; Highlight the selected match.
    (destructuring-bind (h-x . h-y) lusty--highlighted-coords
      (setf (aref (aref lusty--matches-matrix h-x) h-y)
            (propertize (aref (aref lusty--matches-matrix h-x) h-y)
                        'face lusty-match-face)))

    ;; Print the match matrix.
    (dotimes (y n-rows)
      (loop for column-width in lusty--matrix-column-widths
            for x from 0 upto n-columns
            do
            (let ((match (aref (aref lusty--matches-matrix x) y)))
              (when match
                (insert match)
                (when (< x (1- n-columns))
                  (let* ((spacer
                          (make-string (- column-width (length match))
                                       ?\ )))
                    (insert spacer lusty-column-separator))))))
      (insert "\n")))

  (when lusty--matrix-truncated-p
    (lusty--print-truncated)))

(defun lusty--print-no-matches ()
  (insert lusty-no-matches-string)
  (let ((fill-column (window-width)))
    (center-line)))

(defun lusty--print-truncated ()
  (insert lusty-truncated-string)
  (let ((fill-column (window-width)))
    (center-line)))


(defun lusty--define-mode-map ()
  ;; Re-generated every run so that it can inherit new functions.
  (let ((map (make-sparse-keymap)))
    (set-keymap-parent map minibuffer-local-map)
    (define-key map (kbd "RET") 'lusty-open-this)
    (define-key map "\t" 'lusty-select-match)
    (define-key map "\C-n" 'lusty-highlight-next)
    (define-key map "\C-p" 'lusty-highlight-previous)
    (define-key map "\C-s" 'lusty-highlight-next)
    (define-key map "\C-r" 'lusty-highlight-previous)
    (define-key map "\C-f" 'lusty-highlight-next-column)
    (define-key map "\C-b" 'lusty-highlight-previous-column)
    (define-key map "\C-xd" 'lusty-launch-dired)
    (define-key map "\C-xe" 'lusty-select-current-name)
    (setq lusty-mode-map map))
  (run-hooks 'lusty-setup-hook))


(defun lusty--run (read-fn &rest args)
  (let ((lusty--highlighted-coords (cons 0 0))
        (lusty--matches-matrix (make-vector 0 nil))
        (lusty--matrix-column-widths '())
        (lusty--matrix-truncated-p nil))
    (add-hook 'post-command-hook 'lusty--post-command-function t)
    (unwind-protect
        (save-window-excursion
          (apply read-fn lusty-prompt args))
      (remove-hook 'post-command-hook 'lusty--post-command-function)
      (setq lusty--previous-minibuffer-contents nil
            lusty--initial-window-config nil
            lusty--current-idle-timer nil))))


;;
;; Start LiquidMetal
;;
;; Port of Ryan McGeary's LiquidMetal fuzzy matching algorithm found at:
;;   http://github.com/rmm5t/liquidmetal/tree/master.
;;

(defconst LM--score-no-match 0.0)
(defconst LM--score-match 1.0)
(defconst LM--score-trailing 0.8)
(defconst LM--score-trailing-but-started 0.90)
(defconst LM--score-buffer 0.85)

(defsubst* LM-score (str abbrev)
  (let ((str-len (length str))
        (abbrev-len (length abbrev)))
    (cond ;((string= abbrev "")  ; Disabled; can't happen in practice
          ; LM--score-trailing)
          ((> abbrev-len str-len)
           LM--score-no-match)
          (t
           ;; Content of LM--build-score-array...
           ;; Inline for interpreted performance.
           (let* ((scores (make-vector str-len LM--score-no-match))
                  (str-lower (downcase str))
                  (abbrev-lower (downcase abbrev))
                  (last-index 0)
                  (started-p nil))
             (dotimes (i abbrev-len)
               (let ((pos (position (aref abbrev-lower i) str-lower
                                    :start last-index
                                    :end str-len)))
                 (when (null pos)
                   (return-from LM-score LM--score-no-match))
                 (when (zerop pos)
                   (setq started-p t))
                 (cond ((and (plusp pos)
                             (memq (aref str (1- pos))
                                   '(?. ?_ ?- ?\ )))
                        ;; New word.
                        (aset scores (1- pos) LM--score-match)
                        (fill scores LM--score-buffer
                              :start last-index
                              :end (1- pos)))
                       ((and (>= (aref str pos) ?A)
                             (<= (aref str pos) ?Z))
                        ;; Upper case.
                        (fill scores LM--score-buffer
                              :start last-index
                              :end pos))
                       (t
                        (fill scores LM--score-no-match
                              :start last-index
                              :end pos)))
                 (aset scores pos LM--score-match)
                 (setq last-index (1+ pos))))

             (let ((trailing-score
                    (if started-p
                        LM--score-trailing-but-started
                      LM--score-trailing)))
               (fill scores trailing-score :start last-index))

             (/ (reduce '+ scores)
                str-len ))))))

;;
;; End LiquidMetal
;;


;;
;; XEmacs compatibility functions
;;

; (unless (fboundp 'minibufferp)
;   (defun minibufferp ()
;     (eq (window-buffer (minibuffer-window))
;         (current-buffer))))
; 
; (unless (fboundp 'minibuffer-contents-no-properties)
;   (defun minibuffer-contents-no-properties ()
;     (with-current-buffer (window-buffer (minibuffer-window))
;       (let ((start (1+ (length lusty-prompt)))
;             (end (point-max)))
;         (if (>= end start)
;             (buffer-substring-no-properties start end)
;           "")))))
; 
; (unless (fboundp 'minibuffer-prompt-end)
;   (defun minibuffer-prompt-end ()
;     (1+ (length lusty-prompt))))
; 
; (unless (fboundp 'line-number-at-pos)
;   (defun line-number-at-pos (&optional pos)
;     (line-number pos)))
; 
; ;; Cribbed from cal-fit-window-to-buffer
; (unless (fboundp 'fit-window-to-buffer)
;   (defun fit-window-to-buffer (owin max-height)
;     (interactive)
;     (if owin
; 	(delete-other-windows))
;     (when (> (length (window-list nil 'nomini)) 1)
;       (let* ((window (selected-window))
; 	     (buf (window-buffer window))
; 	     (height (window-displayed-height (selected-window)))
; 	     (new-height
;               (min (with-current-buffer buf
;                      (count-lines (point-min) (point-max)))
;                    max-height))
; 	     (diff (- new-height height)))
; 	(unless (zerop diff)
; 	  (enlarge-window diff))
; 	(let ((end (with-current-buffer buf (point-max))))
; 	  (while (and (> (length (window-list nil 'nomini)) 1)
; 		      (not (pos-visible-in-window-p end)))
; 	    (enlarge-window 1)))))))


(provide 'lusty-explorer)

;;; lusty-explorer.el ends here.
