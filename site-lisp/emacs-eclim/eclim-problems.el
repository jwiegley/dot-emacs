(defgroup eclim-problems nil
  "Problems: settings for displaying the problems buffer and highlighting errors in code."
  :group 'eclim)

(defcustom eclim-problems-refresh-delay 0.5
  "The delay (in seconds) to wait before we refresh the problem list buffer after a file is saved."
  :group 'eclim-problems
  :type 'number)

(defcustom eclim-problems-resize-file-column t
  "Resizes file column in emacs-eclim problems mode"
  :group 'eclim-problems
  :type '(choice (const :tag "Off" nil)
                 (const :tag "On" t)))

(defcustom eclim-problems-show-pos nil
  "Shows problem line/column in emacs-eclim problems mode"
  :group 'eclim-problems
  :type '(choice (const :tag "Off" nil)
                 (const :tag "On" t)))

(defcustom eclim-problems-show-file-extension nil
  "Shows file extensions in emacs-eclim problems mode"
  :group 'eclim-problems
  :type '(choice (const :tag "Off" nil)
                 (const :tag "On" t)))

(defcustom eclim-problems-hl-errors t
  "Highlights errors in the problem list buffer"
  :group 'eclim-problems
  :type '(choice (const :tag "Off" nil)
                 (const :tag "On" t)))

(defface eclim-problems-highlight-error-face
  '((t (:underline "red")))
  "Face used for highlighting errors in code"
  :group 'eclim-problems)

(defface eclim-problems-highlight-warning-face
  '((t (:underline "orange")))
  "Face used for highlighting errors in code"
  :group 'eclim-problems)

(defvar eclim-autoupdate-problems t)

(defvar eclim-problems-mode-hook nil)

(defvar eclim--problems-filter-description "")
(defvar eclim--problems-project nil) ;; problems are relative to this project
(defvar eclim--problems-file nil) ;; problems are relative to this file (when eclim--problems-filefilter is non-nil)

(setq eclim-problems-mode-map
      (let ((map (make-keymap)))
        (suppress-keymap map t)
        (define-key map (kbd "a") 'eclim-problems-show-all)
        (define-key map (kbd "e") 'eclim-problems-show-errors)
        (define-key map (kbd "g") 'eclim-problems-buffer-refresh)
        (define-key map (kbd "q") 'eclim-quit-window)
        (define-key map (kbd "w") 'eclim-problems-show-warnings)
        (define-key map (kbd "f") 'eclim-problems-toggle-filefilter)
        (define-key map (kbd "c") 'eclim-problems-correct)
        (define-key map (kbd "RET") 'eclim-problems-open-current)
        map))

(define-key eclim-mode-map (kbd "C-c C-e b") 'eclim-problems)
(define-key eclim-mode-map (kbd "C-c C-e o") 'eclim-problems-open)

(defvar eclim--problems-list nil)

(defvar eclim--problems-filter nil) ;; nil -> all problems, w -> warnings, e -> errors
(defvar eclim--problems-filefilter nil) ;; should filter by file name

(defconst eclim--problems-buffer-name "*eclim: problems*")
(defconst eclim--problems-compilation-buffer-name "*compilation: eclim*")

(defun eclim--problems-mode ()
  (kill-all-local-variables)
  (buffer-disable-undo)
  (setq major-mode 'eclim-problems-mode
        mode-name "eclim/problems"
        mode-line-process ""
        truncate-lines t
        line-move-visual nil
        buffer-read-only t
        default-directory (eclim/workspace-dir))
  (setq mode-line-format
        (list "-"
              'mode-line-mule-info
              'mode-line-modified
              'mode-line-frame-identification
              'mode-line-buffer-identification

              "   "
              'mode-line-position

              "  "
              'eclim--problems-filter-description

              "  "
              'mode-line-modes
              '(which-func-mode ("" which-func-format "--"))

              'global-mode-string
              "-%-"))
  (hl-line-mode t)
  (use-local-map eclim-problems-mode-map)
  (run-mode-hooks 'eclim-problems-mode-hook))

(defun eclim--problem-goto-pos (p)
  (save-restriction
    (widen)
    (goto-char (point-min))
    (forward-line (1- (assoc-default 'line p)))
    (dotimes (i (1- (assoc-default 'column p)))
      (forward-char))))

(defun eclim--problems-apply-filter (f)
  (setq eclim--problems-filter f)
  (eclim-problems-buffer-refresh))

(defun eclim-problems-show-errors ()
  (interactive)
  (eclim--problems-apply-filter "e"))

(defun eclim-problems-toggle-filefilter ()
  (interactive)
  (setq eclim--problems-filefilter (not eclim--problems-filefilter))
  (eclim--problems-buffer-redisplay))

(defun eclim-problems-show-warnings ()
  (interactive)
  (eclim--problems-apply-filter "w"))

(defun eclim-problems-show-all ()
  (interactive)
  (eclim--problems-apply-filter nil))

(defun eclim--problems-insert-highlight (problem)
  (save-excursion
    (eclim--problem-goto-pos problem)
    (let* ((id (eclim--java-identifier-at-point t t))
           (start (car id))
           (end (+ (car id) (length (cdr id)))))
      (let ((highlight (make-overlay start end (current-buffer) t t)))
        (overlay-put highlight 'face
                     (if (eq t (assoc-default 'warning problem))
                         'eclim-problems-highlight-warning-face
                       'eclim-problems-highlight-error-face))
        (overlay-put highlight 'category 'eclim-problem)
        (overlay-put highlight 'kbd-help (assoc-default 'message problem))))))

(defun eclim--problems-clear-highlights ()
  (remove-overlays nil nil 'category 'eclim-problem))

(defadvice find-file (after eclim-problems-highlight-on-find-file activate)
  (eclim-problems-highlight))
(defadvice find-file-other-window (after eclim-problems-highlight-on-find-file-other-window activate)
  (eclim-problems-highlight))
(defadvice other-window (after eclim-problems-highlight-on-other-window activate)
  (eclim-problems-highlight))
(defadvice switch-to-buffer (after eclim-problems-highlight-switch-to-buffer activate)
  (eclim-problems-highlight))

(defun eclim-problems-highlight ()
  (interactive)
  (save-restriction
    (widen)
    (when (eclim--file-managed-p)
      (eclim--problems-clear-highlights)
      (loop for problem across (remove-if-not (lambda (p) (string= (assoc-default 'filename p) (file-truename (buffer-file-name)))) eclim--problems-list)
            do (eclim--problems-insert-highlight problem)))))

(defun eclim--problems-get-current-problem ()
  (let ((buf (get-buffer "*eclim: problems*")))
    (if (eq buf (current-buffer))
        ;; we are in the problems buffer
        (let ((problems (eclim--problems-filtered))
              (index (1- (line-number-at-pos))))
          (if (>= index (length problems))
              (error "No problem on this line.")
            (aref problems index)))
      ;; we need to figure out which problem corresponds to this pos
      (save-restriction
        (widen)
        (let ((line (line-number-at-pos))
              (col (current-column)))
          (or (find-if (lambda (p) (and (string= (assoc-default 'filename p) (file-truename buffer-file-name))
                                        (= (assoc-default 'line p) line)))
                       eclim--problems-list)
              (error "No problem on this line")))))))

(defun eclim-problems-open-current ()
  (interactive)
  (let* ((p (eclim--problems-get-current-problem)))
    (find-file-other-window (assoc-default 'filename p))
    (eclim--problem-goto-pos p)))

(defun eclim-problems-correct ()
  (interactive)
  (let ((p (eclim--problems-get-current-problem)))
    (if (not (string-match "\.java$" (cdr (assoc 'filename p))))
        (error "Not a Java file. Corrections are currently supported only for Java.")
      (eclim-problems-open-current)
      (eclim-java-correct (cdr (assoc 'line p)) (eclim--byte-offset)))))

(defmacro eclim--with-problems-list (problems &rest body)
  (declare (indent defun))
  "Utility macro to refresh the problem list and do operations on
it asynchronously."
  (let ((res (gensym)))
    `(when eclim--problems-project
       (when (not (minibuffer-window-active-p (minibuffer-window)))
         (message "refreshing... %s " (current-buffer)))
       (eclim/with-results-async ,res ("problems" ("-p" eclim--problems-project) (when (string= "e" eclim--problems-filter) '("-e" "true")))
         (setq eclim--problems-list ,res)
         (let ((,problems ,res))
           ,@body)))))

(defun eclim-problems-buffer-refresh ()
  "Refresh the problem list and draw it on screen."
  (interactive)
  (eclim--with-problems-list problems
    (eclim--problems-buffer-redisplay)
    (if (not (minibuffer-window-active-p (minibuffer-window)))
        (if (string= "e" eclim--problems-filter)
            (message "Eclim reports %d errors." (length problems))
          (message "Eclim reports %d errors, %d warnings."
                   (length (remove-if-not (lambda (p) (not (eq t (assoc-default 'warning p)))) problems))
                   (length (remove-if-not (lambda (p) (eq t (assoc-default 'warning p))) problems)))))))

(defun eclim--problems-cleanup-filename (filename)
  (let ((x (file-name-nondirectory (assoc-default 'filename problem))))
    (if eclim-problems-show-file-extension x (file-name-sans-extension x))))

(defun eclim--problems-filecol-size ()
  (if eclim-problems-resize-file-column
      (min 40
           (apply #'max 0
                  (mapcar (lambda (problem)
                            (length (eclim--problems-cleanup-filename (assoc-default 'filename problem))))
                          (eclim--problems-filtered))))
    40))

(defun eclim--problems-update-filter-description ()
  (if eclim--problems-filefilter
      (if eclim--problems-filter
          (setq eclim--problems-filter-description (concat "(file-" eclim--problems-filter ")"))
        (setq eclim--problems-filter-description "(file)"))
    (if eclim--problems-filter
        (setq eclim--problems-filter-description (concat eclim--problems-project "(" eclim--problems-filter ")"))
      (setq eclim--problems-filter-description eclim--problems-project))))

(defun eclim--problems-buffer-redisplay ()
  "Draw the problem list on screen."
  (let ((buf (get-buffer "*eclim: problems*")))
    (when buf
      (save-excursion
        (set-buffer buf)
        (eclim--problems-update-filter-description)
        (save-excursion
          (dolist (b (mapcar #'window-buffer (window-list)))
            (set-buffer b)
            (eclim-problems-highlight)))
        (let ((inhibit-read-only t)
              (line-number (line-number-at-pos))
              (filecol-size (eclim--problems-filecol-size)))
          (erase-buffer)
          (loop for problem across (eclim--problems-filtered)
                do (eclim--insert-problem problem filecol-size))
          (goto-char (point-min))
          (forward-line (1- line-number)))))))

(defun eclim--problems-filtered (&optional ignore-type-filter)
  "Filter reported problems by eclim.

It filters out problems using the ECLIM--PROBLEMS-FILEFILTER
criteria. If IGNORE-TYPE-FILTER is nil (default), then problems
are also filtered according to ECLIM--PROBLEMS-FILTER, i.e.,
error type. Otherwise, error type is ignored. This is useful when
other mechanisms, like compilation's mode
COMPILATION-SKIP-THRESHOLD, implement this feature."
  (remove-if-not
   (lambda (x) (and
                (or (not eclim--problems-filefilter)
                    (string= (assoc-default 'filename x) eclim--problems-file))
                (or ignore-type-filter
                    (not eclim--problems-filter)
                    (and (string= "e" eclim--problems-filter)
                         (not (eq t (assoc-default 'warning x))))
                    (and (string= "w" eclim--problems-filter)
                         (eq t (assoc-default 'warning x))))))
   eclim--problems-list))

(defun eclim--insert-problem (problem filecol-size)
  (let* ((filecol-format-string (concat "%-" (number-to-string filecol-size) "s"))
         (problem-new-line-pos (position ?\n (assoc-default 'message problem)))
         (problem-message
          (if problem-new-line-pos
              (concat (substring (assoc-default 'message problem)
                                 0 problem-new-line-pos)
                      "...")
            (assoc-default 'message problem)))
         (filename (truncate-string-to-width
                    (eclim--problems-cleanup-filename (assoc-default 'filename problem))
                    40 0 nil t))
         (text (if eclim-problems-show-pos
                   (format (concat filecol-format-string
                                   " | line %-12s"
                                   " | %s")
                           filename
                           (assoc-default 'line problem)
                           problem-message)
                 ;; else
                 (format (concat filecol-format-string
                                 " | %s")
                         filename
                         problem-message))))
    (when (and eclim-problems-hl-errors (eq :json-false (assoc-default 'warning problem)))
      (put-text-property 0 (length text) 'face 'bold text))
    (insert text)
    (insert "\n")))

(defun eclim--get-problems-buffer ()
  "Return the eclim problems buffer, if it exists. Otherwise,
create and initialize a new buffer."
  (or (get-buffer "*eclim: problems*")
      (let ((buf (get-buffer-create "*eclim: problems*")))
        (save-excursion
          ;; (setq eclim--problems-project (eclim--project-name))
          (setq eclim--problems-file buffer-file-name)
          (set-buffer buf)
          (eclim--problems-mode)
                                        ;(eclim-problems-buffer-refresh)
          (goto-char (point-min))))))

(defun eclim--problems-mode-init (&optional quiet)
  "Create and initialize the eclim problems buffer. If the
argument QUIET is non-nil, open the buffer in the background
without switching to it."
  (let ((buf (get-buffer-create "*eclim: problems*")))
    (save-excursion
      (setq eclim--problems-project (eclim--project-name))
      (setq eclim--problems-file buffer-file-name)
      (set-buffer buf)
      (eclim--problems-mode)
      (eclim-problems-buffer-refresh)
      (goto-char (point-min)))
    (if (not quiet)
        (switch-to-buffer buf))))

(defun eclim-problems ()
  "Show current compilation problems in a separate window."
  (interactive)
  (if (eclim--project-name)
      (eclim--problems-mode-init)
    (error "Could not figure out the current project. Is this an eclim managed buffer?")))

(defun eclim-problems-open ()
  "Opens a new (emacs) window inside the current frame showing the current project compilation problems"
  (interactive)
  (let ((w (selected-window)))
    (select-window (split-window nil (round (* (window-height w) 0.75)) nil))
    (eclim-problems)
    (select-window w)))

(add-hook 'find-file-hook
          (lambda () (when (and (eclim--accepted-p (buffer-file-name))
                                (not (get-buffer eclim--problems-buffer-name)))
                       (eclim--problems-mode-init t))))

(defun eclim-problems-refocus ()
  (interactive)
  (when (eclim--project-dir)
    (setq eclim--problems-project (eclim--project-name))
    (setq eclim--problems-file buffer-file-name)
    (with-current-buffer eclim--problems-buffer-name
      (eclim-problems-buffer-refresh))))

(defun eclim-problems-next ()
  (interactive)
  (let ((prob-buf (get-buffer eclim--problems-buffer-name)))
    (when prob-buf
      (set-buffer prob-buf)
      (if (boundp 'eclim--problems-list-at-first)
          (setq eclim--problems-list-at-first nil)
        (forward-line 1))
      (hl-line-move hl-line-overlay)
      (eclim-problems-open-current))))

(defun eclim-problems-previous ()
  (interactive)
  (let ((prob-buf (get-buffer eclim--problems-buffer-name)))
    (when prob-buf
      (set-buffer prob-buf)
      (forward-line -1)
      (hl-line-move hl-line-overlay)
      (eclim-problems-open-current))))

(defun eclim--problems-update-maybe ()
  "If autoupdate is enabled, this function triggers a delayed
refresh of the problems buffer."
  (when (and (not eclim--is-completing)
             (eclim--project-dir)
             eclim-autoupdate-problems)
    (setq eclim--problems-project (eclim--project-name))
    (setq eclim--problems-file buffer-file-name)
    (run-with-idle-timer eclim-problems-refresh-delay nil (lambda () (eclim-problems-buffer-refresh)))))

(defun eclim-problems-compilation-buffer ()
  "Creates a compilation buffer from eclim error messages. This
is convenient as it lets the user navigate between errors using
`next-error' (\\[next-error])."
  (interactive)
  (lexical-let ((filecol-size (eclim--problems-filecol-size))
                (project-directory (concat (eclim--project-dir buffer-file-name) "/"))
                (compil-buffer (get-buffer-create eclim--problems-compilation-buffer-name)))
    (eclim--with-problems-list problems
      (with-current-buffer compil-buffer
        (setq default-directory project-directory)
        (setq buffer-read-only nil)
        (erase-buffer)
        (insert (concat "-*- mode: compilation; default-directory: "
                        project-directory
                        " -*-\n\n"))
        (let ((errors 0) (warnings 0))
          (loop for problem across (eclim--problems-filtered)
                do (eclim--insert-problem-compilation problem filecol-size project-directory)
                (cond ((assoc-default 'warning problem)
                       (setq warnings (1+ warnings)))
                      (t
                       (setq errors (1+ errors)))))
          (insert (format "\nCompilation results: %d errors and %d warnings."
                          errors warnings)))
        (compilation-mode))
      (display-buffer compil-buffer 'other-window))))

(defun eclim--insert-problem-compilation (problem filecol-size project-directory)
  (let ((filename (first (split-string (assoc-default 'filename problem) project-directory t)))
        (description (assoc-default 'message problem))
        (type (if (eq t (assoc-default 'warning problem)) "W" "E")))
    (let ((line (assoc-default 'line problem))
          (col (assoc-default 'column problem)))
      (insert (format "%s:%s:%s: %s: %s\n" filename line col (upcase type) description)))))

(provide 'eclim-problems)
