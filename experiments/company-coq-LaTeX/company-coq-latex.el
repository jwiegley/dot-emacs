(require 'dash)
(require 'color)

(defun company-coq-features/latex--substitute-placeholder (kwd repl)
  "Find KWD and replace it with REPL.
Search is case-insensitive."
  (let ((case-fold-search nil))
    (goto-char (point-min))
    (search-forward kwd)
    (replace-match repl t t)))

(defun company-coq-features/latex--default-color (attr)
  "Get ATTR of default face as LaTeX friendly color."
  (let ((color (face-attribute 'default attr)))
    (unless (string-match-p "#......" color)
      (setq color (apply #'color-rgb-to-hex (color-name-to-rgb color))))
    (upcase (substring color 1))))

(defun company-coq-features/latex--img-plist (ov fname alt)
  "Add attributes to OV to display image FNAME.
Uses ALT as help-echo."
  (overlay-put ov 'company-coq-latex t)
  (overlay-put ov 'help-echo alt)
  (overlay-put ov 'display `(image :type imagemagick
                                   :file ,(expand-file-name fname default-directory)
                                   :ascent center)))

(defconst company-coq-features/latex--template-file-name "coq.template.tex"
  "Name of template file for LaTeX rendering.
This file is recursively searched for, starting from the current
script's folder.")

(defun company-coq-features/latex--find-template ()
  "Explore parent directories to locate a rendering template."
  (-if-let* ((script-name buffer-file-name))
      (let ((dir (directory-file-name script-name)))
        (while (not (file-exists-p (expand-file-name company-coq-features/latex--template-file-name dir)))
          (let ((parent (file-name-directory (directory-file-name dir))))
            (when (string= dir parent)
              (user-error "Not found: %s" company-coq-features/latex--template-file-name))
            (setq dir parent)))
        (expand-file-name company-coq-features/latex--template-file-name dir))
    (user-error "Buffer must be saved before LaTeX rendering can happen")))

(defvar company-coq-features/latex--template-path nil
  "Path to ‘company-coq-features/latex--template-file-name’.
Usually populated by calling ‘company-coq-features/latex--find-template’.")

(defun company-coq-features/latex--make-file-name (fname ext)
  "Construct a file name from FNAME and EXT."
  (format "%s.%s" fname ext))

(defun company-coq-features/latex--cleanup-temporaries (prefix)
  "Cleanup temporary files created by LaTeX while rendering PREFIX.
Does not remove the image."
  (dolist (ext '("dvi" "log" "aux" "tex"))
    (ignore-errors (delete-file (company-coq-features/latex--make-file-name prefix ext)))))

(defun company-coq-features/latex--clear-overlays ()
  "Remove overlays created by cc-LaTeX."
  (company-coq-with-current-buffer-maybe proof-goals-buffer
    (dolist (ov (overlays-in (point-min) (point-max)))
      (when (overlay-get ov 'company-coq-latex)
        (delete-overlay ov)))))

(defvar company-coq-features/latex--disk-cache-size 100
  "Max number of goal pictures to keep in disk cache.")

(defvar company-coq-features/latex--disk-cache nil
  "List of PNGs present on disk, in order of last use.")

(defun company-coq-features/latex--add-to-cache (png)
  "Move PNG to the front of the disk cache."
  (setq company-coq-features/latex--disk-cache
        (cons png (remove png company-coq-features/latex--disk-cache))))

(defun company-coq-features/latex--evict-cache (&optional keep-n)
  "Remove all images but KEEP-N from disk cache.
KEEP-N defaults to ‘company-coq-features/latex--disk-cache-size’."
  (setq keep-n (or keep-n company-coq-features/latex--disk-cache-size))
  (let ((cache-cdr (nthcdr keep-n company-coq-features/latex--disk-cache)))
    (dolist (file cache-cdr)
      (ignore-errors (delete-file file)))
    (setf cache-cdr nil)))

(defun company-coq-features/latex-evict-cache (&optional no-redraw)
  "Empty the TeX image cache.
Causes the current goals buffer to be redrawn, unless NO-REDRAW
is non-nil."
  (interactive)
  (clear-image-cache)
  (company-coq-features/latex--evict-cache 0)
  (company-coq-features/latex--clear-overlays)
  (unless no-redraw (company-coq-features/latex--render-goal)))

(defconst company-coq-features/latex--log-buffer "*LaTeX rendering log*"
  "Name of buffer into which LaTeX rendering output is placed.")

(defun company-coq-features/latex--check-process (prog &rest args)
  "Run PROG with ARGS, inserting output in the current buffer.
Raise an error if PROG exits with a non-zero error code."
  (let ((retv (apply #'call-process prog nil (current-buffer) nil args)))
    (unless (eq 0 retv)
      (error "%s failed.  See ‘%s’ for a full trace"
             prog company-coq-features/latex--log-buffer))))

(defun company-coq-features/latex--prepare-tex-file (str fname width-in)
  "Prepare a LaTeX source file from STR; save it as FNAME.
Uses template file in ‘company-coq-features/latex--template-path’.
WIDTH-IN is the paper width in inches."
  (with-temp-buffer
    (insert-file-contents (buffer-local-value 'company-coq-features/latex--template-path proof-script-buffer))
    (company-coq-features/latex--substitute-placeholder "PAGE-WIDTH" (format "%.2fin" width-in))
    (company-coq-features/latex--substitute-placeholder "BACKGROUND" (company-coq-features/latex--default-color :background))
    (company-coq-features/latex--substitute-placeholder "FOREGROUND" (company-coq-features/latex--default-color :foreground))
    (company-coq-features/latex--substitute-placeholder "CONTENTS" str)
    (write-region (point-min) (point-max) fname nil nil)))

(defun company-coq-features/latex--render-tex-file (tex-fname dvi-fname png-fname dpi)
  "Compile and convert LaTeX source file TEX-FNAME.
Uses DVI-FNAME as an intermediate step, before final conversion
to PNG-FNAME with resolution DPI."
  (with-current-buffer (get-buffer-create company-coq-features/latex--log-buffer)
    (erase-buffer)
    (company-coq-features/latex--check-process "latex" tex-fname)
    (company-coq-features/latex--check-process "dvipng" "-T" "tight" "-D" (number-to-string dpi) "-o" png-fname dvi-fname)))

(defun company-coq-features/latex--prepare-latex (str)
  "Cleanup STR before sending it to LaTeX."
  (pcase-dolist (`(,from . ,to) `(("(" . "\\\\left(")
                                  (")" . "\\\\right)")
                                  (,(concat "[?]\\(" coq-id "\\)\\({[^}]}\\)?") . "\\\\ccEvar{\\1}")))
    (setq str (replace-regexp-in-string from to str t)))
  str)

(defun company-coq-features/latex--compute-width ()
  "Compute a good width to display the current buffer as LaTeX."
  (ceiling (-if-let* ((win (get-buffer-window)))
               (* (window-width win t) 0.85)
             (* 0.5 (or (when (fboundp 'x-display-pixel-width)
                          (x-display-pixel-width))
                        1024)))))

(defconst company-coq-features/latex--dvipng-scale-% 100
  "How many pixels per inch, assuming unadjusted font size?")
(defconst company-coq-features/latex--font-size-adjust 100.0
  "What's the reference font size?")

(defun company-coq-features/latex--compute-dpi (font-size)
  "Compute dpi setting from FONT-SIZE.
137 is such that 1in in the pdf yields 150px after dvipng."
  (ceiling (* company-coq-features/latex--dvipng-scale-%
              (/ font-size company-coq-features/latex--font-size-adjust))))

(defun company-coq-features/latex--compute-width-in (window-width-px font-size)
  "Compute dpi setting from WINDOW-WIDTH-PX and FONT-SIZE.
150px is arbitrary (but connected to 137 in
`company-coq-features/latex--compute-dpi'."
  (* (/ window-width-px 100.0)
     (/ company-coq-features/latex--font-size-adjust font-size)))

(defun company-coq-features/latex--render-string (beg end)
  "Render region BEG .. END as a bit of LaTeX code.
Uses the LaTeX template at ‘company-coq-features/latex--template-path’."
  (let* ((str (buffer-substring-no-properties beg end))
         (width-px (company-coq-features/latex--compute-width))
         (ft-size (ceiling (face-attribute 'default :height)))
         (dpi (company-coq-features/latex--compute-dpi ft-size))
         (width-in (company-coq-features/latex--compute-width-in width-px ft-size))
         (latex (company-coq-features/latex--prepare-latex str))
         (prefix (format "cc-preview-%d-%.2f-%s" dpi width-in (md5 latex)))
         (tex-name (company-coq-features/latex--make-file-name prefix "tex"))
         (dvi-name (company-coq-features/latex--make-file-name prefix "dvi"))
         (png-name (company-coq-features/latex--make-file-name prefix "png"))
         (default-directory temporary-file-directory))
    (company-coq-features/latex--add-to-cache (expand-file-name png-name temporary-file-directory))
    (unless (file-exists-p png-name)
      (unwind-protect
          (progn (company-coq-features/latex--prepare-tex-file latex tex-name width-in)
                 (company-coq-features/latex--render-tex-file tex-name dvi-name png-name dpi))
        (company-coq-features/latex--cleanup-temporaries (expand-file-name prefix temporary-file-directory))))
    (company-coq-features/latex--img-plist (make-overlay beg end nil t nil) png-name str)))

(defun company-coq-features/latex--render-goal ()
  "Parse and LaTeX-render the contents of the goals buffer.
Does not run when output is silenced."
  (unless (or (memq 'no-goals-display proof-shell-delayed-output-flags)
              (null proof-script-buffer)
              (not (display-graphic-p)))
    (unless company-coq-features/latex--template-path
      (with-current-buffer proof-script-buffer
        (setq-local company-coq-features/latex--template-path
                    (company-coq-features/latex--find-template))))
    (condition-case-unless-debug err
        (company-coq-with-current-buffer-maybe proof-goals-buffer
          (company-coq-features/latex--evict-cache)
          (dolist (hyp (company-coq--collect-hypotheses))
            (company-coq-features/latex--render-string
             (company-coq-hypothesis-type-position hyp)
             (+ (company-coq-hypothesis-type-position hyp)
                (length (company-coq-hypothesis-type hyp)))))
          (pcase-dolist (`(,type . ,beg) (company-coq--collect-subgoals))
            (company-coq-features/latex--render-string beg (+ beg (length type)))))
      (error (company-coq-features/latex-evict-cache t)
             (message "Error while rendering goals buffers: %S" (error-message-string err))))))

(define-minor-mode company-coq-LaTeX
  "Render Coq goals using LaTeX."
  :lighter " $"
  (if company-coq-LaTeX
      (progn
        (add-hook 'proof-shell-handle-delayed-output-hook #'company-coq-features/latex--render-goal))
    (company-coq-features/latex-evict-cache t)
    (remove-hook 'proof-shell-handle-delayed-output-hook #'company-coq-features/latex--render-goal)))

(company-coq-LaTeX)
(provide 'company-coq-latex)
