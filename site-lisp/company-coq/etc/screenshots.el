;;; screenshots.el --- Programmable screenshots -*- lexical-binding: t -*-

;;; Commentary:

;;; Code:

(require 'dash)
(require 'noflet)

(defvar my/fringe-width 8)

(defun my/basic-setup ()
  (ido-mode)
  (tool-bar-mode -1)
  (menu-bar-mode -1)
  (scroll-bar-mode -1)
  (column-number-mode)
  (fringe-mode (cons my/fringe-width my/fringe-width))
  (blink-cursor-mode -1)
  (setq-default line-spacing 1
                cursor-type 'bar
                cursor-in-non-selected-windows 'bar
                debug-on-error t
                shr-use-fonts nil
                split-width-threshold 140
                company-idle-delay 0.01
                mode-line-end-spaces (propertize "​" 'display '(space :height (+ height (1))))
                mode-line-format '("%e" mode-line-front-space mode-line-buffer-identification " " ;; Only show company-coq
                                   "(" mode-name (:eval (-filter (lambda (m) (equal (car m) 'company-coq-mode)) minor-mode-alist)) ")"
                                   mode-line-end-spaces))
  (load-theme 'tango t)
  (redisplay t))

(defun my/faces-setup ()
  (setq-default frame-background-mode 'dark) ;; For Coq icon
  (set-face-attribute 'match nil :background "yellow1")
  (set-face-attribute 'default nil :family "Ubuntu Mono" :height 105)
  (set-face-attribute 'mode-line nil :foreground "gray60" :background "black")
  (set-face-attribute 'mode-line-inactive nil :foreground "gray60" :background "#404045")
  (set-face-attribute 'mode-line-buffer-id nil :foreground "#eab700")
  (set-fontset-font t 'unicode "Ubuntu Mono")
  (set-fontset-font t 'unicode "Symbola Monospacified for Ubuntu Mono" nil 'append))

(defun my/x-window-id ()
  (frame-parameter nil 'outer-window-id))

(eval-and-compile
  (defvar my/github-w 880))

(defun my/next-insertion-point (&optional end)
  (when (search-forward "<|>" end t)
    (replace-match ""))
  (redisplay t))

(defun my/insert-with-point (str)
  (let ((start (point)))
    (insert str)
    (let ((end (point)))
      (goto-char start)
      (my/next-insertion-point end))))

(defun my/send-keys (keys)
  (redisplay t) ;; Helps company align its popups
  (ignore-errors
    (execute-kbd-macro (kbd (cond
                             ((equal " " keys) "SPC")
                             ((equal "\n" keys) "RET")
                             (t keys))))))

(defun my/frame-file-name (name ext frame-id)
  (setq ext (or ext "png"))
  (expand-file-name (if frame-id
                        (format "frames/%s-%03d.%s" name frame-id ext)
                      (format "%s.%s" name ext))
                    "img"))

(defun my/save-screenshot (name width-spec gravity include-children &optional ext frame-id)
  (accept-process-output nil 0.02) ;; Wait for company's pop-up
  (force-window-update)
  (redisplay t)
  (let ((png-fname (my/frame-file-name name "png" frame-id)))
    ;; The -screen flag captures children windows too
    (apply #'process-lines `("import" ,@(when include-children "-screen") "-window" ,(my/x-window-id) ,png-fname))
    (apply #'process-lines
           "mogrify" "-strip" "-matte"
           "-bordercolor" (face-attribute 'fringe :background) "-border" (format "0x%d" my/fringe-width)
           (append (when gravity
                     (pcase-let* ((`(,frame-h ,frame-w)
                                   (mapcar #'string-to-number (process-lines "identify" "-ping" "-format" "%h\n%w" png-fname)))
                                  (target-width
                                   (floor (* (car width-spec) my/github-w))))
                       (list "-background" "none" "-gravity" gravity
                             "-extent" (format "%dx%d" target-width (+ frame-h (* 2 my/fringe-width))))))
                   (list png-fname)))
    (unless (member ext '(nil "png"))
      ;; We always produce a PNG original of the file in addition to the requested
      ;; one, so if the extension wasn't PNG we need an extra conversion here
      (process-lines "convert" png-fname (my/frame-file-name name ext frame-id)))
    (when gravity
      (process-lines "optipng" "-strip" "all" "-o3" png-fname))))

(defun my/save-screencast (name frame-duration frame-ids)
  (apply #'process-lines
         "gifsicle" "--careful" "-O2" (format "--delay=%d" frame-duration)
         "--loop" "--output" (my/frame-file-name name "gif" nil)
         (mapcar (apply-partially #'my/frame-file-name name "gif") frame-ids))
  (dolist (fid frame-ids)
    (ignore-errors
      (delete-file (my/frame-file-name name "gif" fid)))))

(defmacro my/with-coq-buffer-and-stable-windows (frame-w-spec frame-h-columns buf-name capture-prefix &rest body)
  (declare (indent defun))
  `(progn
     (dolist (buf (buffer-list))
       (when (and (buffer-live-p buf)
                  (buffer-name buf)
                  (not (eq (aref (buffer-name buf) 0) ?\s)))
         (kill-buffer buf)))
     (delete-other-windows)
     ;; (setq-default frame-resize-pixelwise t)
     (if (< emacs-major-version 25)
         (set-frame-size (selected-frame) (floor (/ (cdr ,frame-w-spec) (frame-char-width))) ,frame-h-columns)
       (set-frame-size nil (floor (cdr ,frame-w-spec)) (floor (* ,(1+ frame-h-columns) (frame-char-height))) t))
     (redisplay t)
     (let ((--buf-- (get-buffer-create (replace-regexp-in-string "\\.?\\'" "." ,buf-name)))
           (--dir-- default-directory))
       (set-buffer --buf--)
       (set-window-buffer nil --buf--)
       (coq-mode)
       (message nil)
       (noflet ((set-window-dedicated-p (&rest args) nil))
         ,@(mapcar (lambda (f) `(progn
                             (proof-shell-wait)
                             (unless (or (eq last-command 'my/keep-window) (minibuffer-window-active-p (selected-window)))
                               (set-buffer-modified-p nil)
                               (set-window-buffer nil --buf--)
                               (set-window-point nil  (point)))
                             ,f
                             (setq default-directory --dir--)))
                   body)))))

(defmacro my/with-screenshot (frame-w-spec frame-h-columns include-children gravity buf-name capture-prefix &rest body)
  (declare (indent defun))
  `(progn
     (my/with-coq-buffer-and-stable-windows ,frame-w-spec ,frame-h-columns ,buf-name ,capture-prefix
       ,@body)
     (my/save-screenshot ,capture-prefix ,frame-w-spec ,gravity ,include-children)
     (ignore-errors (proof-shell-exit t))))

(eval-and-compile
  (defun my/compile-screencast-dsl-1 (prog)
    (pcase prog
      ((pred stringp)
       `((my/send-keys ,prog)))
      (`(:split ,(pred stringp))
       (mapcar (lambda (c)
                 `(my/send-keys ,(char-to-string c))
                 ;; `(progn (setq last-command-event ,c)
                 ;;         (setq this-command 'self-insert-command)
                 ;;         (call-interactively #'self-insert-command))
                 )
               (string-to-list (cadr prog))))
      (`(:minibuf ,(and (pred stringp) prompt) ,(and (pred stringp) value))
       (mapcar (lambda (n)
                 `(message "%s%s" ,(apply #'propertize prompt minibuffer-prompt-properties) ,(substring value 0 n)))
               (cl-loop for i from 0 to (length value) collect i)))
      ((pred listp)
       (list prog))
      (_ (error "Unknown form %S" prog))))

  (defun my/compile-screencast-dsl (prog)
    (-mapcat #'my/compile-screencast-dsl-1 prog)))

(defvar my/screencast-frame-id nil)

(defun my/save-screencast-frame (name width-factor gravity include-children)
  (my/save-screenshot name width-factor gravity include-children "gif" my/screencast-frame-id)
  (cl-incf my/screencast-frame-id))

(defmacro my/with-screencast (frame-w-spec frame-h-columns include-children gravity frame-duration last-frame-repeats buf-name capture-prefix &rest body)
  (declare (indent defun))
  `(progn
     (my/with-coq-buffer-and-stable-windows ,frame-w-spec ,frame-h-columns ,buf-name ,capture-prefix
       (setq my/screencast-frame-id 0)
       ,@(-mapcat (lambda (form) `(,form (my/save-screencast-frame ,capture-prefix ,frame-w-spec ,gravity ,include-children)))
                  (my/compile-screencast-dsl body)))
     (let ((last-frame (1- my/screencast-frame-id)))
       ;; repeat last frame to lengthen final image
       (my/save-screencast ,capture-prefix ,frame-duration (append (number-sequence 0 last-frame)
                                                                   (-repeat ,last-frame-repeats last-frame))))
     (ignore-errors (proof-shell-exit t))))

(defun my/start-pg-no-windows ()
  (save-window-excursion
    (noflet ((proof-layout-windows () nil))
      (proof-activate-scripting)))
  (message nil))

(defun set-window-buffer-with-search (buffer-or-name search)
  "As `set-window-buffer' with BUFFER-OR-NAME.
Sets window start using SEARCH."
  (set-window-buffer nil buffer-or-name)
  (set-window-start  nil (with-current-buffer buffer-or-name
                           (goto-char (point-min))
                           (search-forward search)
                           (point))))

(provide 'screenshots)
;;; screenshots.el ends here
