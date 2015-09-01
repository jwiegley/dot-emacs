;;; prodigy.el --- Manage external services from within Emacs

;; Copyright (C) 2013 Johan Andersson

;; Author: Johan Andersson <johan.rejeep@gmail.com>
;; Maintainer: Johan Andersson <johan.rejeep@gmail.com>
;; Version: 0.0.1
;; URL: http://github.com/rejeep/prodigy.el
;; Package-Requires: ((s "1.8.0") (dash "2.4.0") (ht "1.5") (f "0.14.0"))

;; This file is NOT part of GNU Emacs.

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Code:

(require 's)
(require 'dash)
(require 'ht)
(require 'f)
(require 'ansi-color)

(defgroup wrap-region nil
  "Manage external services from within Emacs."
  :prefix "prodigy-"
  :group 'tools
  :link '(url-link :tag "Github" "https://github.com/rejeep/prodigy.el"))

(defface prodigy-line-face
  '((((class color)) :background "#4A708B"))
  "Color of current line."
  :group 'prodigy)

(defconst prodigy-buffer-name "*prodigy*"
  "Name of Prodigy mode buffer.")

(defcustom prodigy-completion-system 'ido
  "The completion system to be used by Prodigy."
  :group 'prodigy
  :type 'symbol
  :options '(ido default))

(defvar prodigy-mode-hook nil
  "Mode hook for `prodigy-mode'.")

(defvar prodigy-log-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "q") 'prodigy-log-quit)
    map)
  "Keymap for `prodigy-log-mode'.")

(defvar prodigy-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "q") 'prodigy-quit)
    (define-key map (kbd "n") 'prodigy-next)
    (define-key map (kbd "p") 'prodigy-prev)
    (define-key map (kbd "m") 'prodigy-mark)
    (define-key map (kbd "t") 'prodigy-mark-tag)
    (define-key map (kbd "M") 'prodigy-mark-all)
    (define-key map (kbd "u") 'prodigy-unmark)
    (define-key map (kbd "T") 'prodigy-unmark-tag)
    (define-key map (kbd "U") 'prodigy-unmark-all)
    (define-key map (kbd "s") 'prodigy-start)
    (define-key map (kbd "S") 'prodigy-stop)
    (define-key map (kbd "r") 'prodigy-restart)
    (define-key map (kbd "$") 'prodigy-display-process)
    (define-key map (kbd "o") 'prodigy-browse)
    (define-key map (kbd "g") 'prodigy-refresh)
    map)
  "Keymap for `prodigy-mode'.")

(defvar prodigy-services (ht-create)
  "All registered services.

Keys is the name of a service and the value is a hash table per
service.")


;;;; Internal functions

(defun prodigy-sorted-services ()
  "Return list of services sorted by name."
  (-sort
   (lambda (service-1 service-2)
     (string<
      (ht-get service-1 :name)
      (ht-get service-2 :name)))
   (ht-values prodigy-services)))

(defun prodigy-service-at-line (&optional line)
  "Return service at LINE or current line."
  (unless line
    (setq line (line-number-at-pos)))
  (let ((point
         (save-excursion
           (goto-char (point-min))
           (forward-line (1- line))
           (line-beginning-position))))
    (let ((service-name (get-text-property point 'service-name)))
      (ht-get prodigy-services service-name))))

(defun prodigy-service-at-line-p (&optional line)
  "Return true if there is a service at LINE or current line."
  (not (null (prodigy-service-at-line line))))

(defun prodigy-goto-next-line ()
  "Go to next line."
  (prodigy-goto-line (1+ (line-number-at-pos))))

(defun prodigy-goto-prev-line ()
  "Go to previous line."
  (prodigy-goto-line (1- (line-number-at-pos))))

(defun prodigy-goto-line (line)
  "Go to LINE."
  (cond ((prodigy-service-at-line-p line)
         (when (prodigy-service-at-line-p)
           (prodigy-service-set (prodigy-service-at-line) :highlighted nil))
         (goto-char (point-min))
         (forward-line (1- line))
         (prodigy-service-set (prodigy-service-at-line) :highlighted t))
        (t
         (error "No service at line %s" line))))

(defun prodigy-status-name (process)
  "Return PROCESS status name."
  (let ((status (process-status process)))
    (cond ((eq status 'run) "Running")
          ((eq status 'stop) "Stopped")
          ((eq status 'exit) "Exit")
          ((eq status 'signal) "Signal")
          ((eq status 'open) "Open")
          ((eq status 'closed) "Closed")
          ((eq status 'connect) "Connect")
          ((eq status 'failed) "Failed")
          ((eq status 'listen) "Listen")
          (t "Unknown"))))

(defun prodigy-write-service-at-line (service)
  "Remove service at line and insert SERVICE."
  (let ((inhibit-read-only t) (service-name (ht-get service :name)))
    (delete-region (line-beginning-position) (line-end-position))
    (if (ht-get service :marked)
        (insert "* ")
      (insert "  "))
    (insert service-name)
    (move-to-column 30 t)
    (-when-let (process (ht-get service :process))
      (insert " " (prodigy-status-name process)))
    (move-to-column 60 t)
    (-when-let (tags (ht-get service :tags))
      (insert " [" (s-join ", " (-map 'symbol-name tags)) "]"))
    (put-text-property (line-beginning-position) (line-end-position) 'service-name service-name)
    (if (ht-get service :highlighted)
        (put-text-property (line-beginning-position) (line-beginning-position 2) 'face 'prodigy-line-face)
      (put-text-property (line-beginning-position) (line-beginning-position 2) 'face nil))))

(defun prodigy-service-set (service key value)
  "Set SERVICE KEY to VALUE.

This will update the SERVICE object, but also update the line
representing SERVICE."
  (ht-set service key value)
  (save-excursion
    (goto-char (point-min))
    (while (not (eq (prodigy-service-at-line) service))
      (forward-line 1))
    (prodigy-write-service-at-line service)))

(defun prodigy-repaint ()
  "Clear buffer and repaint all services."
  (let ((inhibit-read-only t))
    (erase-buffer)
    (-each
     (prodigy-sorted-services)
     (lambda (service)
       (prodigy-write-service-at-line service)
       (insert "\n")))))

(defun prodigy-reset ()
  "Reset state such as marked and highlighted for all services."
  (ht-each
   (lambda (name service)
     (ht-set service :marked nil)
     (ht-set service :highlighted nil))
   prodigy-services))

(defun prodigy-tags ()
  "Return uniq list of tags."
  (-uniq
   (-flatten
    (-map
     (lambda (service)
       (ht-get service :tags))
     (ht-values prodigy-services)))))

(defun prodigy-service-tagged-with? (service tag)
  "Return true if SERVICE is tagged with TAG."
  (-contains? (ht-get service :tags) tag))

(defun prodigy-services-tagged-with (tag)
  "Return list of services tagged with TAG."
  (let (services)
    (ht-each
     (lambda (name service)
       (if (prodigy-service-tagged-with? service tag)
           (push service services)))
     prodigy-services)
    services))

(defun prodigy-marked-services ()
  "Return list of services that are marked."
  (let (services)
    (ht-each
     (lambda (name service)
       (if (ht-get service :marked)
           (push service services)))
     prodigy-services)
    services))

(defun prodigy-completing-read (prompt collection)
  "Read a string in the minibuffer, with completion.

PROMPT is a string to prompt with.
COLLECTION is the list of strings that the user will be asked to
select between.

The completion system used is determined by
`prodigy-completion-system'."
  (let ((args `(,prompt ,collection nil 'require-match)))
    (cond ((eq prodigy-completion-system 'ido)
           (apply 'ido-completing-read args))
          ((eq prodigy-completion-system 'default)
           (apply 'completing-read args)))))

(defun prodigy-read-tag ()
  "Read tag from list of all possible tags."
  (let ((tag-names (-map 'symbol-name (prodigy-tags))))
    (intern (prodigy-completing-read "tag: " tag-names))))

(defun prodigy-buffer-name (service)
  "Return name of process buffer for SERVICE."
  (concat "*prodigy-" (s-dashed-words (s-downcase (ht-get service :name))) "*"))

(defun prodigy-start-service (service)
  "Start process associated with SERVICE."
  (let ((process (ht-get service :process)))
    (unless (and process (process-live-p process))
      (let* ((name (ht-get service :name))
             (command (ht-get service :command))
             (args (ht-get service :args))
             (default-directory (f-full (ht-get service :cwd)))
             (exec-path (append (ht-get service :path) exec-path)))
        (-when-let (init (ht-get service :init))
          (funcall init))
        (let ((process (apply 'start-process (append (list name nil command) args))))
          (set-process-filter process 'prodigy-process-filter)
          (set-process-query-on-exit-flag process nil)
          (prodigy-service-set service :process process))))))

(defun prodigy-stop-service (service)
  "Stop process associated with SERVICE."
  (-when-let (process (ht-get service :process))
    (when (process-live-p process)
      (kill-process process))
    (prodigy-service-set service :process nil)))

(defun prodigy-apply (fn)
  "Apply FN to service at line or marked services."
  (let ((services (prodigy-marked-services)))
    (if services
        (-each services fn)
      (-when-let (service (prodigy-service-at-line))
        (funcall fn service)))))

(defun prodigy-service-port (service)
  "Find something that look like a port in SERVICE arguments."
  (or
   (ht-get service :port)
   (-when-let (port (-first
                     (lambda (arg)
                       (s-matches? "^\\([0-9]\\)\\{4,5\\}$" arg))
                     (ht-get service :args)))
     (string-to-number port))))

;; TODO: Remove once added to ht.el
(defun ht-find (function table)
  (catch 'break
    (ht-each
     (lambda (key value)
       (when (funcall function key value)
         (throw 'break key)))
     table)))

(defun prodigy-process-filter (process output)
  "Process filter for service processes.

PROCESS is the service process that the OUTPUT is associated to."
  (-when-let (service-name
              (ht-find
               (lambda (name service)
                 (eq (ht-get service :process) process))
               prodigy-services))
    (let* ((service (ht-get prodigy-services service-name))
           (buffer (get-buffer-create (prodigy-buffer-name service))))
      (with-current-buffer buffer
        (insert (ansi-color-apply output))))))


;;;; User functions

(defun prodigy-quit ()
  "Quit prodigy."
  (interactive)
  (quit-window))

(defun prodigy-next ()
  "Go to next service."
  (interactive)
  (condition-case err
      (prodigy-goto-next-line)
    (error
     (message "Cannot move further down"))))

(defun prodigy-prev ()
  "Go to previous service."
  (interactive)
  (condition-case err
      (prodigy-goto-prev-line)
    (error
     (message "Cannot move further up"))))

(defun prodigy-mark ()
  "Mark service at point."
  (interactive)
  (-when-let (service (prodigy-service-at-line))
    (prodigy-service-set service :marked t)
    (ignore-errors
      (prodigy-goto-next-line))))

(defun prodigy-mark-tag ()
  "Mark all services with tag."
  (interactive)
  (let ((tag (prodigy-read-tag)))
    (-each
     (prodigy-services-tagged-with tag)
     (lambda (service)
       (prodigy-service-set service :marked t)))))

(defun prodigy-mark-all ()
  "Mark all services."
  (interactive)
  (ht-each
   (lambda (name service)
     (prodigy-service-set service :marked t))
   prodigy-services))

(defun prodigy-unmark ()
  "Unmark service at point."
  (interactive)
  (-when-let (service (prodigy-service-at-line))
    (prodigy-service-set service :marked nil)
    (ignore-errors
      (prodigy-goto-next-line))))

(defun prodigy-unmark-tag ()
  "Unmark all services with tag."
  (interactive)
  (let ((tag (prodigy-read-tag)))
    (-each
     (prodigy-services-tagged-with tag)
     (lambda (service)
       (prodigy-service-set service :marked nil)))))

(defun prodigy-unmark-all ()
  "Unmark all services."
  (interactive)
  (ht-each
   (lambda (name service)
     (prodigy-service-set service :marked nil))
   prodigy-services))

(defun prodigy-start ()
  "Start service at line or marked services."
  (interactive)
  (prodigy-apply 'prodigy-start-service))

(defun prodigy-stop ()
  "Stop service at line or marked services."
  (interactive)
  (prodigy-apply 'prodigy-stop-service))

(defun prodigy-restart ()
  "Restart service at line or marked services."
  (interactive)
  (prodigy-apply 'prodigy-stop-service)
  (prodigy-apply 'prodigy-start-service))

(defun prodigy-display-process ()
  "Switch to process buffer for service at current line."
  (interactive)
  (-when-let (service (prodigy-service-at-line))
    (when (ht-get service :process)
      (prodigy-log-mode service))))

(defun prodigy-browse ()
  "Browse service url at point if possible to figure out."
  (interactive)
  (-when-let (service (prodigy-service-at-line))
    (-if-let (port (prodigy-service-port service))
        (browse-url (format "http://localhost:%d" port))
      (message "Could not determine port"))))

(defun prodigy-refresh ()
  "Refresh GUI."
  (interactive)
  (let ((line (line-number-at-pos)))
    (prodigy-repaint)
    (prodigy-goto-line line)))

(defun prodigy-log-quit ()
  "Quit window and bury buffer."
  (interactive)
  (quit-window))

(defun prodigy-define-service (&rest args)
  "Define a new service.

If first argument is a string, it is considered a doc
string. ARGS is a plist with support for the following keys:

:name    - Name of service
:command - Command to run
:args    - Arguments passed to command
:cwd     - Run command with this as `default-directory'
:port    - Specify service port for use with open function
:tags    - List of tags
:init    - Function called before process is started
:path    - List of directories added to PATH when command runs"
  (when (eq (type-of (car args)) 'string)
    (pop args))
  (-each
   '(:name :cwd :command)
   (lambda (property)
     (unless (plist-get args property)
       (error "Property %s must be specified." property))))
  (ht-set prodigy-services (plist-get args :name) (ht-from-plist args)))

;;;###autoload
(put 'prodigy-define-service 'lisp-indent-function 'defun)

;;;###autoload
(put 'prodigy-define-service 'doc-string-elt 1)

;;;###autoload
(add-hook 'emacs-lisp-mode-hook
          (lambda ()
            (font-lock-add-keywords
             nil
             '(("(\\(\\<prodigy-define-service\\)\\>"
                (1 font-lock-keyword-face nil t))))))

;;;###autoload
(defun prodigy ()
  "Manage external services from within Emacs."
  (interactive)
  (let ((buffer-p (get-buffer prodigy-buffer-name))
        (buffer (get-buffer-create prodigy-buffer-name)))
    (pop-to-buffer buffer)
    (unless buffer-p
      (kill-all-local-variables)
      (setq buffer-read-only t)
      (setq mode-name "Prodigy")
      (setq major-mode 'prodigy-mode)
      (use-local-map prodigy-mode-map)
      (prodigy-reset)
      (prodigy-repaint)
      (ignore-errors
        (prodigy-goto-line 1))
      (run-mode-hooks 'prodigy-mode-hook))))

;;;###autoload
(defun prodigy-log-mode (service)
  "Open log mode for SERVICE."
  (interactive)
  (pop-to-buffer (prodigy-buffer-name service))
  (kill-all-local-variables)
  (setq mode-name "Prodigy Log")
  (setq major-mode 'prodigy-log-mode)
  (use-local-map prodigy-log-mode-map))

(provide 'prodigy)

;;; prodigy.el ends here
