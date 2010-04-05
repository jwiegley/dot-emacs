;; -*- Mode: Emacs-Lisp -*-
;;
;; elscreen.el
;;
(defconst elscreen-version "1.4.6 (December 30, 2007)")
;;
;; Author:   Naoto Morishima <naoto@morishima.net>
;; Based on: screens.el
;;              by Heikki T. Suopanki <suopanki@stekt1.oulu.fi>
;; Created:  June 22, 1996
;; Revised:  December 30, 2007

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

(provide 'elscreen)
(require 'alist)
(eval-when-compile
  (require 'static))

(static-defconst elscreen-on-xemacs (featurep 'xemacs))
(static-defconst elscreen-on-emacs (and (not elscreen-on-xemacs)
                                        (>= emacs-major-version 21)))


;;; User Customizable Variables:

(defgroup elscreen nil
  "ElScreen -- Screen Manager for Emacsen"
  :tag "ElScreen"
  :group 'environment)

(defcustom elscreen-prefix-key "\C-z"
  "*Prefix key for ElScreen commands."
  :tag "Prefix Key of ElScreen"
  :type '(string :size 10)
  :set (lambda (symbol value)
         (when (boundp 'elscreen-map)
           (elscreen-set-prefix-key value))
         (custom-set-default symbol value))
  :group 'elscreen)

(defcustom elscreen-default-buffer-name "*scratch*"
  "*Name of a buffer in new screen."
  :tag "Name of Default Buffer"
  :type '(string :size 24)
  :group 'elscreen)

(defcustom elscreen-default-buffer-initial-major-mode initial-major-mode
  "*Major mode command symbol to use for the default buffer."
  :tag "Major Mode for Default Buffer"
  :type 'function
  :group 'elscreen)

(defcustom elscreen-default-buffer-initial-message initial-scratch-message
  "*Initial message displayed in default buffer.
If this is nil, no message will be displayed."
  :tag "Message to Display in the Default Buffer"
  :type '(choice (text :tag "Message")
                 (const :tag "none" nil))
  :group 'elscreen)

(defcustom elscreen-mode-to-nickname-alist
  '(("^dired-mode$" .
     (lambda ()
       (format "Dired(%s)" dired-directory)))
    ("^Info-mode$" .
     (lambda ()
       (format "Info(%s)" (file-name-nondirectory Info-current-file))))
    ("^mew-draft-mode$" .
     (lambda ()
       (format "Mew(%s)" (buffer-name (current-buffer)))))
    ("^mew-" . "Mew")
    ("^irchat-" . "IRChat")
    ("^liece-" . "Liece")
    ("^lookup-" . "Lookup"))
  "*Alist composed of the pair of name of major-mode and corresponding screen-name."
  :tag "Alist to Derive Screen Names from Major Modes"
  :type '(alist :key-type string :value-type (choice string function))
  :set (lambda (symbol value)
         (custom-set-default symbol value)
         (when (fboundp 'elscreen-rebuild-mode-to-nickname-alist)
           (elscreen-rebuild-mode-to-nickname-alist)))
  :group 'elscreen)

(defcustom elscreen-buffer-to-nickname-alist
  '(("[Ss]hell" . "shell")
    ("compilation" . "compile")
    ("-telnet" . "telnet")
    ("dict" . "OnlineDict")
    ("*WL:Message*" . "Wanderlust"))
  "*Alist composed of the pair of regular expression of
buffer-name and corresponding screen-name."
  :tag "Alist to Derive Screen Names from Major Modes"
  :type '(alist :key-type string :value-type (choice string function))
  :set (lambda (symbol value)
         (custom-set-default symbol value)
         (when (fboundp 'elscreen-rebuild-buffer-to-nickname-alist)
           (elscreen-rebuild-buffer-to-nickname-alist)))
  :group 'elscreen)

(defcustom elscreen-startup-command-line-processing t
  "*If non-nil, ElScreen processes command line when Emacsen
starts up, and opens files with new screen if needed."
  :type 'boolean
  :tag "Enable/Disable ElScreen to Process Command Line Arguments"
  :group 'elscreen)

(defcustom elscreen-display-screen-number t
  "*Non-nil to display the number of current screen in the mode line."
  :tag "Show/Hide Screen Number on the mode-line"
  :type 'boolean
  :group 'elscreen)

(defcustom elscreen-display-tab t
  "*Specify how the tabs at the top of frame should be displayed.
t means to display tabs whose width should be calculated automatically.
A value of integer means to display tabs with fixed width of this value.
nil means don't display tabs."
  :tag "Specify how the tabs at the top of frame should be displayed"
  :type '(choice (const :tag "Show (automatic width tab)" t)
                 (integer :tag "Show (fixed width tab)" :size 4 :value 16)
                 (const :tag "Hide" nil))
  :set (lambda (symbol value)
         (when (or (booleanp value)
                   (and (numberp value)
                        (> value 0)))
           (custom-set-default symbol value)
           (static-cond
            (elscreen-on-emacs
             (when (fboundp 'elscreen-e21-tab-update)
               (elscreen-e21-tab-update t)))
            (elscreen-on-xemacs
             (when (fboundp 'elscreen-xmas-tab-update)
               (elscreen-xmas-tab-update t))))))
  :group 'elscreen)

(static-when elscreen-on-emacs ;; GNU Emacs 21
  (make-obsolete-variable 'elscreen-tab-display-create-screen
                          'elscreen-tab-display-control)
  (defcustom elscreen-tab-display-control t
    "*Non-nil to display control tab at the most left side."
    :tag "Show/Hide the Control Tab"
    :type 'boolean
    :set (lambda (symbol value)
           (custom-set-default symbol value)
           (when (fboundp 'elscreen-e21-tab-update)
             (elscreen-e21-tab-update t)))
    :group 'elscreen)

  (defcustom elscreen-tab-display-kill-screen 'left
    "*Location of the icons to kill a screen on each tab.  Possible values are 'left, 'right, or nil (to hide them)."
    :tag "Location of Buttons to Kill Screen on Each Tab"
    :type '(choice (const :tag "Left" left)
                   (const :tag "Right" right)
                   (const :tag "None" nil))
    :set (lambda (symbol value)
           (custom-set-default symbol value)
           (when (fboundp 'elscreen-e21-tab-update)
             (elscreen-e21-tab-update t)))
    :group 'elscreen)

  (defface elscreen-tab-background-face
    '((((type x w32 mac) (class color))
       :background "Gray50")
      (((class color))
       (:background "black")))
    "Face to fontify background of tab line."
    :group 'elscreen)

  (defface elscreen-tab-control-face
    '((((type x w32 mac) (class color))
       (:background "white" :foreground "black" :underline "Gray50"))
      (((class color))
       (:background "white" :foreground "black" :underline t))
      (t (:underline t)))
    "Face for control tab."
    :group 'elscreen)

  (defface elscreen-tab-current-screen-face
    '((((class color))
       (:background "white" :foreground "black"))
      (t (:underline t)))
    "Face for current screen tab."
    :group 'elscreen)

  (defface elscreen-tab-other-screen-face
    '((((type x w32 mac) (class color))
       :background "Gray85" :foreground "Gray50")
      (((class color))
       (:background "blue" :foreground "black" :underline t)))
    "Face for tabs other than current screen one."
    :group 'elscreen))


;;; Key & Menu bindings:

(defvar elscreen-map (make-sparse-keymap)
  "Keymap for ElScreen.")
(define-key elscreen-map "\C-c" 'elscreen-create)
(define-key elscreen-map "c"    'elscreen-create)
(define-key elscreen-map "C"    'elscreen-clone)
(define-key elscreen-map "\C-k" 'elscreen-kill)
(define-key elscreen-map "k"    'elscreen-kill)
(define-key elscreen-map "\M-k" 'elscreen-kill-screen-and-buffers)
(define-key elscreen-map "K"    'elscreen-kill-others)
(define-key elscreen-map "\C-p" 'elscreen-previous)
(define-key elscreen-map "p"    'elscreen-previous)
(define-key elscreen-map "\C-n" 'elscreen-next)
(define-key elscreen-map "n"    'elscreen-next)
(define-key elscreen-map "\C-a" 'elscreen-toggle)
(define-key elscreen-map "a"    'elscreen-toggle)
(define-key elscreen-map "'"    'elscreen-goto)
(define-key elscreen-map "\""   'elscreen-select-and-goto)
(define-key elscreen-map "0"    'elscreen-jump-0)
(define-key elscreen-map "1"    'elscreen-jump)
(define-key elscreen-map "2"    'elscreen-jump)
(define-key elscreen-map "3"    'elscreen-jump)
(define-key elscreen-map "4"    'elscreen-jump)
(define-key elscreen-map "5"    'elscreen-jump)
(define-key elscreen-map "6"    'elscreen-jump)
(define-key elscreen-map "7"    'elscreen-jump)
(define-key elscreen-map "8"    'elscreen-jump)
(define-key elscreen-map "9"    'elscreen-jump-9)
(define-key elscreen-map "\C-s" 'elscreen-swap)
(define-key elscreen-map "\C-w" 'elscreen-display-screen-name-list)
(define-key elscreen-map "w"    'elscreen-display-screen-name-list)
(define-key elscreen-map "\C-m" 'elscreen-display-last-message)
(define-key elscreen-map "m"    'elscreen-display-last-message)
(define-key elscreen-map "\C-t" 'elscreen-display-time)
(define-key elscreen-map "t"    'elscreen-display-time)
(define-key elscreen-map "A"    'elscreen-screen-nickname)
(define-key elscreen-map "b"    'elscreen-find-and-goto-by-buffer)
(define-key elscreen-map "\C-f" 'elscreen-find-file)
(define-key elscreen-map "\C-r" 'elscreen-find-file-read-only)
(define-key elscreen-map "d"    'elscreen-dired)
(define-key elscreen-map "\M-x" 'elscreen-execute-extended-command)
(define-key elscreen-map "i"    'elscreen-toggle-display-screen-number)
(define-key elscreen-map "T"    'elscreen-toggle-display-tab)
(define-key elscreen-map "?"    'elscreen-help)
(define-key elscreen-map "v"    'elscreen-display-version)
(define-key elscreen-map "j"    'elscreen-link)
(define-key elscreen-map "s"    'elscreen-split)

(defun elscreen-set-prefix-key (prefix-key)
  (when (not (eq elscreen-prefix-key prefix-key))
    (when elscreen-prefix-key
      (global-set-key elscreen-prefix-key
                      (get 'elscreen-prefix-key
                           'global-map-original-definition))
      (define-key minibuffer-local-map elscreen-prefix-key
        (get 'elscreen-prefix-key 'minibuffer-local-map-original-definition)))
    (put 'elscreen-prefix-key 'global-map-original-definition
         (lookup-key global-map prefix-key))
    (put 'elscreen-prefix-key 'minibuffer-local-map-original-definition
         (lookup-key minibuffer-local-map prefix-key)))
  (global-set-key prefix-key elscreen-map)
  (define-key minibuffer-local-map prefix-key 'undefined)
  (setq elscreen-prefix-key prefix-key))

(defvar elscreen-help "ElScreen keys:
  \\[elscreen-create]    Create a new screen and switch to it
  \\[elscreen-clone]    Create a new screen with the window-configuration of current screen
  \\[elscreen-kill]    Kill current screen
  \\[elscreen-kill-screen-and-buffers]  Kill current screen and buffers
  \\[elscreen-kill-others]    Kill other screens
  \\[elscreen-next]    Switch to the \"next\" screen in a cyclic order
  \\[elscreen-previous]    Switch to the \"previous\" screen in a cyclic order
  \\[elscreen-toggle]    Toggle to the screen selected previously
  \\[elscreen-select-and-goto]    Jump to the specified screen
  \\[elscreen-jump-0]
    :      Jump to the screen #
  \\[elscreen-jump-9]
  \\[elscreen-swap]  Swap current screen with previous one
  \\[elscreen-display-screen-name-list]    Show list of screens
  \\[elscreen-screen-nickname]    Name current screen
  \\[elscreen-display-last-message]    Show last message
  \\[elscreen-display-time]    Show time
  \\[elscreen-find-and-goto-by-buffer]    Switch to the screen in which specified buffer is displayed
  \\[elscreen-find-file]  Create new screen and open file
  \\[elscreen-find-file-read-only]  Create new screen and open file but don't allow changes
  \\[elscreen-dired]    Create new screen and run dired
  \\[elscreen-execute-extended-command]  Read function name, then call it with new screen
  \\[elscreen-toggle-display-screen-number]    Show/hide the screen number in the mode line
  \\[elscreen-toggle-display-tab]    Show/hide the tab at the top of screen
  \\[elscreen-display-version]    Show ElScreen version
  \\[elscreen-help]    Show this help"
  "Help shown by elscreen-help-mode")


;;; Internal Functions:

(defvar elscreen-frame-confs nil
  "Alist that contains the information about screen configurations.")

(defun elscreen-current-window-configuration ()
  (list (current-window-configuration) (point-marker)))

(defun elscreen-default-window-configuration ()
  (let ((default-buffer (get-buffer elscreen-default-buffer-name)))
    (save-window-excursion
      (set-window-dedicated-p (selected-window) nil)
      (delete-other-windows)
      (if default-buffer
          (switch-to-buffer default-buffer)
        (switch-to-buffer (get-buffer-create elscreen-default-buffer-name))
        (funcall elscreen-default-buffer-initial-major-mode)
        (insert elscreen-default-buffer-initial-message)
        (set-buffer-modified-p nil))
      (elscreen-current-window-configuration))))

(defun elscreen-apply-window-configuration (elscreen-window-configuration)
  (let ((window-configuration (car elscreen-window-configuration))
        (marker (cadr elscreen-window-configuration)))
    (set-window-configuration window-configuration)
    (when (marker-buffer marker)
      (goto-char marker))))

(defun get-alist (key alist)
  (cdr (assoc key alist)))

(defsubst elscreen-copy-tree (tree)
  (if (fboundp 'copy-tree)
      (copy-tree tree)
    (elscreen-copy-tree-1 tree)))

(defun elscreen-copy-tree-1 (tree)
  (let (clone)
    (while (consp tree)
      (setq clone (cons (or (and (consp (car tree))
                                 (elscreen-copy-tree-1 (car tree)))
                            (car tree))
                        clone))
      (setq tree (cdr tree)))
    (nconc (nreverse clone) tree)))

(defmacro elscreen-save-screen-excursion (&rest body)
  "Execute BODY, preserving ElScreen meta data.
Return the value of the last form in BODY."
  `(let ((original-buffer-list (buffer-list))
         (original-buffer-live-p nil)
         (original-elscreen-window-configuration
          (elscreen-current-window-configuration))
         (original-frame-confs (elscreen-copy-tree elscreen-frame-confs)))
     (unwind-protect
         (save-window-excursion ,@body)
       (setq elscreen-frame-confs original-frame-confs)
       (elscreen-apply-window-configuration
        original-elscreen-window-configuration)
       (mapcar
        (lambda (buffer)
          (when (buffer-live-p buffer)
            (bury-buffer buffer)
            (setq original-buffer-live-p t)))
        original-buffer-list)
       (when original-buffer-live-p
         (while (not (memq (car (buffer-list)) original-buffer-list))
           (bury-buffer (car (buffer-list))))))))

(defsubst elscreen-get-frame-confs (frame)
  (get-alist frame elscreen-frame-confs))

(defun elscreen-make-frame-confs (frame &optional keep-window-configuration)
  (when (null (elscreen-get-frame-confs frame))
    (let ((selected-frame (selected-frame))
          elscreen-window-configuration)
      (save-current-buffer
        (select-frame frame)
        (setq elscreen-window-configuration
              (if keep-window-configuration
                  (elscreen-current-window-configuration)
                (elscreen-default-window-configuration)))
        (set-alist 'elscreen-frame-confs frame
                   (list
                    (cons 'screen-property
                          (list
                           (cons 0 (list
                                    (cons 'window-configuration
                                          elscreen-window-configuration)))))
                    (cons 'screen-history (list 0))
                    (cons 'modified-inquirer nil)
                    (cons 'screen-to-name-alist-cache nil)))
        (elscreen-apply-window-configuration elscreen-window-configuration)
        (elscreen-notify-screen-modification 'force-immediately)
        (select-frame selected-frame)))))

(defun elscreen-delete-frame-confs (frame)
  (remove-alist 'elscreen-frame-confs frame))

(static-cond
 ((boundp 'after-make-frame-functions) ;; GNU Emacs 21
  (add-hook 'after-make-frame-functions 'elscreen-make-frame-confs))
 (t ;; XEmacs
  (add-hook 'create-frame-hook 'elscreen-make-frame-confs)))
(static-cond
 ((boundp 'delete-frame-functions) ;; GNU Emacs 22?
  (add-hook 'delete-frame-functions 'elscreen-delete-frame-confs))
 (t ;; XEmacs
  (add-hook 'delete-frame-hook 'elscreen-delete-frame-confs)))

(defsubst elscreen-get-conf-list (type)
  (get-alist type (elscreen-get-frame-confs (selected-frame))))

(defsubst elscreen-set-conf-list (type conf-list)
  (let ((frame-conf (elscreen-get-frame-confs (selected-frame))))
    (set-alist 'frame-conf type conf-list)))

(defun elscreen-get-screen-property (screen)
  (let ((screen-property-list (elscreen-get-conf-list 'screen-property)))
    (get-alist screen screen-property-list)))

(defun elscreen-set-screen-property (screen property)
  (let ((screen-property-list (elscreen-get-conf-list 'screen-property)))
    (set-alist 'screen-property-list screen property)
    (elscreen-set-conf-list 'screen-property screen-property-list)))

(defun elscreen-delete-screen-property (screen)
  (let ((screen-property-list (elscreen-get-conf-list 'screen-property)))
    (remove-alist 'screen-property-list screen)
    (elscreen-set-conf-list 'screen-property screen-property-list)))

(defun elscreen-get-number-of-screens ()
  "Return total number of screens."
  (length (elscreen-get-conf-list 'screen-property)))

(defun elscreen-one-screen-p ()
  "Return t if there is only one screen."
  (= (elscreen-get-number-of-screens) 1))

(defun elscreen-get-screen-list ()
  "Return a list of screen numbers."
  (mapcar 'car (elscreen-get-conf-list 'screen-property)))

(defun elscreen-screen-live-p (screen)
  "Return t when SCREEN is alive."
  (not (null (elscreen-get-screen-property screen))))

(defun elscreen-get-window-configuration (screen)
  "Return pair of window-configuration and marker of SCREEN
from `elscreen-frame-confs', a cons cell."
  (let ((screen-property (elscreen-get-screen-property screen)))
    (get-alist 'window-configuration screen-property)))

(defun elscreen-set-window-configuration (screen winconf)
  "Set pair of window-configuration and marker of SCREEN to WINCONF."
  (let ((screen-property (elscreen-get-screen-property screen)))
    (set-alist 'screen-property 'window-configuration winconf)
    (elscreen-set-screen-property screen screen-property)))

(defun elscreen-get-screen-nickname (screen)
  "Return nickname of SCREEN from `elscreen-frame-confs', a string."
  (let ((screen-property (elscreen-get-screen-property screen)))
    (get-alist 'nickname screen-property)))

(defun elscreen-set-screen-nickname (screen nickname)
  "Set nickname of SCREEN to NICKNAME."
  (let ((screen-property (elscreen-get-screen-property screen)))
    (set-alist 'screen-property 'nickname nickname)
    (elscreen-set-screen-property screen screen-property)))

(defun elscreen-delete-screen-nickname (screen)
  "Remove nickname of SCREEN from `elscreen-frame-confs'."
  (let ((screen-property (elscreen-get-screen-property screen)))
    (remove-alist 'screen-property 'nickname)
    (elscreen-set-screen-property screen screen-property)))

(defun elscreen-append-screen-to-history (screen)
  (let ((screen-history (elscreen-get-conf-list 'screen-history)))
    (setcdr (last screen-history) (list screen))))

(defun elscreen-delete-screen-from-history (screen)
  (let ((screen-history (elscreen-get-conf-list 'screen-history)))
    (setq screen-history (delq screen screen-history))
    (elscreen-set-conf-list 'screen-history screen-history)))

(defun elscreen-set-current-screen (screen)
  (let ((screen-history (elscreen-get-conf-list 'screen-history)))
    (setq screen-history (cons screen (delq screen screen-history)))
    (elscreen-set-conf-list 'screen-history screen-history)))

(defun elscreen-get-current-screen ()
  (car (elscreen-get-conf-list 'screen-history)))

(defun elscreen-get-previous-screen ()
  (cadr (elscreen-get-conf-list 'screen-history)))

(defun elscreen-status-label (screen &optional default)
  (let ((default (or default " "))
        (current-screen (elscreen-get-current-screen))
        (previous-screen (elscreen-get-previous-screen)))
    (cond
     ((eq screen current-screen) "+")
     ((eq screen previous-screen) "-")
     (t default))))

(defvar elscreen-notify-screen-modification-suppress-flag nil)
(defmacro elscreen-notify-screen-modification-suppress (&rest body)
  `(let ((elscreen-notify-screen-modification-suppress-flag t))
     ,@body))

(defvar elscreen-screen-update-hook nil)
(defun elscreen-run-screen-update-hook ()
  (when elscreen-frame-confs
    (elscreen-notify-screen-modification-suppress
     (run-hooks 'elscreen-screen-update-hook)))
  (remove-hook 'post-command-hook 'elscreen-run-screen-update-hook))

(defun elscreen-screen-modified-p (inquirer)
  (let* ((inquirer-list (elscreen-get-conf-list 'modified-inquirer))
         (modified (null (memq inquirer inquirer-list))))
    (add-to-list 'inquirer-list inquirer)
    (elscreen-set-conf-list 'modified-inquirer inquirer-list)
    modified))

(defun elscreen-set-screen-modified ()
  (elscreen-set-conf-list 'modified-inquirer nil)
  (add-hook 'post-command-hook 'elscreen-run-screen-update-hook))

(cond
 ((fboundp 'compare-window-configurations)) ;; GNU Emacs
 ((fboundp 'window-configuration-equal) ;; XEmacs 21.5
  (defalias 'compare-window-configurations 'window-configuration-equal)))
(defvar elscreen-screen-modified-hook-pwc nil)
(defun elscreen-notify-screen-modification (&optional mode)
  (when (and (not (window-minibuffer-p))
             (not elscreen-notify-screen-modification-suppress-flag)
             (or (eq mode 'force)
                 (eq mode 'force-immediately)
                 (null elscreen-screen-modified-hook-pwc)
                 (not (fboundp 'compare-window-configurations))
                 (not (compare-window-configurations
                       (current-window-configuration)
                       elscreen-screen-modified-hook-pwc))))
    (setq elscreen-screen-modified-hook-pwc
          (current-window-configuration))
    (elscreen-set-screen-modified)
    (when (eq mode 'force-immediately)
      (elscreen-run-screen-update-hook))))

(defmacro elscreen-screen-modified-hook-setup (&rest hooks-and-functions)
  (cons
   'progn
   (mapcar
    (lambda (hook-or-function)
      (let ((mode ''normal))
        (when (listp hook-or-function)
          (setq mode (nth 1 hook-or-function))
          (setq hook-or-function (nth 0 hook-or-function)))
        (cond
         ((string-match "-\\(hooks?\\|functions\\)$"
                        (symbol-name hook-or-function))
          `(add-hook (quote ,hook-or-function)
                     (lambda (&rest ignore)
                       (elscreen-notify-screen-modification ,mode))))
         (t ;; Assume hook-or-function is function
          `(defadvice ,hook-or-function (around
                                         elscreen-screen-modified-advice
                                         activate)
             ad-do-it
             (elscreen-notify-screen-modification ,mode))))))
    hooks-and-functions)))

(elscreen-screen-modified-hook-setup
 (recenter 'force) (change-major-mode-hook 'force)
 other-window
 window-configuration-change-hook window-size-change-functions
 (handle-switch-frame 'force) ;; GNU Emacs 21
 (select-frame-hook 'force) ;; XEmacs
 (delete-frame 'force)
 (Info-find-node-2 'force))

(defun elscreen-get-screen-to-name-alist-cache ()
  (elscreen-get-conf-list 'screen-to-name-alist-cache))

(defun elscreen-set-screen-to-name-alist-cache (alist)
  (elscreen-set-conf-list 'screen-to-name-alist-cache alist))

(defvar elscreen-mode-to-nickname-alist-symbol-list nil)
(defvar elscreen-mode-to-nickname-alist-internal nil)
(defun elscreen-rebuild-mode-to-nickname-alist ()
  (setq elscreen-mode-to-nickname-alist-internal
        (apply 'append
               (mapcar 'symbol-value
                       elscreen-mode-to-nickname-alist-symbol-list)))
  (elscreen-notify-screen-modification 'force-immediately))
(defun elscreen-set-mode-to-nickname-alist (mode-to-nickname-alist-symbol)
  (add-to-list 'elscreen-mode-to-nickname-alist-symbol-list
               mode-to-nickname-alist-symbol)
  (elscreen-rebuild-mode-to-nickname-alist))
(elscreen-set-mode-to-nickname-alist 'elscreen-mode-to-nickname-alist)

(defvar elscreen-buffer-to-nickname-alist-symbol-list nil)
(defvar elscreen-buffer-to-nickname-alist-internal nil)
(defun elscreen-rebuild-buffer-to-nickname-alist ()
  (setq elscreen-buffer-to-nickname-alist-internal
        (apply 'append
               (mapcar 'symbol-value
                       elscreen-buffer-to-nickname-alist-symbol-list)))
  (elscreen-notify-screen-modification 'force-immediately))
(defun elscreen-set-buffer-to-nickname-alist (buffer-to-nickname-alist-symbol)
  (add-to-list 'elscreen-buffer-to-nickname-alist-symbol-list
               buffer-to-nickname-alist-symbol)
  (elscreen-rebuild-buffer-to-nickname-alist))
(elscreen-set-buffer-to-nickname-alist 'elscreen-buffer-to-nickname-alist)

(defsubst elscreen-get-alist-to-nickname (alist op mode-or-buffer-name)
  (catch 'found
    (progn
      (mapcar
       (lambda (map)
         (let ((nickname nil)
               (condition-data (car map))
               (string-or-function (cdr map)))
           (when (funcall op condition-data mode-or-buffer-name)
             (cond
              ((functionp string-or-function)
               (setq nickname
                     (condition-case nil
                         (funcall string-or-function)
                       (wrong-number-of-arguments
                        (funcall string-or-function (current-buffer))))))
              (t
               (setq nickname string-or-function)))
             (throw 'found (cons 'nickname nickname)))))
       alist)
      nil)))

(defun elscreen-get-screen-to-name-alist (&optional truncate-length padding)
  (when (elscreen-screen-modified-p 'elscreen-get-screen-to-name-alist)
    (elscreen-notify-screen-modification-suppress
     (elscreen-set-window-configuration (elscreen-get-current-screen)
                                        (elscreen-current-window-configuration))
     (let* ((screen-list (sort (elscreen-get-screen-list) '<))
            screen-name screen-to-name-alist nickname-type-map)
       (elscreen-save-screen-excursion
        (mapcar
         (lambda (screen)
           ;; If nickname exists, use it.
           (setq screen-name (elscreen-get-screen-nickname screen))
           ;; Nickname does not exist, so examine major-mode and buffer-name.
           (when (null screen-name)
             (elscreen-goto-internal screen)

             (setq nickname-type-map
                   (mapcar
                    (lambda (window)
                      (with-current-buffer (window-buffer window)
                        (or (elscreen-get-alist-to-nickname
                             elscreen-mode-to-nickname-alist-internal
                             'string-match (symbol-name major-mode))
                            (elscreen-get-alist-to-nickname
                             elscreen-buffer-to-nickname-alist-internal
                             'string-match (buffer-name))
                            (cons 'buffer-name (buffer-name)))))
                    (window-list)))

             (let (nickname-list)
               (while (> (length nickname-type-map) 0)
                 (let ((type (caar nickname-type-map))
                       (name (cdar nickname-type-map)))
                   (when name
                     (setq nickname-list (cons name nickname-list)))
                   (setq nickname-type-map
                         (if (eq type 'nickname)
                             (delete (car nickname-type-map) nickname-type-map)
                           (cdr nickname-type-map)))))
               (setq screen-name
                     (mapconcat 'identity (reverse nickname-list) ":"))))

           (set-alist 'screen-to-name-alist screen screen-name))
         screen-list))

       (elscreen-set-screen-to-name-alist-cache screen-to-name-alist))))

  ;; Arguments of truncate-length and padding are deprecated.
  (if truncate-length
      (let ((screen-to-name-alist
             (copy-alist (elscreen-get-screen-to-name-alist-cache))))
        (elscreen-message "Arguments for `elscreen-get-screen-to-name-alist' are deprecated.  Use elscreen-truncate-screen-name for each screen-name.")
        (mapc
         (lambda (screen-to-name)
           (setcdr screen-to-name
                   (elscreen-truncate-screen-name (cdr screen-to-name)
                                                  truncate-length padding)))
         screen-to-name-alist)
        screen-to-name-alist)
    (elscreen-get-screen-to-name-alist-cache)))

(defun elscreen-truncate-screen-name (screen-name truncate-length &optional padding)
  (let ((truncate-length (max truncate-length 4)))
    (cond
     ((> (string-width screen-name) truncate-length)
      (concat (truncate-string-to-width screen-name (- truncate-length 3)
                                        nil ?.)
              "..."))
     (padding
      (truncate-string-to-width screen-name truncate-length nil ?\ ))
     (t
      screen-name))))

(defun elscreen-goto-internal (screen)
  "Set the configuration of windows, buffers and markers previousuly
stored as SCREEN."
  (let ((elscreen-window-configuration
         (elscreen-get-window-configuration screen)))
    (elscreen-apply-window-configuration elscreen-window-configuration)))

(defvar elscreen-create-hook nil)
(defun elscreen-create-internal (&optional noerror)
  "Create a new screen.
If NOERROR is not nil, no message is displayed in mini buffer
when error is occurred."
  (cond
   ((>= (elscreen-get-number-of-screens) 10)
    (unless noerror
      (elscreen-message "No more screens."))
    nil)
   (t
    (let ((screen-list (sort (elscreen-get-screen-list) '<))
          (screen 0))
      (elscreen-set-window-configuration
       (elscreen-get-current-screen)
       (elscreen-current-window-configuration))
      (while (eq (nth screen screen-list) screen)
        (setq screen (+ screen 1)))
      (elscreen-set-window-configuration
       screen (elscreen-default-window-configuration))
      (elscreen-append-screen-to-history screen)
      (elscreen-notify-screen-modification 'force)
      (run-hooks 'elscreen-create-hook)
      screen))))

(defun elscreen-kill-internal (screen)
  (elscreen-delete-screen-property screen)
  (elscreen-delete-screen-from-history screen)
  screen)

(defun elscreen-find-screens (condition)
  (let ((screen-list (sort (elscreen-get-screen-list) '<))
        result)
    (save-current-buffer
      (elscreen-set-window-configuration
       (elscreen-get-current-screen)
       (elscreen-current-window-configuration))
      (elscreen-notify-screen-modification-suppress
       (elscreen-save-screen-excursion
        (mapc
         (lambda (screen)
           (when (funcall condition screen)
             (setq result (cons screen result))))
         screen-list))
       result))))

(defun elscreen-find-screen (condition)
  (catch 'elscreen-find-screen
    (elscreen-find-screens `(lambda (screen)
                              (when (funcall ,condition screen)
                                (throw 'elscreen-find-screen screen))))))

(defun elscreen-find-screen-by-buffer (buffer &optional create)
  (let* ((buffer (if (bufferp buffer) buffer (get-buffer buffer)))
         (screen (when buffer
                   (elscreen-find-screen
                    `(lambda (screen)
                       (elscreen-goto-internal screen)
                       (not (null (get-buffer-window ,buffer))))))))
    (when (and buffer (null screen) create)
      (cond
       ((setq screen (elscreen-create-internal 'noerror))
        (save-window-excursion
          (elscreen-goto-internal screen)
          (switch-to-buffer buffer t)
          (elscreen-set-window-configuration
           screen (elscreen-current-window-configuration))))
       (t
        (setq screen (elscreen-get-current-screen))
        (elscreen-goto-internal screen)
        (save-selected-window
          (select-window (split-window))
          (switch-to-buffer buffer t)))))
    screen))

(defun elscreen-find-screen-by-major-mode (major-mode-or-re)
  (let ((major-mode-re (cond
                        ((stringp major-mode-or-re)
                         major-mode-or-re)
                        ((symbolp major-mode-or-re)
                         (format "^%s$" (regexp-quote
                                         (symbol-name major-mode-or-re))))
                        (t nil))))
    (when major-mode-re
      (elscreen-find-screen
       (lambda (screen)
         (elscreen-goto-internal screen)
         (save-selected-window
           (catch 'found
             (mapcar
              (lambda (window)
                (select-window window)
                (when (string-match major-mode-re (symbol-name major-mode))
                  (throw 'found t)))
              (window-list))
             nil)))))))

(defvar elscreen-last-message "Welcome to ElScreen!"
  "Last shown message.")
(defun elscreen-message (message &optional sec)
  "Display MESSAGE in mini-buffer for SEC seconds.
Default value for SEC is 3."
  (when message
    (setq elscreen-last-message message)
    (message "%s" message)
    (sit-for (or sec 3)))
  (message nil))


;;; User Interfaces:

(defun elscreen-create ()
  "Create a new screen and switch to it."
  (interactive)
  (let ((screen (elscreen-create-internal)))
    (if screen
        (elscreen-goto screen))))

(defun elscreen-clone (&optional screen)
  "Create a new screen with the window-configuration of SCREEN.
If SCREEN is ommitted, current-screen is used."
  (interactive)
  (let ((screen (or screen (elscreen-get-current-screen)))
        clone elscreen-window-configuration)
    (cond
     ((not (elscreen-screen-live-p screen))
      (elscreen-message "There is no such screen, cannot clone"))
    ((setq clone (elscreen-create-internal))
     (save-window-excursion
       (elscreen-goto-internal screen)
       (setq elscreen-window-configuration
             (elscreen-current-window-configuration)))
     (elscreen-set-window-configuration clone elscreen-window-configuration)
     (elscreen-goto clone)))))

(defvar elscreen-kill-hook nil)
(defun elscreen-kill (&optional screen)
  "Kill SCREEN.  If optional argument SCREEN is
ommitted, current-screen is killed."
  (interactive "P")
  (let ((screen (or (and (numberp screen) screen)
                    (elscreen-get-current-screen))))
    (cond
     ((not (elscreen-screen-live-p screen))
      (elscreen-message "There is no such screen, cannot kill")
      nil)
     ((elscreen-one-screen-p)
      (elscreen-message "There is only one screen, cannot kill")
      nil)
     (t
      (elscreen-kill-internal screen)
      (elscreen-goto-internal (elscreen-get-current-screen))
      (elscreen-notify-screen-modification 'force)
      (run-hooks 'elscreen-kill-hook)
      screen))))

(defun elscreen-kill-screen-and-buffers (&optional screen)
  "Kill buffers on SCREEN and SCREEN itself.  If optional
argument SCREEN is omitted, current screen is killed."
  (interactive)
  (let* ((screen (or screen (elscreen-get-current-screen)))
         (elscreen-window-configuration
          (elscreen-get-window-configuration screen)))
    (when (elscreen-kill screen)
      (save-window-excursion
        (elscreen-apply-window-configuration elscreen-window-configuration)
        (mapc
         (lambda (buffer)
           (when (buffer-live-p buffer)
             (kill-buffer buffer)))
         (mapcar 'window-buffer (window-list))))
      screen)))

(defun elscreen-kill-others (&optional screen)
  "Kill screens other than SCREEN.  If optional argument SCREEN
is ommitted, current screen will survive."
  (interactive)
  (let* ((screen (or screen (elscreen-get-current-screen)))
         (screen-list (when (elscreen-screen-live-p screen)
                        (delq screen (sort (elscreen-get-screen-list) '<))))
         screen-list-string)
    (cond
     ((not (elscreen-screen-live-p screen)) ;; XXX
      (when (interactive-p)
        (elscreen-message "There is no such screen")))
     ((null screen-list)
      (when (interactive-p)
        (elscreen-message "There is only one screen, cannot kill")))
     ((or
       (not (interactive-p))
       (yes-or-no-p (format "Really kill screens other than %d? " screen)))
      (setq screen-list-string (mapconcat
                                (lambda (screen)
                                  (elscreen-kill-internal screen)
                                  (number-to-string screen))
                                screen-list ","))
      (elscreen-goto-internal screen)
      (elscreen-notify-screen-modification 'force-immediately)
      (when (interactive-p)
        (elscreen-message (format "screen %s killed" screen-list-string)))))
    screen-list))

(defvar elscreen-goto-hook nil)
(defun elscreen-goto (screen)
  "Switch to screen SCREEN."
  (interactive "NGoto screen number: ")
  (cond
   ((eq (elscreen-get-current-screen) screen))
   ((elscreen-screen-live-p screen)
    (elscreen-set-window-configuration
     (elscreen-get-current-screen)
     (elscreen-current-window-configuration))
    (elscreen-set-current-screen screen)
    (elscreen-goto-internal screen)
    (static-when (and elscreen-on-emacs (= emacs-major-version 21))
      (when window-system
        (redraw-frame (selected-frame))))
    (elscreen-notify-screen-modification 'force)
    (run-hooks 'elscreen-goto-hook)
    screen)
   (t
    (elscreen-message (format "No screen %d" screen))
    nil)))

(defun elscreen-next ()
  "Switch to the next screen."
  (interactive)
  (cond
   ((elscreen-one-screen-p)
    (elscreen-message
     (format "You cannot escape from screen %d!"
             (elscreen-get-current-screen))))
   (t
    (let* ((screen-list (sort (elscreen-get-screen-list) '<))
           (next-screen
            (or (nth 1 (memq (elscreen-get-current-screen) screen-list))
                (car screen-list))))
      (elscreen-goto next-screen)))))

(defun elscreen-previous ()
  "Switch to the previous screen."
  (interactive)
  (cond
   ((elscreen-one-screen-p)
    (elscreen-message
     (format "You cannot escape from screen %d!"
             (elscreen-get-current-screen))))
   (t
    (let* ((screen-list (sort (elscreen-get-screen-list) '>))
           (previous-screen
            (or (nth 1 (memq (elscreen-get-current-screen) screen-list))
                (car screen-list))))
      (elscreen-goto previous-screen)))))

(defun elscreen-toggle ()
  "Toggle to the screen selected previously."
  (interactive)
  (cond
   ((elscreen-one-screen-p)
    (elscreen-message
     (format "You cannot escape from screen %d!"
             (elscreen-get-current-screen))))
   (t
    (elscreen-goto (elscreen-get-previous-screen)))))

(defun elscreen-jump ()
  "Switch to specified screen."
  (interactive)
  (let ((next-screen (string-to-number (string last-command-char))))
    (if (and (<= 0 next-screen) (<= next-screen 9))
        (elscreen-goto next-screen))))
(defalias 'elscreen-jump-0 'elscreen-jump)
(defalias 'elscreen-jump-9 'elscreen-jump)

(defun elscreen-swap ()
  "Interchange screens selected currently and previously."
  (interactive)
  (cond
   ((elscreen-one-screen-p)
    (elscreen-message "There is only one screen, cannot swap"))
   (t
    (let* ((current-screen (elscreen-get-current-screen))
           (previous-screen (elscreen-get-previous-screen))
           (current-screen-property
            (elscreen-get-screen-property current-screen))
           (previous-screen-property
            (elscreen-get-screen-property previous-screen)))
      (elscreen-set-screen-property current-screen previous-screen-property)
      (elscreen-set-screen-property previous-screen current-screen-property)
      (elscreen-goto-internal (elscreen-get-current-screen))))))

(defun elscreen-screen-nickname (nickname)
  "Set nickname for current screen to NICKNAME."
  (interactive "sSet window title to: ")
  (cond
   ((zerop (length nickname))
    (elscreen-delete-screen-nickname (elscreen-get-current-screen)))
   (t
    (elscreen-set-screen-nickname (elscreen-get-current-screen) nickname)))
  (elscreen-notify-screen-modification 'force))

(defun elscreen-display-screen-name-list ()
  "Display the list of screens in mini-buffer."
  (interactive)
  (let ((screen-list (sort (elscreen-get-screen-list) '<))
        (screen-to-name-alist (elscreen-get-screen-to-name-alist)))
    (elscreen-message
     (mapconcat
      (lambda (screen)
        (let ((screen-name (get-alist screen screen-to-name-alist)))
          (format "%d%s %s" screen
                  (elscreen-status-label screen "")
                  screen-name)))
      screen-list "  "))))


;;; Help

(defvar elscreen-help-symbol-list nil)
(defun elscreen-set-help (help-symbol)
  (add-to-list 'elscreen-help-symbol-list help-symbol t))
(elscreen-set-help 'elscreen-help)

(defun elscreen-help ()
  "Show key bindings of ElScreen and Add-On softwares."
  (interactive)
  (with-output-to-temp-buffer "*ElScreen Help*"
    (princ (substitute-command-keys
            (mapconcat 'symbol-value
                       elscreen-help-symbol-list "\n\n")))
    (print-help-return-message)))


;;; Utility Functions

(defun elscreen-display-version ()
  "Display ElScreen version."
  (interactive)
  (elscreen-message (concat "ElScreen version " elscreen-version)))

(defun elscreen-toggle-display-screen-number ()
  "Toggle the screen number in the mode line."
  (interactive)
  (setq elscreen-display-screen-number (null elscreen-display-screen-number))
  (elscreen-notify-screen-modification 'force))

(defun elscreen-toggle-display-tab ()
  "Toggle the tab on the top of screen."
  (interactive)
  (setq elscreen-display-tab (null elscreen-display-tab))
  (elscreen-notify-screen-modification 'force))

(defun elscreen-display-last-message ()
  "Repeat the last message displayed in the mini-buffer."
  (interactive)
  (elscreen-message elscreen-last-message 5))

(defun elscreen-display-time ()
  "Show system information."
  (interactive)
  (elscreen-message
   (format "%s %s / %s"
           (current-time-string)
           (nth 1 (current-time-zone))
           (mapconcat
            (lambda (load)
              (format "%.2f" (/ load 100.0)))
            (load-average) " "))))

(defun elscreen-select-and-goto ()
  (interactive)
  (let* ((screen-list (sort (elscreen-get-screen-list) '<))
         (screen-to-name-alist (elscreen-get-screen-to-name-alist))
         (command-list '(("c" . elscreen-create)
                         ("n" . elscreen-next)
                         ("p" . elscreen-previous)
                         ("t" .  elscreen-toggle)))
         (truncate-length (- (frame-width) 6))
         (candidate-window-height (max (+ (elscreen-get-number-of-screens) 4)
                                       window-min-height))
         (candidate-buffer (get-buffer-create
                            (format " *ElScreen-select:%s*"
                                    (prin1-to-string (selected-frame)))))
         (candidate (concat
                     "Current screen list: \n\n"
                     (mapconcat
                      (lambda (screen)
                        (format "  %d%s %s\n" screen
                                (elscreen-status-label screen)
                                (elscreen-truncate-screen-name
                                 (get-alist screen screen-to-name-alist)
                                 truncate-length)))
                      screen-list nil)))
         (prompt "Select screen or (c)reate, (n)ext, (p)revious, (t)oggle: ")
         (minibuffer-map (copy-keymap minibuffer-local-map))
         window frame-last-window command-or-target-screen mini-hist)
    ;; prepare window to show candidates
    (save-window-excursion
      (setq frame-last-window (previous-window (static-if elscreen-on-xemacs
                                                   (frame-highest-window)
                                                 (frame-first-window))))
      (while (minibuffer-window-active-p frame-last-window)
        (setq frame-last-window (previous-window frame-last-window)))
      (while (and (not (one-window-p))
                  (or (< (window-width frame-last-window)
                         (frame-width))
                      (< (window-height frame-last-window)
                         (+ candidate-window-height window-min-height))))
        (setq window frame-last-window)
        (setq frame-last-window (previous-window window))
        (delete-window window))
      (select-window (split-window frame-last-window))
      (shrink-window (- (window-height) candidate-window-height))
      ;; now switch to the buffer for candidates and fill it
      (switch-to-buffer candidate-buffer)
      (let ((buffer-read-only nil))
        (erase-buffer)
        (insert candidate)
        (goto-char (point-min))
        (save-excursion
          (while (not (eobp))
            (when (looking-at "^  \\([0-9]\\)\\(.\\) \\(.*\\)$")
              (put-text-property
               (match-beginning 1) (match-end 1) 'face 'bold)
              (cond
               ((string= (match-string 2) "+")
                (put-text-property
                 (match-beginning 3) (match-end 3) 'face 'bold))))
            (forward-line 1)))
        (setq buffer-read-only t)
        (set-buffer-modified-p nil))
      ;; make keymap for minibuffer
      (suppress-keymap minibuffer-map t)
      (define-key minibuffer-map "\C-g" 'abort-recursive-edit)
      (define-key minibuffer-map "\C-m" 'exit-recursive-edit)
      (define-key minibuffer-map "q" 'exit-recursive-edit)
      (define-key minibuffer-map " " 'exit-recursive-edit)
      (mapcar
       (lambda (command)
         (define-key minibuffer-map (car command) 'self-insert-and-exit))
       command-list)
      (mapcar
       (lambda (screen)
         (define-key minibuffer-map (number-to-string screen)
           'self-insert-and-exit))
       screen-list)
      ;; read key from minibuffer
      (unwind-protect
          (setq command-or-target-screen
                (read-from-minibuffer prompt nil minibuffer-map
                                      nil 'mini-hist))
        (kill-buffer candidate-buffer)))
    (cond
     ((string= command-or-target-screen ""))
     ((get-alist command-or-target-screen command-list)
      (funcall (get-alist command-or-target-screen command-list)))
     (t
      (elscreen-goto (string-to-number command-or-target-screen))))))

(defun elscreen-find-and-goto-by-buffer (&optional buffer create noselect)
  "Go to the screen that has the window with buffer BUFFER,
creating one if none already exists."
  (interactive)
  (let* ((prompt "Go to the screen with specified buffer: ")
         (create (or create (interactive-p)))
         (buffer-name (or (and (bufferp buffer) (buffer-name buffer))
                          (and (stringp buffer) buffer)
                          (and (featurep 'iswitchb)
                               (iswitchb-read-buffer prompt))
                          (read-buffer prompt)))
         (target-screen (elscreen-find-screen-by-buffer
                         (get-buffer-create buffer-name) create)))
    (when target-screen
      (elscreen-goto target-screen)
      (unless noselect
        (select-window (get-buffer-window buffer-name))))
    target-screen))

(defun elscreen-find-file (filename)
  "Edit file FILENAME.
Switch to a screen visiting file FILENAME,
creating one if none already exists."
  (interactive "FFind file in new screen: ")
  (elscreen-find-and-goto-by-buffer (find-file-noselect filename) 'create))

(defun elscreen-find-file-read-only (filename)
  "Edit file FILENAME with new screen but don't allow changes.
Like \\[elscreen-find-file] but marks buffer as read-only.
Use \\[toggle-read-only] to permit editing."
  (interactive "FFind file read-only in new screen: ")
  (elscreen-find-file filename)
  (toggle-read-only 1))

(defun elscreen-dired (dirname &optional switches)
  (interactive (progn
                 (or (featurep 'dired) (require 'dired))
                 (dired-read-dir-and-switches "in new screen ")))
  (elscreen-find-and-goto-by-buffer (dired-noselect dirname switches) 'create))

(defun elscreen-execute-extended-command (prefix-arg)
  (interactive "P")
  (let ((prefix-arg prefix-arg)
        (prefix-key (key-description elscreen-prefix-key))
        target-screen)
    (setq this-command (intern (completing-read
                                ;; Note: this has the hard-wired
                                ;;  "C-u" and "M-x" string bug in common
                                ;;  with all Emacs's.
                                ;; (i.e. it prints C-u and M-x regardless of
                                ;; whether some other keys were actually bound
                                ;; to `execute-extended-command' and
                                ;; `universal-argument'.
                                (cond ((eq prefix-arg '-)
                                       (format "- %s M-x " prefix-key))
                                      ((equal prefix-arg '(4))
                                       (format "C-u %s M-x " prefix-key))
                                      ((integerp prefix-arg)
                                       (format "%d %s M-x "
                                               prefix-arg prefix-key))
                                      ((and (consp prefix-arg)
                                            (integerp (car prefix-arg)))
                                       (format "%d %s M-x "
                                               (car prefix-arg) prefix-key))
                                      (t
                                       (format "%s M-x " prefix-key)))
                                obarray 'commandp t nil
                                (static-if elscreen-on-xemacs
                                    'read-command-history
                                  'extended-command-history))))
    (if (setq target-screen (elscreen-create-internal 'noerror))
        (elscreen-goto target-screen)
      (select-window (split-window)))
    (command-execute this-command t)))


;;; Mode Line & Menu & Tab

;; GNU Emacs
(static-when elscreen-on-emacs
  ;; Mode Line
  (defvar elscreen-e21-mode-line-string "[0]")
  (defun elscreen-e21-mode-line-update ()
    (when (elscreen-screen-modified-p 'elscreen-e21-mode-line-update)
      (setq elscreen-e21-mode-line-string
            (format "[%d]" (elscreen-get-current-screen)))
      (force-mode-line-update)))

  (let ((point (or
                ;; GNU Emacs 21.3.50 or later
                (memq 'mode-line-position mode-line-format)
                ;; GNU Emacs 21.3.1
                (memq 'mode-line-buffer-identification mode-line-format)))
        (elscreen-mode-line-elm '(elscreen-display-screen-number
                                  (" " elscreen-e21-mode-line-string))))
    (when (null (member elscreen-mode-line-elm mode-line-format))
      (setcdr point (cons elscreen-mode-line-elm (cdr point)))))

  (add-hook 'elscreen-screen-update-hook 'elscreen-e21-mode-line-update)

  ;; Menu
  (define-key-after (lookup-key global-map [menu-bar]) [elscreen]
    (cons "ElScreen" (make-sparse-keymap "ElScreen")) 'buffer)

  (defvar elscreen-e21-menu-bar-command-entries
    (list (list 'elscreen-command-separator
                'menu-item
                "--")
          (list 'elscreen-create
                'menu-item
                "Create Screen"
                'elscreen-create
                :help "Create a new screen and switch to it")
          (list 'elscreen-clone
                'menu-item
                "Clone Screen"
                'elscreen-clone
                :help "Create a new screen with the window-configuration of current screen")
          (list 'elscreen-kill
                'menu-item
                "Kill Screen"
                'elscreen-kill
                :help "Kill current screen")
          (list 'elscreen-kill-screen-and-buffers
                'menu-item
                "Kill Screen and Buffers"
                'elscreen-kill-screen-and-buffers
                :help "Kill current screen and buffers")
          (list 'elscreen-kill-others
                'menu-item
                "Kill Other Screens"
                'elscreen-kill-others
                :help "Kill other screens")
          (list 'elscreen-next
                'menu-item
                "Next Screen"
                'elscreen-next
                :help "Switch to the \"next\" screen in a cyclic order")
          (list 'elscreen-previous
                'menu-item
                "Previous Screen"
                'elscreen-previous
                :help "Switch to the \"previous\" screen in a cyclic order")
          (list 'elscreen-toggle
                'menu-item
                "Toggle Screen"
                'elscreen-toggle
                :help "Toggle to the screen selected previously")
          (list 'elscreen-command-separator
                'menu-item
                "--")
          (list 'elscreen-toggle-display-screen-number
                'menu-item
                "Display Screen Number"
                'elscreen-toggle-display-screen-number
                :help "Display screen number on the mode line"
                :button '(:toggle . elscreen-display-screen-number))
          (list 'elscreen-toggle-display-tab
                'menu-item
                "Display Tab"
                'elscreen-toggle-display-tab
                :help "Display tab on the top of screen"
                :button '(:toggle . elscreen-display-tab))))

  (defun elscreen-e21-menu-bar-update (&optional force)
    (when (and (lookup-key (current-global-map) [menu-bar elscreen])
               (or force
                   (elscreen-screen-modified-p 'elscreen-menu-bar-update)))
      (let ((screen-list (sort (elscreen-get-screen-list) '<))
            (screen-to-name-alist (elscreen-get-screen-to-name-alist))
            (elscreen-menu nil))
        (setq elscreen-menu
              (mapcar
               (lambda (screen)
                 (list (string-to-char (number-to-string screen))
                       'menu-item
                       (format "%d%s %s" screen
                               (elscreen-status-label screen)
                               (elscreen-truncate-screen-name
                                (get-alist screen screen-to-name-alist) 25))
                       'elscreen-jump
                       :keys (format "%s %d"
                                     (key-description elscreen-prefix-key)
                                     screen)))
              screen-list))
        (setq elscreen-menu
              (nconc elscreen-menu elscreen-e21-menu-bar-command-entries))
        (setq elscreen-menu
              (cons 'keymap (cons "Select Screen" elscreen-menu)))
        (define-key (current-global-map) [menu-bar elscreen]
          (cons (copy-sequence "ElScreen") elscreen-menu)))))

  (add-hook 'elscreen-screen-update-hook 'elscreen-e21-menu-bar-update)

  ;; Tab
  (defvar elscreen-e21-tab-format nil)
  (make-variable-buffer-local 'elscreen-e21-tab-format)

  (defsubst elscreen-e21-tab-create-keymap (&rest definitions)
    (let ((keymap (make-sparse-keymap))
          (key-function-pairs
           (eval-when-compile
             (mapcar
              (lambda (key)
                (cons key 'ignore))
              (list 'mouse-1 'mouse-2 'mouse-3
                    'down-mouse-1 'down-mouse-2 'down-mouse-3
                    'drag-mouse-1 'drag-mouse-2 'drag-mouse-3)))))
      (while definitions
        (set-alist 'key-function-pairs (car definitions) (cadr definitions))
        (setq definitions (cddr definitions)))
      (mapc
       (lambda (key-function-pair)
         (let ((key (car key-function-pair))
               (function (cdr key-function-pair)))
           (define-key keymap (vector 'header-line key) function)))
       key-function-pairs)
      keymap))

  (defsubst elscreen-e21-tab-width ()
    (if (numberp elscreen-display-tab)
        elscreen-display-tab
      (let* ((number-of-screens (elscreen-get-number-of-screens))
             (available-width
              (- (frame-width) (if elscreen-tab-display-control 4 0)))
             (tab-width
              (round (- (/ available-width number-of-screens)
                        (if elscreen-tab-display-kill-screen 5.5 1.5)))))
        (max (min tab-width 16) 1))))

  (defun elscreen-e21-tab-escape-% (string)
    (if (string-match "%" string)
        (let ((retval "")
              start (end 0) substring)
          (while (setq start end)
            (setq end (next-property-change start string))
            (setq substring (replace-regexp-in-string
                             "%" "%%" (substring string start end)))
            (set-text-properties 0 (length substring)
                                 (text-properties-at start string) substring)
            (setq retval (concat retval substring)))
          retval)
      string))

  (defun elscreen-e21-tab-update (&optional force)
    (when (and (not (window-minibuffer-p))
               (or (elscreen-screen-modified-p 'elscreen-tab-update) force))
      (walk-windows
       (lambda (window)
         (with-current-buffer (window-buffer window)
           (when (and (boundp 'elscreen-e21-tab-format)
                      (equal header-line-format elscreen-e21-tab-format)
                      (or (not (eq (window-buffer window)
                                   (window-buffer (frame-first-window))))
                          (not elscreen-display-tab)))
             (kill-local-variable 'elscreen-e21-tab-format)
             (setq header-line-format nil))))
       'other 'other)

      (when elscreen-display-tab
        (let ((screen-list (sort (elscreen-get-screen-list) '<))
              (screen-to-name-alist (elscreen-get-screen-to-name-alist))
              (current-screen (elscreen-get-current-screen))
              (half-space (eval-when-compile
                            (propertize
                             " "
                             'display '(space :width 0.5))))
              (tab-separator (eval-when-compile
                               (propertize
                                " "
                                'face 'elscreen-tab-background-face
                                'display '(space :width 0.5))))
              (control-tab (eval-when-compile
                             (propertize
                              "<->"
                              'face 'elscreen-tab-control-face
                              'local-map (elscreen-e21-tab-create-keymap
                                          'mouse-1 'elscreen-previous
                                          'mouse-2 'elscreen-create
                                          'mouse-3 'elscreen-next)
                              'help-echo "mouse-1: previous screen, mouse-2: create new screen, mouse-3: next screen"))))
          (with-current-buffer (window-buffer (frame-first-window))
            (kill-local-variable 'elscreen-e21-tab-format)
            (when elscreen-tab-display-control
              (setq elscreen-e21-tab-format
                    (nconc
                     elscreen-e21-tab-format
                     (list
                      control-tab
                      tab-separator))))

            (mapcar
             (lambda (screen)
               (let ((kill-screen
                      (propertize
                       "[X]"
                       'local-map (elscreen-e21-tab-create-keymap
                                   'mouse-1 `(lambda (e)
                                               (interactive "e")
                                               (elscreen-kill ,screen))
                                   'M-mouse-1 `(lambda (e)
                                                 (interactive "e")
                                                 (elscreen-kill-screen-and-buffers ,screen)))
                       'help-echo (format "mouse-1: kill screen %d, M-mouse-1: kill screen %d and buffers on it" screen screen))))
                 (setq elscreen-e21-tab-format
                       (nconc
                        elscreen-e21-tab-format
                        (list
                         (propertize
                          (concat
                           (when (or (eq elscreen-tab-display-kill-screen 'left)
                                     (eq elscreen-tab-display-kill-screen t))
                             kill-screen)
                           half-space
                           (propertize
                            (format "%d%s%s%s"
                                    screen
                                    (elscreen-status-label screen)
                                    half-space
                                    (elscreen-e21-tab-escape-%
                                     (elscreen-truncate-screen-name
                                      (get-alist screen screen-to-name-alist)
                                      (elscreen-e21-tab-width) t)))
                            'help-echo (get-alist screen screen-to-name-alist)
                            'local-map (elscreen-e21-tab-create-keymap
                                        'mouse-1 `(lambda (e)
                                                    (interactive "e")
                                                    (elscreen-goto ,screen))))
                           (when (eq elscreen-tab-display-kill-screen 'right)
                             (concat half-space kill-screen)))
                          'face (if (eq current-screen screen)
                                    'elscreen-tab-current-screen-face
                                  'elscreen-tab-other-screen-face))
                         tab-separator)))))
               screen-list)

            (setq elscreen-e21-tab-format
                  (nconc
                   elscreen-e21-tab-format
                   (list
                    (propertize
                     (make-string (window-width) ?\ )
                     'face 'elscreen-tab-background-face
                     'local-map (elscreen-e21-tab-create-keymap)))))

            (setq header-line-format elscreen-e21-tab-format))))))

  (add-hook 'elscreen-screen-update-hook 'elscreen-e21-tab-update))

;; XEmacs
(static-when elscreen-on-xemacs
  ;; Mode Line
  (defvar elscreen-xmas-mode-line-string "[0]")
  (defun elscreen-xmas-mode-line-update ()
    (when (elscreen-screen-modified-p 'elscreen-xmas-mode-line-update)
      (setq elscreen-xmas-mode-line-string
            (format "[%d]" (elscreen-get-current-screen)))
      (force-mode-line-update)))

  (let ((point (memq 'global-mode-string mode-line-format))
        (elscreen-mode-line-elm '(elscreen-display-screen-number
                                  (" " elscreen-xmas-mode-line-string))))
    (if (null (member elscreen-mode-line-elm mode-line-format))
        (setcdr point (cons elscreen-mode-line-elm (cdr point)))))

  (add-hook 'elscreen-screen-update-hook 'elscreen-xmas-mode-line-update)

  ;; Menu
  (defvar elscreen-xmas-menu-bar-command-entries
    '("%_ElScreen"
      :filter elscreen-xmas-menu-bar-filter
      "----"
      ["%_Create Screen" elscreen-create]
      ["%_Clone Screen" elscreen-clone]
      ["%_Kill Screen" elscreen-kill]
      ["%_Kill Screen and Buffers" elscreen-kill-screen-and-buffers]
      ["%_Kill Other Screens" elscreen-kill-others]
      ["%_Next Screen" elscreen-next]
      ["%_Previous Screen" elscreen-previous]
      ["%_Toggle Screen" elscreen-toggle]
      "----"
      ["%_Display Screen Number" elscreen-toggle-display-screen-number
       :style toggle :selected elscreen-display-screen-number]
      ["%_Display Tab" elscreen-toggle-display-tab
       :style toggle :selected elscreen-display-tab]))

  (defconst elscreen-xmas-menubar (copy-sequence default-menubar))
  (let ((menubar elscreen-xmas-menubar))
    (catch 'buffers-menu-search
      (while (car menubar)
        (when (equal (car (car menubar)) "%_Buffers")
          (throw 'buffers-menu-search menubar))
        (setq menubar (cdr menubar))))
    (setcdr menubar
            (cons elscreen-xmas-menu-bar-command-entries (cdr menubar))))

  (set-menubar elscreen-xmas-menubar)
  (set-menubar-dirty-flag)

  (defun elscreen-xmas-menu-bar-filter (menu)
    (let ((screen-list (sort (elscreen-get-screen-list) '<))
          (screen-to-name-alist (elscreen-get-screen-to-name-alist))
          (elscreen-menu nil))
      (setq elscreen-menu
            (mapcar
             (lambda (screen)
               (vector (format "%d%s %s" screen
                               (elscreen-status-label screen)
                               (elscreen-truncate-screen-name
                                (get-alist screen screen-to-name-alist) 25))
                       `(elscreen-goto ,screen)
                       :active t
                       :keys (format "%s %d"
                                     (key-description elscreen-prefix-key)
                                     screen)))
             screen-list))
      (append elscreen-menu menu)))

  ;; Tab
  (defsubst elscreen-xmas-tab-width ()
    (if (numberp elscreen-display-tab) elscreen-display-tab 16))

  (defvar elscreen-xmas-tab-glyph (make-glyph))
  (let* ((gutter-string (copy-sequence "\n"))
         (gutter-elscreen-tab-extent (make-extent 0 1 gutter-string)))
    (set-extent-begin-glyph gutter-elscreen-tab-extent elscreen-xmas-tab-glyph)
    (mapcar
     (lambda (console-type)
       (when (valid-image-instantiator-format-p 'tab-control console-type)
         (set-specifier top-gutter-border-width 0 'global console-type)
         (set-gutter-element top-gutter 'elscreen-tab
                             gutter-string 'global console-type)))
     (console-type-list)))

  (defun elscreen-xmas-tab-update (&optional force)
    (if (or (not elscreen-display-tab)
            (window-dedicated-p (selected-window)))
        (set-gutter-element-visible-p default-gutter-visible-p
                                      'elscreen-tab nil)
      (when (and (not (window-minibuffer-p))
                 (or (elscreen-screen-modified-p 'elscreen-tab-update) force))
        (set-gutter-element-visible-p default-gutter-visible-p
                                      'elscreen-tab t)
        (when (valid-image-instantiator-format-p 'tab-control)
          (let* ((screen-list (sort (elscreen-get-screen-list) '<))
                 (screen-to-name-alist (elscreen-get-screen-to-name-alist))
                 (current-screen (elscreen-get-current-screen))
                 (tab-items
                  (mapcar
                   (lambda (screen)
                     (vector
                      (format "%d%s %s" screen
                              (elscreen-status-label screen)
                              (elscreen-truncate-screen-name
                               (get-alist screen screen-to-name-alist)
                               (elscreen-xmas-tab-width) t))
                      `(elscreen-goto ,screen)
                      :selected (eq screen current-screen)))
                   screen-list)))
            (set-glyph-image
             elscreen-xmas-tab-glyph
             (vector 'tab-control
                     :descriptor "ElScreen"
                     :face 'default
                     :orientation 'top
                     :pixel-width '(gutter-pixel-width)
                     :items tab-items)
             (selected-frame)))
          (set-gutter-dirty-p 'top)))))

  (add-hook 'elscreen-screen-update-hook 'elscreen-xmas-tab-update))

;;; Command-line processing at startup time

(defun elscreen-command-line-funcall (switch-string)
  (let ((argval (intern (car command-line-args-left)))
        screen elscreen-window-configuration)
    (setq command-line-args-left (cdr command-line-args-left))
    (save-window-excursion
      (elscreen-apply-window-configuration
       (elscreen-default-window-configuration))
      (if (commandp argval)
          (command-execute argval)
        (funcall argval))
      (setq elscreen-window-configuration
            (elscreen-current-window-configuration)))
    (setq file-count (1+ file-count))
    (cond
     ((= file-count 1)
      (elscreen-apply-window-configuration elscreen-window-configuration))
     ((setq screen (elscreen-create-internal 'noerror))
      (elscreen-set-window-configuration screen
                                           elscreen-window-configuration)))))

(defun elscreen-command-line-find-file (file file-count &optional line column)
  (let ((line (or line 0))
        (column (or column 0)))
    (cond
     ((= file-count 1)
      (find-file file))
     ((> file-count 10)
      (find-file-noselect file))
     (t
      (elscreen-find-screen-by-buffer (find-file-noselect file) 'create)))
    (or (zerop line)
        (goto-line line))
    (unless (< column 1)
      (move-to-column (1- column)))))

(when elscreen-startup-command-line-processing
  (setq command-switch-alist
        (append command-switch-alist
                '(("-elscreen-funcall" . elscreen-command-line-funcall)
                  ("-e"                . elscreen-command-line-funcall))))

  (static-when elscreen-on-emacs
    (defun elscreen-e21-command-line ()
      (when (string-match "\\`-" argi)
        (error "Unknown option `%s'" argi))
      (setq file-count (1+ file-count))
      (setq inhibit-startup-buffer-menu t)
      (let* ((file
              (expand-file-name
               (command-line-normalize-file-name orig-argi)
               dir)))
        (elscreen-command-line-find-file file file-count line column))
      (setq line 0)
      (setq column 0)
      t)

    (add-hook 'after-init-hook (lambda ()
                                 (add-to-list 'command-line-functions
                                              'elscreen-e21-command-line t))))

  (static-when elscreen-on-xemacs
    (defadvice command-line-1 (around elscreen-xmas-command-line-1 activate)
      (cond
       ((null command-line-args-left)
        ad-do-it)
       (t
        (let ((dir command-line-default-directory)
              (file-count 0)
              (line nil)
              (end-of-options nil)
              file-p arg tem)
          (while command-line-args-left
            (setq arg (pop command-line-args-left))
            (cond
             (end-of-options
              (setq file-p t))
             ((setq tem (when (eq (aref arg 0) ?-)
                          (or (assoc arg command-switch-alist)
                              (assoc (substring arg 1)
                                     command-switch-alist))))
              (funcall (cdr tem) arg))
             ((string-match "\\`\\+[0-9]+\\'" arg)
              (setq line (string-to-int arg)))
             ((or (string= arg "-") (string= arg "--"))
              (setq end-of-options t))
             (t
              (setq file-p t)))

            (when file-p
              (setq file-p nil)
              (incf file-count)
              (elscreen-command-line-find-file
               (expand-file-name arg dir) file-count line)
              (setq line nil)))))))))

;;; Unsupported Functions...

(defun elscreen-link ()
  (interactive)
  (cond
   ((null (one-window-p))
    (elscreen-message "current screen must not have two or more window!"))
   ((or (null (elscreen-get-previous-screen))
        (elscreen-one-screen-p))
    (elscreen-message "must specify previous screen!"))
   ((and (elscreen-goto (elscreen-get-previous-screen))
         (null (one-window-p)))
    (elscreen-goto (elscreen-get-previous-screen))
    (elscreen-message "previous screen must not have two or more window!"))
   (t
    (let ((elscreen-link-buffer (current-buffer)))
      (elscreen-kill)
      (switch-to-buffer-other-window elscreen-link-buffer)))))

(defun elscreen-split ()
  (interactive)
  (if (and (null (one-window-p))
           (< (elscreen-get-number-of-screens) 10))
      (let ((elscreen-split-buffer (current-buffer)))
        (delete-window)
        (elscreen-create)
        (switch-to-buffer elscreen-split-buffer)
        (elscreen-goto (elscreen-get-previous-screen)))
    (elscreen-message "cannot split screen!")))

;;; Start ElScreen!

(defun elscreen-start ()
  (mapcar
   (lambda (frame)
     (elscreen-make-frame-confs frame 'keep))
   (frame-list))
  (let ((prefix-key elscreen-prefix-key)
        (elscreen-prefix-key nil))
    (elscreen-set-prefix-key prefix-key)))

(elscreen-start)
