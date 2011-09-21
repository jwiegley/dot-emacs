;;; wg-tabs --- Tabbar for Workgroups from Windows, taken from ElScreen

;; Copyright (C) 2011 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 21 Sep 2011
;; Version: 1.0
;; Keywords: workgroups tabs tabbar elscreen
;; X-URL: https://github.com/jwiegley/dot-emacs

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or (at
;; your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 59 Temple Place - Suite 330,
;; Boston, MA 02111-1307, USA.

;;; Commentary:

;; Tabbar for Workgroups from Windows, taken from ElScreen.  Just load this
;; file and away you go.

(require 'workgroups)

(defgroup wg-tabs nil
  "Tab controls for Workgroups from Windows, taken from ElScreen."
  :group 'workgroups
  :version wg-version)

(defcustom wg-display-tab t
  "Specify how the tabs at the top of frame should be displayed.
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
           (when (fboundp 'wg-e21-tab-update)
             (wg-e21-tab-update t))))
  :group 'wg-tabs)

(defcustom wg-tab-display-control t
  "Non-nil to display control tab at the most left side."
  :tag "Show/Hide the Control Tab"
  :type 'boolean
  :set (lambda (symbol value)
         (custom-set-default symbol value)
         (when (fboundp 'wg-e21-tab-update)
           (wg-e21-tab-update t)))
  :group 'wg-tabs)

(defcustom wg-tab-display-kill-screen 'left
  "Location of the icons to kill a screen on each tab.
Possible values are 'left, 'right, or nil (to hide them)."
  :tag "Location of Buttons to Kill Screen on Each Tab"
  :type '(choice (const :tag "Left" left)
                 (const :tag "Right" right)
                 (const :tag "None" nil))
  :set (lambda (symbol value)
         (custom-set-default symbol value)
         (when (fboundp 'wg-e21-tab-update)
           (wg-e21-tab-update t)))
  :group 'wg-tabs)

(defface wg-tab-background-face
  '((((type x w32 mac) (class color))
     :background "Gray50")
    (((class color))
     (:background "black")))
  "Face to fontify background of tab line."
  :group 'wg-tabs)

(defface wg-tab-control-face
  '((((type x w32 mac) (class color))
     (:background "white" :foreground "black" :underline "Gray50"))
    (((class color))
     (:background "white" :foreground "black" :underline t))
    (t (:underline t)))
  "Face for control tab."
  :group 'wg-tabs)

(defface wg-tab-current-screen-face
  '((((class color))
     (:background "white" :foreground "black"))
    (t (:underline t)))
  "Face for current screen tab."
  :group 'wg-tabs)

(defface wg-tab-other-screen-face
  '((((type x w32 mac) (class color))
     :background "Gray85" :foreground "Gray50")
    (((class color))
     (:background "blue" :foreground "black" :underline t)))
  "Face for tabs other than current screen one."
  :group 'wg-tabs)

(defvar wg-e21-tab-format nil)
(make-variable-buffer-local 'wg-e21-tab-format)

(defvar wg-modified t)

(defun wg-was-modified ()
  (setq wg-modified t)
  (wg-e21-tab-update t))

(add-hook 'wg-switch-hook 'wg-was-modified)

(defadvice wg-set-workgroup-prop
  (after wg-set-workgroup-prop-is-dirty activate)
  ""
  (wg-was-modified))
(defadvice wg-delete
  (after wg-delete-is-dirty activate)
  ""
  (wg-was-modified))
(defadvice wg-add
  (after wg-add-is-dirty activate)
  ""
  (wg-was-modified))
(defadvice wg-cyclic-offset-workgroup
  (after wg-cyclic-offset-workgroup-is-dirty activate)
  ""
  (wg-was-modified))
(defadvice wg-list-swap
  (after wg-list-swap-is-dirty activate)
  ""
  (wg-was-modified))

(defsubst wg-get-number-of-screens ()
  (length (wg-list)))
(defsubst wg-screen-modified-p (&optional notifier)
  (let ((modified wg-modified))
    (setq wg-modified nil)
    wg-modified))
(defsubst wg-get-screen-list ()
  (mapcar #'(lambda (wg) (cdr (assq 'uid wg))) (wg-list)))
(defsubst wg-get-screen-to-name-alist ()
  (mapcar #'(lambda (wg) (cons (cdr (assq 'uid wg))
                          (cdr (assq 'name wg)))) (wg-list)))
(defsubst wg-get-current-screen ()
  (cdr (assq 'uid (wg-current-workgroup))))

(defun wg-screen-to-workgroup (screen)
  (catch 'found
    (ignore
     (dolist (w (wg-list))
       (let ((uid (cdr (assq 'uid w))))
         (if (= screen uid)
             (throw 'found w)))))))

(defun wg-status-label (screen)
  (catch 'found
    (dolist (w (wg-list))
      (let ((uid (cdr (assq 'uid w))))
        (if (= screen uid)
            (cond
             ((eq w (wg-current-workgroup  t))
              (throw 'found "+"))
             ((eq w (wg-previous-workgroup  t))
              (throw 'found "-"))))))
    " "))

(defun wg-goto (screen)
  (wg-switch-to-workgroup (wg-screen-to-workgroup screen)))

(defun wg-truncate-screen-name (screen-name truncate-length &optional padding)
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

(defsubst wg-e21-tab-create-keymap (&rest definitions)
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

(defsubst wg-e21-tab-width ()
  (if (numberp wg-display-tab)
      wg-display-tab
    (let* ((number-of-screens (wg-get-number-of-screens))
           (available-width
            (- (frame-width) (if wg-tab-display-control 4 0)))
           (tab-width
            (round (- (/ available-width number-of-screens)
                      (if wg-tab-display-kill-screen 5.5 1.5)))))
      (max (min tab-width 16) 1))))

(defun wg-e21-tab-escape-% (string)
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

(defun get-alist (key alist)
  (cdr (assoc key alist)))

(defun wg-e21-tab-update (&optional force)
  (when (and (not (window-minibuffer-p))
             (or (wg-screen-modified-p 'wg-tab-update) force))
    (walk-windows
     (lambda (window)
       (with-current-buffer (window-buffer window)
         (when (and (boundp 'wg-e21-tab-format)
                    (equal header-line-format wg-e21-tab-format)
                    (or (not (eq (window-buffer window)
                                 (window-buffer (frame-first-window))))
                        (not wg-display-tab)))
           (kill-local-variable 'wg-e21-tab-format)
           (setq header-line-format nil))))
     'other 'other)

    (when wg-display-tab
      (let ((screen-list (sort (wg-get-screen-list) '<))
            (screen-to-name-alist (wg-get-screen-to-name-alist))
            (current-screen (wg-get-current-screen))
            (half-space (eval-when-compile
                          (propertize
                           " "
                           'display '(space :width 0.5))))
            (tab-separator (eval-when-compile
                             (propertize
                              " "
                              'face 'wg-tab-background-face
                              'display '(space :width 0.5))))
            (control-tab (eval-when-compile
                           (propertize
                            "<->"
                            'face 'wg-tab-control-face
                            'local-map (wg-e21-tab-create-keymap
                                        'mouse-1 'wg-switch-left
                                        'mouse-2 'wg-create-workgroup
                                        'mouse-3 'wg-switch-right)
                            'help-echo "mouse-1: previous screen, mouse-2: create new screen, mouse-3: next screen"))))
        (with-current-buffer (window-buffer (frame-first-window))
          (kill-local-variable 'wg-e21-tab-format)
          (when wg-tab-display-control
            (setq wg-e21-tab-format
                  (nconc
                   wg-e21-tab-format
                   (list
                    control-tab
                    tab-separator))))

          (mapc
           (lambda (screen)
             (let ((kill-screen
                    (propertize
                     "[X]"
                     'local-map (wg-e21-tab-create-keymap
                                 'mouse-1 `(lambda (e)
                                             (interactive "e")
                                             (wg-kill-workgroup
                                              (wg-screen-to-workgroup ,screen)))
                                 'M-mouse-1 `(lambda (e)
                                               (interactive "e")
                                               (wg-kill-workgroup-and-buffers
                                                (wg-screen-to-workgroup ,screen))))
                     'help-echo (format "mouse-1: kill screen %d, M-mouse-1: kill screen %d and buffers on it" screen screen))))
               (setq wg-e21-tab-format
                     (nconc
                      wg-e21-tab-format
                      (list
                       (propertize
                        (concat
                         (when (or (eq wg-tab-display-kill-screen 'left)
                                   (eq wg-tab-display-kill-screen t))
                           kill-screen)
                         half-space
                         (propertize
                          (format "%d%s%s%s"
                                  screen
                                  (wg-status-label screen)
                                  half-space
                                  (wg-e21-tab-escape-%
                                   (wg-truncate-screen-name
                                    (get-alist screen screen-to-name-alist)
                                    (wg-e21-tab-width) t)))
                          'help-echo (get-alist screen screen-to-name-alist)
                          'local-map (wg-e21-tab-create-keymap
                                      'mouse-1 `(lambda (e)
                                                  (interactive "e")
                                                  (wg-goto ,screen))))
                         (when (eq wg-tab-display-kill-screen 'right)
                           (concat half-space kill-screen)))
                        'face (if (eq current-screen screen)
                                  'wg-tab-current-screen-face
                                'wg-tab-other-screen-face))
                       tab-separator)))))
           screen-list)

          (setq wg-e21-tab-format
                (nconc
                 wg-e21-tab-format
                 (list
                  (propertize
                   (make-string (window-width) ?\ )
                   'face 'wg-tab-background-face
                   'local-map (wg-e21-tab-create-keymap)))))

          (setq header-line-format wg-e21-tab-format))))))

(wg-e21-tab-update t)

(provide 'wg-tabs)

;;; wg-tabs.el ends here
