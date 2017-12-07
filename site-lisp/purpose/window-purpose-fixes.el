;;; window-purpose-fixes.el --- fix integration issues with other features -*- lexical-binding: t -*-

;; Copyright (C) 2015, 2016 Bar Magal

;; Author: Bar Magal
;; Package: purpose

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;; This files contains fixes that allow Purpose to work well with other
;; features, or to allow other features to work well with Purpose.

;;; Code:

(require 'window-purpose-switch)
(require 'window-purpose-configuration)



;;; `compilation-next-error-function' sometimes hides the compilation buffer
;;; when Purpose is on. Solution: make the buffer's window dedicated while
;;; executing `compilation-next-error-function'

(define-purpose-compatible-advice 'compilation-next-error-function
    :around purpose--fix-compilation-next-error
    (&rest args)
    "Integrate Purpose and `compilation-next-error-function'.
Advice that prevents `compilation-next-error-function' from hiding the
compilation buffer.  This is done by ensuring that the buffer is
dedicated for the duration of the function.
This function should be advised around
`compilation-next-error-function'."
  ;; new style advice
  ((let* ((compilation-window (get-buffer-window (marker-buffer (point-marker))))
          (old-window-dedicated-p (window-dedicated-p compilation-window)))
     (set-window-dedicated-p compilation-window t)
     (unwind-protect
         (apply oldfun args)
       (set-window-dedicated-p compilation-window old-window-dedicated-p))))

  ;; old style advice
  ((let* ((compilation-window (get-buffer-window (marker-buffer (point-marker))))
          (old-window-dedicated-p (window-dedicated-p compilation-window)))
     (set-window-dedicated-p compilation-window t)
     (unwind-protect
         ad-do-it
       (set-window-dedicated-p compilation-window old-window-dedicated-p)))))



;;; Hydra's *LV* buffer should be ignored by Purpose
(defun purpose--fix-hydra-lv ()
  "Add hydra's LV buffer to Purpose's ignore list."
  (eval-after-load 'lv
    '(add-to-list 'purpose-action-function-ignore-buffer-names "^ \\*LV\\*$")))



;;; Helm's buffers should be ignored, and they should have their own purpose
(defvar purpose--helm-conf
  (purpose-conf "helm"
                :regexp-purposes '(("^\\*Helm" . helm)
                                   ("^\\*helm" . helm)))
  "Purpose configuration for helm.")
(defun purpose--fix-helm ()
  "Fix issues with helm.
Add helm's buffers to Purposes's ignore list.
Install helm's purpose configuration."
  (eval-after-load 'helm
    '(add-to-list 'purpose-action-function-ignore-buffer-names "^\\*Helm"))
  (eval-after-load 'helm
    '(add-to-list 'purpose-action-function-ignore-buffer-names "^\\*helm"))
  (eval-after-load 'helm
    '(purpose-set-extension-configuration :helm purpose--helm-conf)))



;;; Neotree handles display of its own buffer and of opening files from the
;;; neotree buffer in a way that doesn't work well with Purpose.
;;; We override how neotree displays its buffer.  When neotree tries to open a
;;; file in a fancy way, we let it.
;;; The integration issues fixed here:
;;; - calling `neotree' from a dedicated window opened neotree on the right,
;;;   with 2 or 3 horizontally-split windows showing the buffer from the
;;;   dedicated window (see https://github.com/jaypei/emacs-neotree/issues/124)
;;; - with one 'edit' window, one 'general' window, select the 'general' window,
;;;   then call `neotree'. from neotree window, open an 'edit' buffer in a new
;;;   split (press '-' or '|'). 'general' window is split in two, the new 'edit'
;;;   buffer is displayed in the 'edit' window instead of the old 'edit' buffer

(defun purpose--fix-create-neo-window ()
  "Create neotree window, with Purpose."
  (let* ((buffer (neo-global--get-buffer t))
         (window (display-buffer buffer)))
    (neo-window--init window buffer)
    (neo-global--attach)
    (neo-global--reset-width)
    window))

(defun purpose--fix-display-neotree (buffer alist)
  "Display neotree window, with Purpose."
  (let* ((first-window (frame-root-window))
         (new-window (split-window first-window nil 'left)))
    (purpose-change-buffer buffer new-window 'window alist)
    new-window))

(defun purpose--fix-neotree-1 ()
  "Integrate neotree with Purpose.
Override the display and creation of the neotree window.
When opening files from the neotree window, use Purpose only when
necessary.
Note: Don't call this function before `neotree' is loaded."
  (define-purpose-compatible-advice 'neo-global--create-window
      :around purpose-fix-neotree-create-window-advice
      (&rest args)
      "Override `neo-global--create-window' with `purpose--fix-create-neo-window'.
When `purpose--active-p' is nil, call original `neo-global--create-window'."
    ;; new style adivce
    ((if purpose--active-p
         (purpose--fix-create-neo-window)
       (apply oldfun args)))
    ;; old style advice
    ((if purpose--active-p
         (setq ad-return-value (purpose--fix-create-neo-window))
       ad-do-it)))

  (define-purpose-compatible-advice 'neo-open-file
      :around purpose-fix-neotree-open-file-advice
      (full-path &optional arg)
      "When ARG is nil, make sure Purpose is off while executing `neo-open-file'."
    ;; new style advice
    ((if (and purpose--active-p (null arg))
         (find-file full-path)
       (without-purpose (funcall oldfun full-path arg))))
    ;; old style advice
    ((if (and purpose--active-p (null arg))
         (setq ad-return-value (find-file full-path))
       (without-purpose ad-do-it))))

  ;; using purpose 'Neotree, because using 'neotree causes problems with
  ;; `purpose-special-action-sequences' ('neotree is also a function, so
  ;; `purpose--special-action-sequence' will try to call it)
  (purpose-set-extension-configuration
   :neotree
   (purpose-conf "Neotree" :name-purposes `((,neo-buffer-name . Neotree))))
  (add-to-list 'purpose-special-action-sequences
               '(Neotree purpose-display-reuse-window-buffer
                         purpose-display-reuse-window-purpose
                         purpose--fix-display-neotree))
  (purpose-advice-add 'neo-global--create-window
                      :around 'purpose-fix-neotree-create-window-advice)
  (purpose-advice-add 'neo-open-file
                      :around 'purpose-fix-neotree-open-file-advice))

(defun purpose--fix-neotree ()
  "Call `purpose--fix-neotree-1' after `neotree' is loaded."
  (eval-after-load 'neotree
    '(purpose--fix-neotree-1)))



;;; `org-no-popups' suppresses `display-buffer-alist', so we should suppress
;;; purpose-mode as well. However, since it's a macro and evaluated during
;;; byte-compilation, we can't use advice for it. Instead, we wrap functions
;;; that use the macro.
;;; known functions: `org-get-location', `org-switch-to-buffer-other-window'
(defun purpose--fix-org-no-popups-1 ()
  "Make Purpose inactive during some functions that use `org-no-popups'.
Don't call this function before `org' is loaded."
  (define-purpose-compatible-advice 'org-switch-to-buffer-other-window
      :around purpose--fix-org-switch-to-buffer-other-window
      (&rest args)
      "Make Purpose inactive during `org-switch-to-buffer-other-window'."
    ;; new style advice
    ((without-purpose (apply oldfun args)))
    ;; old style advice
    ((without-purpose ad-do-it)))
  (define-purpose-compatible-advice 'org-get-location
      :around purpose--fix-org-get-location
      (&rest args)
      "Make Purpose inactive during `org-get-location'."
    ;; new style advice
    ((without-purpose (apply oldfun args)))
    ;; old style advice
    ((without-purpose ad-do-it)))
  (purpose-advice-add 'org-switch-to-buffer-other-window
                      :around 'purpose--fix-org-switch-to-buffer-other-window)
  (purpose-advice-add 'org-get-location
                      :around 'purpose--fix-org-get-location))

(defun purpose--fix-org-no-popups ()
  "Call `purpose--fix-org-no-popups-1' after `org' is loaded."
  (eval-after-load 'org
    '(purpose--fix-org-no-popups-1)))



;;; popwin uses `switch-to-buffer' when it replicates the window tree, so
;;; Purpose has to be deactivated during that time. this affects guide-key too
(defun purpose--fix-popwin-1 ()
  "Make Purpose inactive during `popwin:replicate-window-config'.
Don't call this function before `popwin' is loaded."
  (define-purpose-compatible-advice 'popwin:replicate-window-config
      :around purpose--fix-popwin-replicate
      (&rest args)
      "Make Purpose inactive during `popwin:replicate-window-config'."
    ;; new style advice
    ((without-purpose (apply oldfun args)))
    ;; old style advice
    ((without-purpose ad-do-it)))
  (purpose-advice-add 'popwin:replicate-window-config
                      :around 'purpose--fix-popwin-replicate))

(defun purpose--fix-popwin ()
  "Call `purpose--fix-popwin-1' after `popwin' is loaded."
  (eval-after-load 'popwin
    '(purpose--fix-popwin-1)))



;;; Use a seperate purpose for guide-key window (not 'general)
(defun purpose--fix-guide-key ()
  "Use a seperate purpose for guide-key window."
  (eval-after-load 'guide-key
    '(purpose-set-extension-configuration
      :guide-key
      (purpose-conf
       "guide-key"
       :name-purposes `((,guide-key/guide-buffer-name . guide-key))))))



;;; Use a seperate purpose for which-key window (not 'general), don't interfere
;;; with how which-key opens a window/frame
(defun purpose--fix-which-key ()
  "Don't interfere with which-key, and use a seperate which-key purpose."
  (eval-after-load 'which-key
    '(progn
       (add-to-list 'purpose-action-function-ignore-buffer-names (regexp-quote which-key-buffer-name))
       (purpose-set-extension-configuration
        :which-key
        (purpose-conf
         "which-key"
         :name-purposes `((,which-key-buffer-name . which-key)))))))



;;; Let magit-popup use its own way of opening a help window (see https://github.com/syl20bnr/spacemacs/issues/9570)
(defun purpose--fix-magit-popup ()
  "Let magit-popup display help windows the way it wants."
  (eval-after-load 'magit-popup
    '(progn
       (define-purpose-compatible-advice 'magit-popup-describe-function
           :around purpose--fix-magit-popup-help
           (&rest args)
           "Make Purpose inactive during `magit-popup-describe-function'."
         ;; new style advice
         ((without-purpose (apply oldfun args)))
         ;; old style advice
         ((without-purpose ad-do-it)))
       (define-purpose-compatible-advice 'magit-popup-manpage
           :around purpose--fix-magit-popup-help
           (&rest args)
           "Make Purpose inactive during `magit-popup-manpage'."
         ;; new style advice
         ((without-purpose (apply oldfun args)))
         ;; old style advice
         ((without-purpose ad-do-it)))
       (purpose-advice-add 'magit-popup-describe-function
                           :around 'purpose--fix-magit-popup-help)
       (purpose-advice-add 'magit-popup-manpage
                           :around 'purpose--fix-magit-popup-help)
       )))

;;; install fixes

(defun purpose-fix-install (&rest exclude)
  "Install fixes for integrating Purpose with other features.
EXCLUDE is a list of integrations to skip.  Known members of EXCLUDE
are:
- 'compilation-next-error-function : don't integrate with
  `compilation-next-error-function'.
- 'lv : don't integrate with lv (hydra)
- 'helm : don't integrate with helm
- 'neotree : don't integrate with neotree
- 'org : don't integrate with org
- 'popwin : don't integrate with popwin
- 'guide-key : don't integrate with guide-key
- 'which-key : don't integrate with which-key"
  (interactive)
  (unless (member 'compilation-next-error-function exclude)
    (purpose-advice-add 'compilation-next-error-function
                        :around #'purpose--fix-compilation-next-error))
  (unless (member 'lv exclude)
    (purpose--fix-hydra-lv))
  (unless (member 'helm exclude)
    (purpose--fix-helm))
  (unless (member 'neotree exclude)
    (purpose--fix-neotree))
  (unless (member 'org exclude)
    (purpose--fix-org-no-popups))
  (unless (member 'popwin exclude)
    (purpose--fix-popwin))
  (unless (member 'guide-key exclude)
    (purpose--fix-guide-key))
  (unless (member 'which-key exclude)
    (purpose--fix-which-key))
  (unless (member 'magit-popup exclude)
    (purpose--fix-magit-popup)))

(provide 'window-purpose-fixes)
;;; window-purpose-fixes.el ends here
