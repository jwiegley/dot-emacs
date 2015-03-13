;;; muse-ikiwiki.el --- integrate with Ikiwiki

;; Copyright (C) 2008, 2009, 2010  Free Software Foundation, Inc.

;; This file is part of Emacs Muse.  It is not part of GNU Emacs.

;; Emacs Muse is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published
;; by the Free Software Foundation; either version 3, or (at your
;; option) any later version.

;; Emacs Muse is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with Emacs Muse; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; Contributors:

;;; Code:

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Muse Ikiwiki Integration
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'muse)
(require 'muse-html)
(require 'muse-ipc)
(require 'muse-publish)

(eval-when-compile
  (require 'muse-colors))

(defgroup muse-ikiwiki nil
  "Options controlling the behavior of Muse integration with Ikiwiki."
  :group 'muse-publish)

(defcustom muse-ikiwiki-header ""
  "Header used for publishing Ikiwiki output files.
This may be text or a filename."
  :type 'string
  :group 'muse-ikiwiki)

(defcustom muse-ikiwiki-footer ""
  "Footer used for publishing Ikiwiki output files.
This may be text or a filename."
  :type 'string
  :group 'muse-ikiwiki)

(defcustom muse-ikiwiki-markup-regexps
  `(;; Ikiwiki directives
    (1350 ,(concat "\\(\\\\?\\)\\[\\[!""\\(?:-\\|\\w\\)+"
                   "\\([" muse-regexp-blank "\n]+"
                   "\\(?:\\(?:\\(?:-\\|\\w\\)+=\\)?"
                   "\\(?:\"\"\".*?\"\"\"\\|\"[^\"]+\""
                   "\\|[^]" muse-regexp-blank "\n]+\\)"
                   "[" muse-regexp-blank "\n]*\\)*\\)?\\]\\]")
          0 muse-ikiwiki-markup-directive))
  "List of markup rules for publishing Ikiwiki markup on Muse pages.
For more on the structure of this list, see `muse-publish-markup-regexps'."
  :type '(repeat (choice
                  (list :tag "Markup rule"
                        integer
                        (choice regexp symbol)
                        integer
                        (choice string function symbol))
                  function))
  :group 'muse-ikiwiki)

;;; Publishing

(defun muse-ikiwiki-markup-directive ()
  "Handle publishing of an Ikiwiki directive."
  (unless (get-text-property (match-beginning 0) 'read-only)
    (add-text-properties (match-beginning 0) (match-end 0)
                         '(muse-no-paragraph t))
    (muse-publish-mark-read-only (match-beginning 0) (match-end 0))))

(defun muse-ikiwiki-publish-buffer (name title &optional style)
  "Publish a buffer for Ikiwki.
The name of the corresponding file is NAME.
The name of the style is given by STYLE.  It defaults to \"ikiwiki\"."
  (unless style (setq style "ikiwiki"))
  (unless title (setq title (muse-page-name name)))
  (let ((muse-batch-publishing-p t)
        (muse-publishing-current-file name)
        (muse-publishing-current-output-path name)
        (muse-publishing-current-style style)
        (font-lock-verbose nil)
        (vc-handled-backends nil)) ; don't activate VC when publishing files
    (run-hooks 'muse-before-publish-hook)
    (let ((muse-inhibit-before-publish-hook t))
      (muse-publish-markup-buffer title style))))

(defun muse-ikiwiki-publish-file (file name &optional style)
  "Publish a single file for Ikiwiki.
The name of the real file is NAME, and the name of the temporary
file containing the content is FILE.
The name of the style is given by STYLE.  It defaults to \"ikiwiki\"."
  (if (not (stringp file))
      (message "Error: No file given to publish")
    (unless style
      (setq style "ikiwiki"))
    (let ((output-path file)
          (target file)
          (vc-handled-backends nil) ; don't activate VC when publishing files
          auto-mode-alist
          muse-current-output-style)
      (setq auto-mode-alist
            (delete (cons (concat "\\." muse-file-extension "\\'")
                          'muse-mode-choose-mode)
                    auto-mode-alist))
      (setq muse-current-output-style (list :base style :path file))
      (muse-with-temp-buffer
        (muse-insert-file-contents file)
        (muse-ikiwiki-publish-buffer name nil style)
        (when (muse-write-file output-path t)
          (muse-style-run-hooks :final style file output-path target))))))

(defun muse-ikiwiki-start-server (port)
  "Start Muse IPC server, initializing with the client on PORT."
  (muse-ipc-start "foo" #'muse-ikiwiki-publish-buffer port))

;;; Colors

(defface muse-ikiwiki-directive
  '((((class color) (background light))
     (:foreground "dark green"))
    (((class color) (background dark))
     (:foreground "green")))
  "Face for Ikiwiki directives."
  :group 'muse-ikiwiki)

(defun muse-colors-ikiwiki-directive ()
  "Color ikiwiki directives."
  (let ((start (match-beginning 0)))
    (unless (or (eq (get-text-property start 'invisible) 'muse)
                (get-text-property start 'muse-comment)
                (get-text-property start 'muse-directive))
      ;; beginning of line or space or symbol
      (save-excursion
        (and
         (catch 'valid
           (while t
             (skip-chars-forward "^\"]" muse-colors-region-end)
             (cond ((eq (point) (point-max))
                    (throw 'valid nil))
                   ((> (point) muse-colors-region-end)
                    (throw 'valid nil))
                   ((eq (char-after) ?\")
                    (if (and (< (1+ (point)) muse-colors-region-end)
                             (eq (char-after (1+ (point))) ?\"))
                        (if (and (< (+ 2 (point)) muse-colors-region-end)
                                 (eq (char-after (+ 2 (point))) ?\"))
                            ;; triple-quote
                            (progn
                              (forward-char 3)
                              (or (and (looking-at "\"\"\"")
                                       (goto-char (match-end 0)))
                                  (re-search-forward
                                   "\"\"\"" muse-colors-region-end t)
                                  (throw 'valid nil)))
                          ;; empty quotes (""), which are invalid
                          (throw 'valid nil))
                      ;; quote with content
                      (forward-char 1)
                      (skip-chars-forward "^\"" muse-colors-region-end)
                      (when (eq (char-after) ?\")
                        (forward-char 1))))
                   ((eq (char-after) ?\])
                    (forward-char 1)
                    (when (and (< (point) muse-colors-region-end)
                               (eq (char-after (point)) ?\]))
                      (forward-char 1)
                      (throw 'valid t)))
                   (t (throw 'valid nil)))))
         ;; found a valid directive
         (let ((end (point)))
           ;; remove flyspell overlays
           (when (fboundp 'flyspell-unhighlight-at)
             (let ((cur start))
               (while (> end cur)
                 (flyspell-unhighlight-at cur)
                 (setq cur (1+ cur)))))
           (add-text-properties start end
                                '(face muse-ikiwiki-directive
                                  muse-directive t muse-no-flyspell t))
           (when (progn
                   (goto-char start)
                   (skip-chars-forward "^\n" end)
                   (and (eq (char-after) ?\n)
                        (not (= (point) end))))
             (add-text-properties start end
                                  '(font-lock-multiline t)))))))))

(defun muse-ikiwiki-insinuate-colors ()
  (add-to-list 'muse-colors-markup
               '("\\[\\[!" ?\[ muse-colors-ikiwiki-directive)
               nil))

(eval-after-load "muse-colors" '(muse-ikiwiki-insinuate-colors))

;; Styles
(muse-derive-style "ikiwiki" "xhtml"
                   :header  'muse-ikiwiki-header
                   :footer  'muse-ikiwiki-footer
                   :regexps 'muse-ikiwiki-markup-regexps)

(provide 'muse-ikiwiki)

;;; muse-ikiwiki.el ends here
