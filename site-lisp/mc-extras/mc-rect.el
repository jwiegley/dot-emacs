;;; mc-rect.el --- Make multiple-cursors interact with rectangle selection.

;; Copyright (c) 2015 Akinori MUSHA
;;
;; All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above copyright
;;    notice, this list of conditions and the following disclaimer in the
;;    documentation and/or other materials provided with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR AND CONTRIBUTORS ``AS IS'' AND
;; ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
;; IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR OR CONTRIBUTORS BE LIABLE
;; FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
;; OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
;; HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
;; LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
;; OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
;; SUCH DAMAGE.

;; Author: Akinori MUSHA <knu@iDaemons.org>
;; URL: https://github.com/knu/mc-extras.el
;; Created: 22 Jan 2015
;; Package-Requires: ((multiple-cursors "1.2.1"))
;; Keywords: editing, cursors

;;; Commentary:
;;
;; This library contains functions to make multiple-cursors interact
;; with rectangle selection.
;;
;; Suggested key bindings are as follows:
;;
;;   (define-key rectangle-mark-mode-map (kbd "C-. C-,") 'mc/rect-rectangle-to-multiple-cursors)


;;; Code:

(require 'cl)
(require 'multiple-cursors-core)

;;;###autoload
(defun mc/rect-rectangle-to-multiple-cursors (start end)
  "Turn rectangle-mark-mode into multiple-cursors mode, keeping selections."
  (interactive "*r")
  (let* ((current-line (line-beginning-position))
         (reversed (= (current-column)
                      (min
                       (save-excursion
                         (goto-char end)
                         (current-column))
                       (save-excursion
                         (goto-char start)
                         (current-column)))))
         (mark-row `(lambda (startcol endcol)
                     (let ((markcol  ,(if reversed 'endcol 'startcol))
                           (pointcol ,(if reversed 'startcol 'endcol)))
                       (move-to-column markcol)
                       (push-mark (point))
                       (move-to-column pointcol)
                       (setq transient-mark-mode (cons 'only transient-mark-mode))
                       (activate-mark)
                       (setq deactivate-mark nil)))))
    (apply-on-rectangle
     '(lambda (startcol endcol)
        (if (= (point) current-line)
            (funcall mark-row startcol endcol)
          (mc/save-excursion
           (funcall mark-row startcol endcol)
           (mc/create-fake-cursor-at-point))))
     start end)
    (mc/maybe-multiple-cursors-mode)))

(add-to-list 'mc--default-cmds-to-run-once 'mc/rect-rectangle-to-multiple-cursors)

(provide 'mc-rect)

;;; mc-rect.el ends here
