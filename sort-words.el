;;; sort-words.el --- Sort words in a selected region

;; Filename: sort-words.el
;; Description: Sort words in a selected region
;; Author: "Aleksandar Simic" <asimic@gmail.com>
;; License: BSD
;; Created: 2016-09-07
;; Version: 0.0.4
;; Homepage: http://github.org/dotemacs/sort-words.el
;; Keywords: tools

;;; Commentary:
;;
;; Usage: select a region and then
;; M-x sort-words RET

;;; This file is NOT part of GNU Emacs
;;
;; Copyright (c) 2016, Aleksandar Simic
;; All rights reserved.
;;
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions
;; are met:
;; 1. Redistributions of source code must retain the above copyright
;;    notice, this list of conditions and the following disclaimer.
;; 2. Redistributions in binary form must reproduce the above
;;    copyright notice, this list of conditions and the following
;;    disclaimer in the documentation and/or other materials provided
;;    with the distribution.
;;
;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
;; FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE
;; COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
;; INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
;; (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
;; SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
;; HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
;; STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
;; ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED
;; OF THE POSSIBILITY OF SUCH DAMAGE.

;;; Code:

(defun sort-words-in-region (start end)
  "Sort the words in a given region (START and END) and return them as a list."
   (sort (split-string (buffer-substring-no-properties start end)) #'string<))

(defun sort-words-sorted (start end)
  "Sort the words in a given region (START and END) and return them as a string."
  (mapconcat 'identity (sort-words-in-region start end) " "))

;;;###autoload
(defun sort-words (start end)
  "Sort words in region alphabetically.
Then insert them replacing the existing region.
START and END are boundries of the selected region."
  (interactive "r")
  (save-excursion
    (save-restriction
      (narrow-to-region start end)
      (let ((words (sort-words-sorted (point-min) (point-max))))
        (delete-region (point-min) (point-max))
        (goto-char (point-min))
        (insert words)))))

(provide 'sort-words)

;;; sort-words.el ends here
