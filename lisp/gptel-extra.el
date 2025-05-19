;;; gptel-extra --- Extra functions for use with gptel

;; Copyright (C) 2025 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created: 28 Feb 2025
;; Version: 1.0
;; Keywords: ai gptel tools
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

(require 'cl-lib)
(eval-when-compile
  (require 'cl))

(require 'gptel)

(gptel-make-tool
 :function (lambda (location unit)
             (url-retrieve-synchronously "api.weather.com/..."
                                         location unit))
 :name "get_weather"
 :description "Get the current weather in a given location"
 :args
 (list
  '(:name "location"
          :type string
          :description "The city and state, e.g. San Francisco, CA")
  '(:name "unit"
          :type string
          :enum ["celsius" "farenheit"]
          :description
          "The unit of temperature, either 'celsius' or 'fahrenheit'"
          :optional t)))

(defun gptel-extra-code-infill ()
  "Fill in code at point based on buffer context.  Note: Sends the whole buffer."
  (let ((lang (gptel--strip-mode-suffix major-mode)))
    `(,(format "You are a %s programmer and assistant in a code buffer in a text editor.

Follow my instructions and generate %s code to be inserted at the cursor.
For context, I will provide you with the code BEFORE and AFTER the cursor.


Generate %s code and only code without any explanations or markdown code fences.  NO markdown.
You may include code comments.

Do not repeat any of the BEFORE or AFTER code." lang lang lang)
      nil
      "What is the code AFTER the cursor?"
      ,(format "AFTER\n```\n%s\n```\n"
               (buffer-substring-no-properties
                (if (use-region-p) (max (point) (region-end)) (point))
                (point-max)))
      "And what is the code BEFORE the cursor?"
      ,(format "BEFORE\n```%s\n%s\n```\n" lang
               (buffer-substring-no-properties
                (point-min)
                (if (use-region-p) (min (point) (region-beginning)) (point))))
      ,(if (use-region-p) "What should I insert at the cursor?"))))

(defun gptel-extra-clear-buffer ()
  (interactive)
  (if nil
      (progn
        (erase-buffer)
        (insert "*Prompt*: "))
    (org-shifttab 0)
    (goto-char (point-max))
    (org-insert-heading)
    (insert "Next topic\n\n*Prompt*: ")))

(provide 'gptel-extra)
