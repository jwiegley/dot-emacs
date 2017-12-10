;;; erc-question --- Ask Google before asking on IRC

;; Copyright (C) 2017 John Wiegley

;; Author: John Wiegley <johnw@newartisans.com>
;; Created: 5 Nov 2017
;; Version: 1.0
;; Keywords: erc irc google
;; X-URL: https://github.com/jwiegley/erc-question

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

;; If you ask a question in ERC ending with ? and hit RET, it will instead
;; submit the query to Google using your browser.  If you return to ERC and
;; hit RET a second time (with no intervening commands), then it submits the
;; question.

;;; Code:

(defgroup erc-question nil
  "Ask Google before asking IRC"
  :group 'erc)

(defvar erc-question--last-asked nil)
(defvar erc-question--mode t)

(defun erc-cmd-ASKON (&rest ignore)
  (setq erc-question--mode t)
  (message "Queries now go to Google; use ?ask to submit the question"))

(defun erc-cmd-ASKOFF (&rest ignore)
  (setq erc-question--mode nil)
  (message "Queries now go to IRC"))

(defun erc-question (input)
  "Ask Google before asking IRC"
  (make-variable-buffer-local 'erc-question--last-asked)
  (when erc-question--mode
    (let ((len (1- (length input))))
      (cond
       ((string= input "?ask")
        (setq str erc-question--last-asked
              erc-question--last-asked nil))
       ((string-match "\\`\\(.+?\\)\\?\\'" input)
        (browse-url (concat "https://www.google.com/search?q="
                            (url-encode-url (match-string 1 input))))
        (setq erc-send-this nil
              erc-question--last-asked input))))))

;; (add-hook 'erc-send-pre-hook 'erc-question)

(defun erc-cmd-G (name &rest ignore)
  (when (re-search-backward
         (concat "<" name "> \\(\\(.\\|\n\\)+\\)\\?") nil t)
    (browse-url
     (concat "https://www.google.com/search?q="
             (url-encode-url
              (subst-char-in-string ?\n ?\  (match-string 1)))))))

(provide 'erc-question)

;;; erc-question.el ends here
