;;; helm-hoogle.el --- Use helm to navigate query results from Hoogle

;; Copyright (C) 2013 John Wiegley

;; Author: John Wiegley <jwiegley@gmail.com>
;; Created: 13 Jan 2013
;; Version: 1.0
;; Keywords: haskell programming hoogle
;; X-URL: https://github.com/jwiegley/haskell-config
;; Package-Requires: ((helm "1.6.2"))

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

;; cabal install hoogle, then run M-x helm-hoogle

(require 'helm)
(eval-when-compile
  (require 'cl))

(defgroup helm-hoogle nil
  "Use helm to navigate query results from Hoogle"
  :group 'helm)

(defvar helm-c-source-hoogle
  '((name . "Hoogle")
    (candidates . helm-c-hoogle-set-candidates)
    (action . (("Lookup Entry" . eww-browse-url)))
    (filtered-candidate-transformer . (lambda (candidates source) candidates))
    (volatile)
    (delayed)))

(defun helm-c-hoogle-set-candidates (&optional request-prefix)
  (let* ((pattern (or (and request-prefix
                           (concat request-prefix
                                   " " helm-pattern))
                      helm-pattern))
         (short-pattern
          (if (string-match "\\`\\([a-zA-Z_][a-zA-Z0-9_]*\\) " pattern)
              (match-string 1 pattern)
            pattern))
         (lim helm-candidate-number-limit)
         (args (append (list "search" "-l")
                       (and lim (list "-n" (int-to-string lim)))
                       (list short-pattern))))
    (let (candidates)
      (with-temp-buffer
        (apply #'call-process "hoogle" nil t nil args)
        (goto-char (point-min))
        (while (not (eobp))
          (if (looking-at "\\(.+?\\) -- \\(.+\\)")
              (push (cons (match-string 1)
                          (match-string-no-properties 2))
                    candidates))
          (forward-line 1)))
      (nreverse candidates))))

;;;###autoload
(defun helm-hoogle ()
  (interactive)
  (helm :sources 'helm-c-source-hoogle
        :input ""
        :prompt "Hoogle: "
        :buffer "*Hoogle search*"))

(provide 'helm-hoogle)

;;; helm-hoogle.el ends here
