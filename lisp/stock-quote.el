;;; stock-quote --- quickly grab a stock quote from the net

;; Copyright (C) 1999, 2000, 2001 John Wiegley

;; Author: John Wiegley <johnw@gnu.org>
;; Created:  3 Dec 1999
;; Version: 2.3
;; Keywords: data
;; X-URL: http://www.gci-net.com/users/j/johnw/emacs.html

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

;; A simple mode for snarfing stock quotes.
;;
;; To obtain a quote, type `M-x stock-quote', and enter the ticker
;; symbol.
;;
;; To watch a quote in the modeline, configure the variable
;; `stock-quote-in-modeline' with the name of the ticker symbol to
;; watch.
;;
;; To change the way that quotes are obtained, write a new function
;; and add-hook it to `stock-quote-data-functions'.  It will be passed
;; the ticker name, and should return the price if it can.  The
;; default method uses the Money Quick Quotes web page, and the W3
;; package.
;;
;; If you want Emacs to do certain things when certain conditions are
;; met, you should configure the triggers and actions variables.  Only
;; a few predefined triggers are given, but the mechanism is
;; extensible.  Just add your trigger function to
;; `stock-quote-trigger-functions'.  It will be given the ticker name
;; and price (as a floating point value).  If the function returns a
;; string, representing the reason why the trigger is firing, then the
;; trigger is considered as having fired, and an action will be
;; performed.
;;
;; Actions are functions that have been add-hook'd to
;; `stock-quote-trigger-functions'.  If the first action to return a
;; non-nil value is chosen.  They can do anything, and will be passed
;; the ticker name, the price, and the reason returned by the trigger
;; function.
;;
;; And always remember: profit isn't real until its real.

;;; History:
;;
;; Fri Dec 15 2000 Marcus Harnisch <marcus.harnisch@gmx.net>
;;
;; * Added code to make stock-quote.el work with XEmacs

;;; Code:

(defconst stock-quote-version "2.3"
  "This version of stock-quote.")

(defgroup stock-quote nil
  "quickly grab a stock quote from the Net."
  :group 'applications)

;;; User Variables:

(defcustom stock-quote-data-functions '(stock-quote-MoneyQuickQuotes)
  "*A list of functions used to obtain stock quote prices.
Each function is passed the ticker name as a string.
The first function to return a price (as a floating point value) is
used."
  :type 'hook
  :group 'stock-quote)

(defcustom stock-quote-trigger-functions nil
  "*A list of functions to call to determine if a trigger fires.
Each function is passed the ticker name as a string, and the stock
price as a floating point value.
The first function to return a string, representing the reason for the
trigger, is called."
  :type 'hook
  :group 'stock-quote)

(defcustom stock-quote-action-functions '(stock-quote-message-box)
  "*A list of functions to call when a trigger fires.
Each function is passed the ticker name, the stock price as a floating
point value, and the return value from the trigger.
If any function returns a non-nil value, none else will be called."
  :type 'hook
  :group 'stock-quote)

(defcustom stock-quote-interval 300
  "*Number of seconds to wait between stock quote updates."
  :type 'integer
  :group 'stock-quote)

;;; Internal Variables:

(defvar stock-quote-last-price nil
  "The last stock quote value.")

(defvar stock-quote-mode-string ""
  "A string representing the last stock quote value.")

(defvar stock-quote-timer nil)

;;; User Functions:

;;;###autoload
(defun stock-quote (ticker)
  (interactive "sTicker: ")
  (setq stock-quote-last-price
	(run-hook-with-args-until-success
	 'stock-quote-data-functions (upcase ticker)))
  (message (format "%s: %.2f" ticker stock-quote-last-price)))

;;; Internal Functions:

(defun stock-quote-MoneyQuickQuotes (ticker)
  "Download a stock price using the Money Quick Quotes web page."
  (require 'w3)
  (require 'url)
  (with-temp-buffer
    (let (url-show-status)
      (url-insert-file-contents
       (concat "http://quote.pathfinder.com/money/quote/qc?symbols="
	       ticker))
      (set-buffer-modified-p nil))
    (goto-char (point-min))
    (if (and (re-search-forward "<b>" nil t)
	     (re-search-forward "<b>" nil t)
	     (re-search-forward "<b>" nil t)
	     (looking-at "-?[0-9.]+"))
	(string-to-number (match-string 0)))))

(custom-add-option 'stock-quote-data-functions
		   'stock-quote-MoneyQuickQuotes)

(defun stock-quote-QuickenCom (ticker)
  "Download a stock price using the www.quicken.com web site."
  (require 'w3)
  (require 'url)
  (with-temp-buffer
    (let (url-show-status)
      (url-insert-file-contents
       (concat "http://www.quicken.com/investments/quotes/?symbol="
	       ticker "&B1=Go"))
      (set-buffer-modified-p nil))
    (goto-char (point-min))
    (when (re-search-forward "Last Trade" nil t)
      (forward-line 2)
      (if (re-search-forward
	   (concat "^\\s-*\\([0-9]+\\)"
		   "\\(\\s-*<FONT SIZE=[0-9]+>\\([0-9]+\\)"
		   "/\\([0-9]+\\)\\)?") nil t)
	  (let ((integer (string-to-number (match-string 1)))
		(numerator (if (match-string 3)
			       (string-to-number (match-string 3))))
		(divisor (if (match-string 4)
			     (string-to-number (match-string 4)))))
	    (if numerator
		(setq numerator (/ (float numerator) divisor)
		      integer (+ (float integer) numerator)))
	    (float integer))))))

(custom-add-option 'stock-quote-data-functions
		   'stock-quote-QuickenCom)

(defun stock-quote-update ()
  "Update the last know stock price, and check triggers."
  (when (setq stock-quote-last-price
	      (run-hook-with-args-until-success
	       'stock-quote-data-functions stock-quote-in-modeline))
    (setq stock-quote-mode-string
	  (format " {%.2f}" stock-quote-last-price))
    (force-mode-line-update)
    (let ((reason (run-hook-with-args-until-success
		   'stock-quote-trigger-functions
		   stock-quote-in-modeline stock-quote-last-price)))
      (if reason
	  (run-hook-with-args-until-success
	   'stock-quote-action-functions stock-quote-in-modeline
	   stock-quote-last-price reason)))))

(defcustom stock-quote-floor-trigger 10
  "*Value of the floor trigger (see `stock-quote-trigger-functions') ."
  :type 'number
  :group 'stock-quote)

(defun stock-quote-floor-trigger (ticker price)
  "Fire a trigger if the stock goes below `stock-quote-floor-trigger'."
  (if (< price stock-quote-floor-trigger)
      (format "%s has dropped to %.2f" ticker price)))

(custom-add-option 'stock-quote-trigger-functions
		   'stock-quote-floor-trigger)

(defcustom stock-quote-ceiling-trigger 100
  "*Value of the ceiling trigger (see `stock-quote-trigger-functions') ."
  :type 'number
  :group 'stock-quote)

(defun stock-quote-ceiling-trigger (ticker price)
  "Fire a trigger if the stock rises above `stock-quote-ceiling-trigger'."
  (if (> price stock-quote-ceiling-trigger)
      (format "%s has risen to %.2f" ticker price)))

(custom-add-option 'stock-quote-trigger-functions
		   'stock-quote-ceiling-trigger)

(defcustom stock-quote-move-trigger 10
  "*Value of the move trigger (see `stock-quote-trigger-functions') ."
  :type 'number
  :group 'stock-quote)

(defun stock-quote-move-trigger (ticker price)
  "Fire a trigger on changes more than `stock-quote-move-trigger' percent."
  (let ((diff (and stock-quote-last-price
		   (* (/ stock-quote-last-price price) 100))))
    (if (> (abs diff) stock-quote-ceiling-trigger)
	(format "%s has moved by %.2f%%" ticker diff))))

(custom-add-option 'stock-quote-trigger-functions
		   'stock-quote-move-trigger)

(defun stock-quote-message-box (ticker price reason)
  "If a triggers fires, pop up a message box."
  (ignore (message-box "Stock trigger: %s" reason)))

(custom-add-option 'stock-quote-action-functions
		   'stock-quote-message-box)

(defvar stock-quote-running-xemacs
  (string-match "XEmacs" emacs-version)
  "Non-nil means that we're running XEmacs here.")

(defun stock-quote-cancel-timer (timer)
  "Wrapper for different timer functions in GNU Emacs and XEmacs.
\`stock-quote-cancel-timer' calls either \`cancel-timer' (GNU Emacs) or
\`disable-timeout' (XEmacs)"
  (if stock-quote-running-xemacs
      (disable-timeout timer)
    (cancel-timer timer)))

(defun stock-quote-run-when-idle (func)
  "Run FUNC if emacs is idle for a second. This is a wrapper for the
different i(dle-)timer functions of GNU Emacs and
XEmacs. \`stock-quote-run-when-idle' calls either \`run-with-idle-timer'
(GNU Emacs) or \`start-itimer' (XEmacs)."
  (if stock-quote-running-xemacs
      (start-itimer "stock-quote-itimer" func 1 nil t)
    (run-with-idle-timer 1 nil func)))

(defun stock-quote-run-repeatedly (func interval)
  "Run FUNC repeatedly in intervals of INTERVAL seconds. This is a
wrapper function for different timer functions in GNU Emacs and
XEmacs. \`stock-quote-run-repeatedly' calls either \`run-at-time' (GNU
Emacs) or \`add-timeout' (XEmacs)."
  (if stock-quote-running-xemacs
      (add-timeout 0.1 `(lambda (dummy) (,func)) 'nil interval)
    (run-at-time nil interval func)))

(defun stock-quote-in-modeline (ticker)
  "Set the price of TICKER to display in the modeline.
If TICKER is nil, disable modeline display."
  (setq stock-quote-in-modeline ticker)
  (if ticker
      (stock-quote-run-when-idle
       (function
	(lambda ()
	  (unless (memq 'stock-quote-mode-string global-mode-string)
	    (if global-mode-string
		(nconc global-mode-string '(stock-quote-mode-string))
	      (setq global-mode-string '(stock-quote-mode-string))))
	  (setq stock-quote-timer
		(stock-quote-run-repeatedly 'stock-quote-update
					    stock-quote-interval))
	  (force-mode-line-update))))
    (setq global-mode-string
	  (delq 'stock-quote-mode-string global-mode-string))
    (when stock-quote-timer
      (stock-quote-cancel-timer stock-qoute-timer)
      (setq stock-quote-timer nil)))
  ticker)

(defcustom stock-quote-in-modeline nil
  "*If a string, display that stock price in the modeline."
  :set (lambda (symbol value)
	 (stock-quote-in-modeline value))
  :type '(choice string (const :tag "None" nil))
  :require 'stock-quote
  :group 'stock-quote)

(provide 'stock-quote)

;;; stock-quote.el ends here
