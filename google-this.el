;;; google-this.el --- A set of functions and bindings to google under point.

;; Copyright (C) 2012-2013 Artur Malabarba <bruce.connor.am@gmail.com>

;; Author: Artur Malabarba <bruce.connor.am@gmail.com>
;; URL: http://github.com/Malabarba/emacs-google-this
;; Version: 1.10
;; Package-Requires: ((emacs "24.1"))
;; Keywords: convenience hypermedia
;; Prefix: google-this
;; Separator: -

;;; Commentary:

;; google-this is a package that provides a set of functions and
;; keybindings for launching google searches from within Emacs.

;; The main function is `google-this' (bound to C-c / g). It does a
;; google search using the currently selected region, or the
;; expression under point. All functions are bound under "C-c /"
;; prefix, in order to comply with Emacs' standards. If that's a
;; problem see `google-this-keybind'. To view all keybindings type "C-c
;; / C-h".
;;
;; If you don't like this keybind, just reassign the
;; `google-this-mode-submap' variable.
;; My personal preference is "C-x g":
;;
;;        (global-set-key (kbd "C-x g") 'google-this-mode-submap)
;;
;; Or, if you don't want google-this to overwrite the default ("C-c /")
;; key insert the following line BEFORE everything else (even before
;; the `require' command):
;;
;;        (setq google-this-keybind (kbd "C-x g"))
;;

;; To start a blank search, do `google-search' (C-c / RET). If you
;; want more control of what "under point" means for the `google-this'
;; command, there are the `google-word', `google-symbol',
;; `google-line' and `google-region' functions, bound as w, s, l and space,
;; respectively. They all do a search for what's under point.

;; If the `google-wrap-in-quotes' variable is t, than searches are
;; enclosed by double quotes (default is NOT). If a prefix argument is
;; given to any of the functions, invert the effect of
;; `google-wrap-in-quotes'.

;; There is also a `google-error' (C-c / e) function. It checks the
;; current error in the compilation buffer, tries to do some parsing
;; (to remove file name, line number, etc), and googles it. It's still
;; experimental, and has only really been tested with gcc error
;; reports.

;; Finally there's also a google-cpp-reference function (C-c / r).

;;; Instructions:

;; INSTALLATION

;;  Make sure "google-this.el" is in your load path, then place
;;      this code in your .emacs file:
;;		(require 'google-this)
;;              (google-this-mode 1)

;;; License:
;;
;; This file is NOT part of GNU Emacs.
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License
;; as published by the Free Software Foundation; either version 2
;; of the License, or (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;;; Code:

(require 'url)
(eval-when-compile
  (progn
    (require 'compile)
    (require 'simple)))

(defgroup google-this '()
  "Customization group for `google-this-mode'."
  :link '(url-link "http://github.com/Malabarba/emacs-google-this")
  :group 'convenience
  :group 'comm)

(defconst google-this-version "1.10"
  "Version string of the `google-this' package.")
(defcustom google-this-wrap-in-quotes nil
  "If not nil, searches are wrapped in double quotes.

If a prefix argument is given to any of the functions, the
opposite happens."
  :type 'boolean
  :group 'google-this)

(defcustom google-this-suspend-after-search nil
  "Whether Emacs should be minimized after a search is launched (calls `suspend-frame')."
  :type 'boolean
  :group 'google-this)

(defcustom google-this-browse-url-function 'browse-url
  "Function used to browse urls.
Possible values include: `browse-url', `browse-url-generic',
`browse-url-emacs', `eww-browse-url'."
  :type 'function
  :group 'google-this)

(defvar google-this-mode-submap)
(define-prefix-command 'google-this-mode-submap)
(define-key google-this-mode-submap [return] #'google-this-search)
(define-key google-this-mode-submap " " #'google-this-region)
(define-key google-this-mode-submap "t" #'google-this)
(define-key google-this-mode-submap "n" #'google-this-noconfirm)
(define-key google-this-mode-submap "g" #'google-this-lucky-search)
(define-key google-this-mode-submap "i" #'google-this-lucky-and-insert-url)
(define-key google-this-mode-submap "w" #'google-this-word)
(define-key google-this-mode-submap "s" #'google-this-symbol)
(define-key google-this-mode-submap "l" #'google-this-line)
(define-key google-this-mode-submap "e" #'google-this-error)
(define-key google-this-mode-submap "f" #'google-this-forecast)
(define-key google-this-mode-submap "r" #'google-this-cpp-reference)
(define-key google-this-mode-submap "m" #'google-this-maps)
(define-key google-this-mode-submap "a" #'google-this-ray)
(define-key google-this-mode-submap "m" #'google-maps)
;; "c" is for "convert language" :-P
(define-key google-this-mode-submap "c" #'google-this-translate-query-or-region)

(defun google-this-translate-query-or-region ()
  "If region is active `google-translate-at-point', otherwise `google-translate-query-translate'."
  (interactive)
  (unless (require 'google-translate nil t)
    (error "[google-this]: This command requires the 'google-translate' package"))
  (if (region-active-p)
      (if (functionp 'google-translate-at-point)
          (call-interactively 'google-translate-at-point)
        (error "[google-this]: `google-translate-at-point' function not found in `google-translate' package"))
    (if (functionp 'google-translate-query-translate)
        (call-interactively 'google-translate-query-translate)
      (error "[google-this]: `google-translate-query-translate' function not found in `google-translate' package"))))

(defcustom google-this-base-url "https://www.google."
  "The base url to use in google searches.

This will be appended with `google-this-location-suffix', so you
shouldn't include the final \"com\" here."
  :type 'string
  :group 'google-this)

(defcustom google-this-location-suffix "com"
  "The url suffix associated with your location (com, co.uk, fr, etc)."
  :type 'string
  :group 'google-this)

(defun google-this-url ()
  "URL for google searches."
  (concat google-this-base-url google-this-location-suffix "/search?ion=1&q=%s"))

(defcustom google-this-error-regexp '(("^[^:]*:[0-9 ]*:\\([0-9 ]*:\\)? *" ""))
  "List of (REGEXP REPLACEMENT) pairs to parse error strings."
  :type '(repeat (list regexp string))
  :group 'google-this)

(defun google-this-pick-term (prefix)
  "Decide what \"this\" and return it.
PREFIX determines quoting."
  (let* ((term (if (region-active-p)
                   (buffer-substring-no-properties (region-beginning) (region-end))
                 (or (thing-at-point 'symbol)
                     (thing-at-point 'word)
                     (buffer-substring-no-properties (line-beginning-position)
                                                     (line-end-position)))))
         (term (read-string (concat "Googling [" term "]: ") nil nil term)))
    term))

;;;###autoload
(defun google-this-search (prefix &optional search-string)
  "Write and do a google search.
Interactively PREFIX determines quoting.
Non-interactively SEARCH-STRING is the string to search."
  (interactive "P")
  (let* ((term (google-this-pick-term prefix)))
    (if (stringp term)
        (google-this-parse-and-search-string term prefix search-string)
      (message "[google-this-string] Empty query."))))

(defun google-this-lucky-search-url ()
  "Return the url for a feeling-lucky google search."
  (format "%s%s/search?q=%%s&btnI" google-this-base-url google-this-location-suffix))

(defalias 'google-this--do-lucky-search
  (with-no-warnings
    (if (version< emacs-version "24")
        (lambda (term callback)
          "Build the URL using TERM, perform the `url-retrieve' and call CALLBACK if we get redirected."
          (url-retrieve (format (google-this-lucky-search-url) (url-hexify-string term))
                        `(lambda (status)
                           (if status
                               (if (eq :redirect (car status))
                                   (progn (message "Received URL: %s" (cadr status))
                                          (funcall ,callback (cadr status)))
                                 (message "Unkown response: %S" status))
                             (message "Search returned no results.")))
                        nil))
      (lambda (term callback)
        "Build the URL using TERM, perform the `url-retrieve' and call CALLBACK if we get redirected."
        (url-retrieve (format (google-this-lucky-search-url) (url-hexify-string term))
                      `(lambda (status)
                         (if status
                             (if (eq :redirect (car status))
                                 (progn (message "Received URL: %s" (cadr status))
                                        (funcall ,callback (cadr status)))
                               (message "Unkown response: %S" status))
                           (message "Search returned no results.")))
                      nil t t)))))

(defvar google-this--last-url nil "Last url that was fetched by `google-this-lucky-and-insert-url'.")

;;;###autoload
(defun google-this-lucky-and-insert-url (term &optional insert)
  "Fetch the url that would be visited by `google-this-lucky'.

If you just want to do an \"I'm feeling lucky search\", use
`google-this-lucky-search' instead.

Interactively:
* Insert the URL at point,
* Kill the searched term, removing it from the buffer (it is killed, not
  deleted, so it can be easily yanked back if desired).
* Search term defaults to region or line, and always queries for
  confirmation.

Non-Interactively:
* Runs synchronously,
* Search TERM is an argument without confirmation,
* Only insert if INSERT is non-nil, otherwise return."
  (interactive '(needsQuerying t))
  (let ((nint (null (called-interactively-p 'any)))
        (l (if (region-active-p) (region-beginning) (line-beginning-position)))
        (r (if (region-active-p) (region-end) (line-end-position)))
        ;; We get current-buffer and point here, because it's
        ;; conceivable that they could change while waiting for input
        ;; from read-string
        (p (point))
        (b (current-buffer)))
    (when nint (setq google-this--last-url nil))
    (when (eq term 'needsQuerying)
      (setq term (read-string "Lucky Term: " (buffer-substring-no-properties l r))))
    (unless (stringp term) (error "TERM must be a string!"))
    (google-this--do-lucky-search
     term
     `(lambda (url)
        (unless url (error "Received nil url"))
        (with-current-buffer ,b
          (save-excursion
            (if ,nint (goto-char ,p)
              (kill-region ,l ,r)
              (goto-char ,l))
            (when ,insert (insert url))))
        (setq google-this--last-url url)))
    (unless nint (deactivate-mark))
    (when nint
      (while (null google-this--last-url) (sleep-for 0 10))
      google-this--last-url)))

;;;###autoload
(defun google-this-lucky-search (prefix)
  "Exactly like `google-this-search', but use the \"I'm feeling lucky\" option.
PREFIX determines quoting."
  (interactive "P")
  (google-this-search prefix (google-this-lucky-search-url)))

(defun google-this--maybe-wrap-in-quotes (text flip)
  "Wrap TEXT in quotes.
Depends on the value of FLIP and `google-this-wrap-in-quotes'."
  (if (if flip (not google-this-wrap-in-quotes) google-this-wrap-in-quotes)
      (format "\"%s\"" text)
    text))

(defun google-this-parse-and-search-string (text prefix &optional search-url)
  "Convert illegal characters in TEXT to their %XX versions, and then googles.
PREFIX determines quoting.
SEARCH-URL is usually either the regular or the lucky google
search url.

Don't call this function directly, it could change depending on
version. Use `google-this-string' instead (or any of the other
google-this-\"something\" functions)."
  (let* (;; Create the url
         (query-string (google-this--maybe-wrap-in-quotes text prefix))
         ;; Perform the actual search.
         (browse-result (funcall google-this-browse-url-function
                                 (format (or search-url (google-this-url))
                                         (url-hexify-string query-string)))))
    ;; Maybe suspend emacs.
    (when google-this-suspend-after-search (suspend-frame))
    ;; Return what browse-url returned (very usefull for tests).
    browse-result))

;;;###autoload
(defun google-this-string (prefix &optional text noconfirm)
  "Google given TEXT, but ask the user first if NOCONFIRM is nil.
PREFIX determines quoting."
  (unless noconfirm
    (setq text (read-string "Googling: "
                            (if (stringp text) (replace-regexp-in-string "^[[:blank:]]*" "" text)))))
  (if (stringp text)
      (google-this-parse-and-search-string text prefix)
    (message "[google-this-string] Empty query.")))

;;;###autoload
(defun google-this-line (prefix &optional noconfirm)
  "Google the current line.
PREFIX determines quoting.
NOCONFIRM goes without asking for confirmation."
  (interactive "P")
  (let ((line (buffer-substring (line-beginning-position) (line-end-position))))
    (google-this-string prefix line noconfirm)))

;;;###autoload
(defun google-this-ray (prefix &optional noconfirm noregion)
  "Google text between the point and end of the line.
If there is a selected region, googles the region.
PREFIX determines quoting. Negative arguments invert the line segment.
NOCONFIRM goes without asking for confirmation.
NOREGION ignores the region."
  (interactive "P")
  (if (and (region-active-p) (not noregion))
      (google-this-region prefix noconfirm)
    (let (beg end pref (arg (prefix-numeric-value prefix)))
      (if (<= arg -1)
          (progn
            (setq beg (line-beginning-position))
            (setq end (point))
            (setq pref (< arg -1)))
        (setq beg (point))
        (setq end (line-end-position))
        (setq pref prefix))
      (google-this-string pref (buffer-substring beg end) noconfirm))))

;;;###autoload
(defun google-this-word (prefix)
  "Google the current word.
PREFIX determines quoting."
  (interactive "P")
  (google-this-string prefix (thing-at-point 'word) t))

;;;###autoload
(defun google-this-symbol (prefix)
  "Google the current symbol.
PREFIX determines quoting."
  (interactive "P")
  (google-this-string prefix (thing-at-point 'symbol) t))


;;;###autoload
(defun google-this-region (prefix &optional noconfirm)
  "Google the current region.
PREFIX determines quoting.
NOCONFIRM goes without asking for confirmation."
  (interactive "P")
  (google-this-string
   prefix (buffer-substring-no-properties (region-beginning) (region-end))
   noconfirm))

;;;###autoload
(defun google-this (prefix &optional noconfirm)
  "Decide what the user wants to google (always something under point).
Unlike `google-this-search' (which presents an empty prompt with
\"this\" as the default value), this function inserts the query
in the minibuffer to be edited.
PREFIX argument determines quoting.
NOCONFIRM goes without asking for confirmation."
  (interactive "P")
  (cond
   ((region-active-p) (google-this-region prefix noconfirm))
   ((thing-at-point 'symbol) (google-this-string prefix (thing-at-point 'symbol) noconfirm))
   ((thing-at-point 'word) (google-this-string prefix (thing-at-point 'word) noconfirm))
   (t (google-this-line prefix noconfirm))))

;;;###autoload
(defun google-this-noconfirm (prefix)
  "Decide what the user wants to google and go without confirmation.
Exactly like `google-this' or `google-this-search', but don't ask
for confirmation.
PREFIX determines quoting."
  (interactive "P")
  (google-this prefix 'noconfirm))

;;;###autoload
(defun google-this-error (prefix)
  "Google the current error in the compilation buffer.
PREFIX determines quoting."
  (interactive "P")
  (unless (boundp 'compilation-mode-map)
    (error "No compilation active"))
  (require 'compile)
  (require 'simple)
  (save-excursion
    (let ((pt (point))
          (buffer-name (next-error-find-buffer)))
      (unless (compilation-buffer-internal-p)
        (set-buffer buffer-name))
      (google-this-string prefix
                     (google-this-clean-error-string
                      (buffer-substring (line-beginning-position) (line-end-position)))))))


;;;###autoload
(defun google-this-clean-error-string (s)
  "Parse error string S and turn it into googleable strings.

Removes unhelpful details like file names and line numbers from
simple error strings (such as c-like erros).

Uses replacements in `google-this-error-regexp' and stops at the first match."
  (interactive)
  (let (out)
    (catch 'result
      (dolist (cur google-this-error-regexp out)
        (when (string-match (car cur) s)
          (setq out (replace-regexp-in-string
                     (car cur) (car (cdr cur)) s))
          (throw 'result out))))))

;;;###autoload
(defun google-this-cpp-reference ()
  "Visit the most probable cppreference.com page for this word."
  (interactive)
  (google-this-parse-and-search-string
   (concat "site:cppreference.com " (thing-at-point 'symbol))
   nil (google-this-lucky-search-url)))

;;;###autoload
(defun google-this-forecast (prefix)
  "Search google for \"weather\".
With PREFIX, ask for location."
  (interactive "P")
  (if (not prefix) (google-this-parse-and-search-string "weather" nil)
    (google-this-parse-and-search-string
     (concat "weather " (read-string "Location: " nil nil "")) nil)))

(defcustom google-this-keybind (kbd "C-c /")
  "Keybinding under which `google-this-mode-submap' is assigned.

To change this do something like:
    (setq google-this-keybind (kbd \"C-x g\"))
BEFORE activating the function `google-this-mode' and BEFORE `require'ing the
`google-this' feature."
  :type 'string
  :group 'google-this
  :package-version '(google-this . "1.4"))

(defcustom google-this-modeline-indicator " Google"
  "String to display in the modeline when command `google-this-mode' is activated."
  :type 'string
  :group 'google-this
  :package-version '(google-this . "1.8"))

;;;###autoload
(define-minor-mode google-this-mode nil nil google-this-modeline-indicator
  `((,google-this-keybind . ,google-this-mode-submap))
  :global t
  :group 'google-this)
;; (setq google-this-keybind (kbd \"C-x g\"))

(provide 'google-this)

;;; google-this.el ends here
