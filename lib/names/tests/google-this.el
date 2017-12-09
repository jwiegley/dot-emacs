;;; google-this.el --- A set of functions and bindings to google under point.

;; Copyright (C) 2012-2013 Artur Malabarba <bruce.connor.am@gmail.com>

;; Author: Artur Malabarba <bruce.connor.am@gmail.com>
;; URL: http://github.com/Bruce-Connor/emacs-google-this
;; Version: 1.9
;; Package-Requires: ((emacs "24.1") (names "0.5"))
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

;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;

;;; Change Log:
;; 1.9   - 2014/09/02 - Renamed A LOT of functions to be namespaced correctly.
;; 1.10  - 2014/09/02 - Fix 24.3 compatibility.
;; 1.9   - 2014/06/19 - Customizable URL.
;; 1.8   - 2013/10/31 - Customizable mode-line indicator (credit https://github.com/mgalgs)
;; 1.7.1 - 2013/09/17 - google-this-parse-and-search-string returns what browse-url returns.
;; 1.7   - 2013/09/08 - Removed some obsolete aliases.
;; 1.7   - 2013/09/08 - Implemented google-lucky-and-insert-url, with keybinding.
;; 1.7   - 2013/09/08 - Implemented google-lucky, with keybinding.
;; 1.6   - 2013/08/22 - Activated google-instant, so you can navigate straight for the keyboard
;; 1.5   - 2013/07/18 - added keybinding for google region.
;; 1.5   - 2013/07/18 - Fixed cpp-reference.
;; 1.4   - 2013/06/03 - Added parent groups.
;; 1.4   - 2013/06/03 - Renamed some functions and variables. Is backwards incompatible if you were using functions you shouldn't be.
;; 1.4   - 2013/06/03 - Fixed quoting.
;; 1.3   - 2013/05/31 - Merged fix for google-forecast. Thanks to ptrv.
;; 1.3   - 2013/05/31 - More robust google-translate command.
;; 1.2.1 - 2013/04/26 - Created an error parser for the google-error function.
;; pre   - 2013/02/27 - It works with c-like errors and is extendable to other types of errors using the varible `google-error-regexp'.
;; 1.2.1 - 2013/04/26 - autoloaded any functions that the user might want to call directly.
;; 1.2   - 2013/04/21 - Fixed docs.
;; pre   - 2013/05/04 - Changed the keybinding to be standards compliant.
;; pre   - 2013/03/03 - Fixed problem with backslash.
;; pre   - 2013/02/27 - Added support for google-translate and google-maps packages.
;; pre   - 2013/02/27 - And added `google-forecast' function.
;; pre   - 2013/02/27 - And added `google-location-suffix' so we're not constrained to google.com anymore.
;;; Code:

(require 'url)
(require 'names)
(eval-when-compile
  (progn
    (require 'compile)
    (require 'simple)
    (declare-function google-maps "google-maps")))

(defgroup google-this '()
  "Customization group for `google-this-mode'."
  :link '(url-link "http://github.com/Bruce-Connor/emacs-google-this")
  :group 'convenience
  :group 'comm)

(define-namespace google-this-

(defconst version "1.9"
  "Version string of the `google-this' package.")
(defconst version-int 10
  "Integer version number of the `google-this' package (for comparing versions).")
(defcustom wrap-in-quotes nil
  "If not nil, searches are wrapped in double quotes.

If a prefix argument is given to any of the functions, the
opposite happens."
  :type 'boolean
  :group 'google-this)

(defcustom suspend-after-search nil
  "Whether Emacs should be minimized after a search is launched (calls `suspend-frame')."
  :type 'boolean
  :group 'google-this)

(defvar mode-submap)
(define-prefix-command 'google-this-mode-submap)
(define-key mode-submap [return] #'search)
(define-key mode-submap " " #'region)
(define-key mode-submap "t" #'google-this)
(define-key mode-submap "g" #'lucky-search)
(define-key mode-submap "i" #'lucky-and-insert-url)
(define-key mode-submap "w" #'word)
(define-key mode-submap "s" #'symbol)
(define-key mode-submap "l" #'line)
(define-key mode-submap "e" #'error)
(define-key mode-submap "f" #'forecast)
(define-key mode-submap "r" #'cpp-reference)
(when (fboundp #'google-maps)
  (define-key mode-submap "m" #'google-maps))
;; "c" is for "convert language" :-P
(define-key mode-submap "c" #'translate-query-or-region)

(defun translate-query-or-region ()
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

(defcustom base-url "https://www.google."
  "The base url to use in google searches.

This will be appended with `google-this-location-suffix', so you
shouldn't include the final \"com\" here."
  :type 'string
  :group 'google-this)

(defcustom location-suffix "com"
  "The url suffix associated with your location (com, co.uk, fr, etc)."
  :type 'string
  :group 'google-this)

(defun url () "URL for google searches."
       (concat base-url location-suffix "/search?ion=1&q=%s"))

(defcustom error-regexp '(("^[^:]*:[0-9 ]*:\\([0-9 ]*:\\)? *" ""))
  "List of (REGEXP REPLACEMENT) pairs to parse error strings."
  :type '(repeat (list regexp string))
  :group 'google-this)

(defun pick-term (prefix)
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

:autoload
(defun search (prefix &optional search-string)
  "Write and do a google search.
Interactively PREFIX determines quoting.
Non-interactively SEARCH-STRING is the string to search."
  (interactive "P")
  (let* ((term (pick-term prefix)))
    (if (stringp term)
        (parse-and-search-string term prefix search-string)
      (message "[google-this-string] Empty query."))))

(defun lucky-search-url ()
  "Return the url for a feeling-lucky google search."
  (format "%s%s/search?q=%%s&btnI" base-url location-suffix))

(defalias 'google-this--do-lucky-search
  (if (version< emacs-version "24")
      '(lambda (term callback)
         "Build the URL using TERM, perform the `url-retrieve' and call CALLBACK if we get redirected."
         (url-retrieve (format (google-this-lucky-search-url) (url-hexify-string term))
                       (eval `(lambda (status)
                                (if status
                                    (if (eq :redirect (car status))
                                        (progn (message "Received URL: %s" (cadr status))
                                               (funcall ,callback (cadr status)))
                                      (message "Unkown response: %S" status))
                                  (message "Search returned no results."))))
                       nil))
    '(lambda (term callback)
       "Build the URL using TERM, perform the `url-retrieve' and call CALLBACK if we get redirected."
       (url-retrieve (format (google-this-lucky-search-url) (url-hexify-string term))
                     (eval `(lambda (status)
                              (if status
                                  (if (eq :redirect (car status))
                                      (progn (message "Received URL: %s" (cadr status))
                                             (funcall ,callback (cadr status)))
                                    (message "Unkown response: %S" status))
                                (message "Search returned no results."))))
                     nil t t))))

(defvar -last-url nil "Last url that was fetched by `google-this-lucky-and-insert-url'.")

:autoload
(defun lucky-and-insert-url (term &optional insert)
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
    (when nint (setq -last-url nil))
    (when (eq term 'needsQuerying)
      (setq term (read-string "Lucky Term: " (buffer-substring-no-properties l r))))
    (unless (stringp term) (error "TERM must be a string!"))
    (-do-lucky-search term
                      (eval `(lambda (url)
                               (unless url (error "Received nil url"))
                               (with-current-buffer ,b
                                 (save-excursion
                                   (if ,nint (goto-char ,p)
                                     (kill-region ,l ,r)
                                     (goto-char ,l))
                                   (when ,insert (insert url))))
                               (setq google-this--last-url url))))
    (unless nint (deactivate-mark))
    (when nint
      (while (null -last-url) (sleep-for 0 10))
      -last-url)))

:autoload
(defun lucky-search (prefix)
  "Exactly like `google-this-search', but use the \"I'm feeling lucky\" option.
PREFIX determines quoting."
  (interactive "P")
  (search prefix (lucky-search-url)))

(defun -maybe-wrap-in-quotes (text flip)
  "Wrap TEXT in quotes.
Depends on the value of FLIP and `google-this-wrap-in-quotes'."
  (if (if flip (not wrap-in-quotes) wrap-in-quotes)
      (format "\"%s\"" text)
    text))

(defun parse-and-search-string (text prefix &optional search-url)
  "Convert illegal characters in TEXT to their %XX versions, and then googles.
PREFIX determines quoting.
SEARCH-URL is usually either the regular or the lucky google
search url.

Don't call this function directly, it could change depending on
version. Use `google-this-string' instead (or any of the other
google-this-\"something\" functions)."
  (let* (;; Create the url
         (query-string (-maybe-wrap-in-quotes text prefix))
         ;; Perform the actual search.
         (browse-result (browse-url (format (or search-url (url))
                                            (url-hexify-string query-string)))))
    ;; Maybe suspend emacs.
    (when suspend-after-search (suspend-frame))
    ;; Return what browse-url returned (very usefull for tests).
    browse-result))

:autoload
(defun string (prefix &optional TEXT NOCONFIRM)
  "Google given TEXT, but ask the user first if NOCONFIRM is nil.
PREFIX determines quoting."
  (unless NOCONFIRM
    (setq TEXT (read-string "Googling: "
                            (if (stringp TEXT) (replace-regexp-in-string "^[[:blank:]]*" "" TEXT)))))
  (if (stringp TEXT)
      (parse-and-search-string TEXT prefix)
    (message "[google-this-string] Empty query.")))

:autoload
(defun line (prefix)
  "Google the current line.
PREFIX determines quoting."
  (interactive "P")
  (let ((Line (buffer-substring (line-beginning-position) (line-end-position))))
    (string prefix Line)))

:autoload
(defun word (prefix)
  "Google the current word.
PREFIX determines quoting."
  (interactive "P")
  (string prefix (thing-at-point 'word) t))

:autoload
(defun symbol (prefix)
  "Google the current symbol.
PREFIX determines quoting."
  (interactive "P")
  (string prefix (thing-at-point 'symbol) t))


:autoload
(defun region (prefix)
  "Google the current region.
PREFIX determines quoting."
  (interactive "P")
  (string
   prefix (buffer-substring-no-properties (region-beginning) (region-end))))

:autoload
(defun google-this (prefix)
  "Decide what the user wants to google (always something under point).

Unlike `google-this-search' (which presents an empty prompt with
\"this\" as the default value), this function inserts the query
in the minibuffer to be edited.
PREFIX determines quoting."
  (interactive "P")
  (cond
   ((region-active-p) (region prefix))
   ((thing-at-point 'symbol) (string prefix (thing-at-point 'symbol)))
   ((thing-at-point 'word) (string prefix (thing-at-point 'word)))
   (t (line prefix))))

:autoload
(defun error (prefix)
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
      (string prefix
              (clean-error-string
               (buffer-substring (line-beginning-position) (line-end-position)))))))


:autoload
(defun clean-error-string (s)
  "Parse error string S and turn it into googleable strings.

Removes unhelpful details like file names and line numbers from
simple error strings (such as c-like erros).

Uses replacements in `google-this-error-regexp' and stops at the first match."
  (interactive)
  (let (out)
    (catch 'result
      (dolist (cur error-regexp out)
        (when (string-match (car cur) s)
          (setq out (replace-regexp-in-string
                     (car cur) (car (cdr cur)) s))
          (throw 'result out))))))

:autoload
(defun cpp-reference ()
  "Visit the most probable cppreference.com page for this word."
  (interactive)
  (parse-and-search-string
   (concat "site:cppreference.com " (thing-at-point 'symbol))
   nil (lucky-search-url)))

:autoload
(defun forecast (prefix)
  "Search google for \"weather\".
With PREFIX, ask for location."
  (interactive "P")
  (if (not prefix) (parse-and-search-string "weather" nil)
    (parse-and-search-string
     (concat "weather " (read-string "Location: " nil nil "")) nil)))

(defcustom keybind (kbd "C-c /")
  "Keybinding under which `google-this-mode-submap' is assigned.

To change this do something like:
    (setq google-this-keybind (kbd \"C-x g\"))
BEFORE activating the function `google-this-mode' and BEFORE `require'ing the
`google-this' feature."
  :type 'string
  :group 'google-this
  :package-version '(google-this . "1.4"))

(defcustom modeline-indicator " Google"
  "String to display in the modeline when command `google-this-mode' is activated."
  :type 'string
  :group 'google-this
  :package-version '(google-this . "1.8"))

:autoload
(define-minor-mode mode nil nil modeline-indicator
  `((,keybind . ,mode-submap))
  :global t
  :group 'google-this)

;; (setq google-this-keybind (kbd \"C-x g\"))
)

(define-obsolete-variable-alias 'google-error-regexp 'google-this-error-regexp "1.9")
(define-obsolete-variable-alias 'google-location-suffix 'google-this-location-suffix "1.9")
(define-obsolete-variable-alias 'google-base-url 'google-this-base-url "1.9")
(define-obsolete-variable-alias 'google-wrap-in-quotes 'google-this-wrap-in-quotes "1.9")

;;;###autoload
(dolist (it '("-do-lucky-search" "lucky-search-url" "string" "pick-term"
              "url" "translate-query-or-region" "cpp-reference" "forecast"
              "error" "line" "symbol" "word" "lucky-and-insert-url"
              "lucky-search" "region" "search"))
  (define-obsolete-function-alias
    (intern (concat "google-" it))
    (intern (concat "google-this-" it))
    "1.9"))

(provide 'google-this)

;;; google-this.el ends here
