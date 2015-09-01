;;; helm-google.el --- Emacs Helm Interface for quick Google searches

;; Copyright (C) 2014, Steckerhalter

;; Author: steckerhalter
;; Package-Requires: ((helm "0") (google "0"))
;; URL: https://github.com/steckerhalter/helm-google
;; Keywords: helm google search browse

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

;; Emacs Helm Interface for quick Google searches

;;; Code:

(require 'helm)
(require 'google)

(defgroup helm-google '()
  "Customization group for `helm-google'."
  :link '(url-link "http://github.com/steckerhalter/helm-google")
  :group 'convenience
  :group 'comm)

(defcustom helm-google-search-function 'helm-google-html-search
  "The function that should be used to get the search results.
Available functions are currently `helm-google-api-search' and
`helm-google-html-search'."
  :type 'symbol
  :group 'helm-google)

(defcustom helm-google-tld "com"
  "The TLD of the google url to be used (com, de, fr, co.uk etc.)."
  :type 'string
  :group 'helm-google)

(defcustom helm-google-use-regexp-parsing nil
  "Force use of regexp html parsing even if libxml is available."
  :type 'boolean
  :group 'helm-google)

(defvar helm-google-input-history nil)
(defvar helm-google-pending-query nil)

(defun helm-google-url ()
  "URL to google searches.
If 'com' TLD is set use 'encrypted' subdomain to avoid country redirects."
  (concat "https://"
          (if (string= "com" helm-google-tld)
              "encrypted"
            "www")
          ".google."
          helm-google-tld
          "/search?ie=UTF-8&oe=UTF-8&q=%s"))

(defun helm-google--process-html (html)
  (replace-regexp-in-string
   "\n" ""
   (with-temp-buffer
     (insert html)
     (html2text)
     (buffer-substring-no-properties (point-min) (point-max)))))

(defmacro helm-google--with-buffer (buf &rest body)
  (declare (doc-string 3) (indent 2))
  `(with-current-buffer ,buf
     (set-buffer-multibyte t)
     (goto-char url-http-end-of-headers)
     (prog1 ,@body
       (kill-buffer ,buf))))

(defun helm-google--parse-w/regexp (buf)
  (helm-google--with-buffer buf
      (let (results result)
        (while (re-search-forward "class=\"r\"><a href=\"/url\\?q=\\(.*?\\)&amp;sa" nil t)
          (setq result (plist-put result :url (match-string-no-properties 1)))
          (re-search-forward "\">\\(.*?\\)</a></h3>" nil t)
          (setq result (plist-put result :title (helm-google--process-html (match-string-no-properties 1))))
          (re-search-forward "class=\"st\">\\([\0-\377[:nonascii:]]*?\\)</span>" nil t)
          (setq result (plist-put result :content (helm-google--process-html (match-string-no-properties 1))))
          (add-to-list 'results result t)
          (setq result nil))
        results)))

(defun helm-google--tree-search (tree)
  (pcase tree
    (`(,x . ,y) (or (and (null y) nil)
                    (and (eql x 'div)
                         (string= (xml-get-attribute tree 'id) "ires")
                         (pcase-let* ((`(_ _ . ,ol) tree)
                                      (`(_ _ . ,items) (car ol)))
                           items))
                    (helm-google--tree-search x)
                    (helm-google--tree-search y)))))

(defun helm-google--parse-w/libxml (buf)
  (let* ((xml (helm-google--with-buffer buf
                  (libxml-parse-html-region
                   (point-min) (point-max))))
         (items (helm-google--tree-search xml))
         (get-string (lambda (element)
                       (mapconcat (lambda (e)
                                    (if (listp e) (car (last e)) e))
                                  element "")))
         (fix-url (lambda (str)
                    (concat "https://www.google." helm-google-tld str)))
         results)
    (dolist (item items results)
      (add-to-list 'results
                   (list :title (funcall get-string (cddr (assoc 'a (assoc 'h3 item))))
                         :cite (funcall get-string (cddr (assoc 'cite (assoc 'div (assoc 'div item)))))
                         :url (funcall fix-url (cdr (assoc 'href (cadr (assoc 'a (assoc 'h3 item))))))
                         :content (helm-google--process-html
                                   (funcall get-string (cddr (assoc 'span (assoc 'div item))))))
                   t))))

(defun helm-google--parse (buf)
  "Extract the search results from BUF."
  (if (or helm-google-use-regexp-parsing
          (not (fboundp 'libxml-parse-html-region)))
      (helm-google--parse-w/regexp buf)
    (helm-google--parse-w/libxml buf)))

(defun helm-google--response-buffer-from-search (text &optional search-url)
  (let ((url-mime-charset-string "utf-8")
        (url (format (or search-url (helm-google-url)) (url-hexify-string text))))
    (url-retrieve-synchronously url t)))

(defun helm-google--search (text)
  (let* ((buf (helm-google--response-buffer-from-search text))
         (results (helm-google--parse buf)))
    results))

(defun helm-google-html-search ()
  "Get Google results by scraping the website.
This is better than using the deprecated API. It gives more
results but is tied to the html output so any change Google
makes can break the results."
  (let* ((results (helm-google--search helm-pattern)))
    (mapcar (lambda (result)
              (let ((cite (plist-get result :cite)))
                (concat
                 (propertize
                  (plist-get result :title)
                  'face 'font-lock-variable-name-face)
                 "\n"
                 (plist-get result :content)
                 "\n"
                 (when cite
                   (concat
                    (propertize
                     cite
                     'face 'link)
                    "\n"))
                 (propertize
                  (plist-get result :url)
                  'face (if cite 'glyphless-char 'link)))))
            results)))

(defun helm-google-api-search ()
  "Get Google results using the `google.el' library.
Since the API this library uses is deprecated it is not very reliable."
  (let* ((results (google-search helm-pattern))
         (responseData (google-result-field 'responseData results))
         (records (google-result-field 'results responseData)))
    (mapcar (lambda (record)
              (concat
               (propertize
                (google-result-field 'titleNoFormatting record)
                'face 'font-lock-variable-name-face)
               "\n"
               (replace-regexp-in-string
                "\n" ""
                (with-temp-buffer
                  (insert (google-result-field 'content record))
                  (html2text)
                  (buffer-substring-no-properties (point-min) (point-max))))
               "\n"
               (propertize
                (url-unhex-string (google-result-field 'url record))
                'face 'link)))
            records)))

(defun helm-google-search ()
  "Invoke the search function set by `helm-google-search-function'."
  (funcall helm-google-search-function))

(defun helm-google-display-to-real (candidate)
  "Retrieve the URL from the results for the action."
  (car (last (split-string candidate "[\n]+"))))

(defvar helm-source-google
  `((name . "Google")
    (init . (lambda () (require 'google)))
    (action ("Browse URL" . browse-url))
    (display-to-real . helm-google-display-to-real)
    (candidates . helm-google-search)
    (requires-pattern)
    (nohighlight)
    (multiline)
    (volatile)))

;;;###autoload
(defun helm-google ()
  "Preconfigured `helm' : Google search."
  (interactive)
  (let ((google-referer "https://github.com/steckerhalter/helm-google")
        (region (when (use-region-p)
                  (buffer-substring-no-properties
                   (region-beginning)
                   (region-end))))
        (helm-input-idle-delay 0.3))
    (helm :sources 'helm-source-google
          :prompt "Google: "
          :input region
          :buffer "*helm google*"
          :history 'helm-google-input-history)))

(provide 'helm-google)

;;; helm-google.el ends here
