;; company-emacs-eclim.el --- an interface to the Eclipse IDE.
;;
;; Copyright (C) 2012   Fredrik Appelberg
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;;; Contributors
;;
;;; Conventions
;;
;; Conventions used in this file: Name internal variables and functions
;; "eclim--<descriptive-name>", and name eclim command invocations
;; "eclim/command-name", like eclim/project-list.
;;; Description
;;
;; company-emacs-eclim.el -- completion functions used by the company-mode
;;    and auto-complete-mode backends.
;;

(require 'thingatpt)

(defun eclim--completion-candidate-type (candidate)
  "Returns the type of a candidate."
  (assoc-default 'type candidate))

(defun eclim--completion-candidate-class (candidate)
  "Returns the class name of a candidate."
  (assoc-default 'info candidate))

(defun eclim--completion-candidate-doc (candidate)
  "Returns the documentation for a candidate."
  (assoc-default 'menu candidate))

(defun eclim--completion-candidate-package (candidate)
  "Returns the package name of a candidate."
  (let ((doc (eclim--completion-candidate-doc candidate)))
    (when (string-match "\\(.*\\)\s-\s\\(.*\\)" doc)
      (match-string 2 doc))))

(defvar eclim--completion-candidates nil)

(defun eclim--complete ()
  (setq eclim--is-completing t)
  (unwind-protect
      (setq eclim--completion-candidates
            (case major-mode
              (java-mode
               (assoc-default 'completions
                              (eclim/execute-command "java_complete" "-p" "-f" "-e" ("-l" "standard") "-o")))
              ((xml-mode nxml-mode)
               (eclim/execute-command "xml_complete" "-p" "-f" "-e" "-o"))
              (ruby-mode
               (eclim/execute-command "ruby_complete" "-p" "-f" "-e" "-o"))
              (php-mode
               (eclim/execute-command "php_complete" "-p" "-f" "-e" "-o"))
              ((javascript-mode js-mode)
               (eclim/execute-command "javascript_complete" "-p" "-f" "-e" "-o"))
              ((c++-mode c-mode)
               (eclim/execute-command "c_complete" "-p" "-f" "-e" ("-l" "standard") "-o"))))
    (setq eclim--is-completing nil)))

(defun eclim--completion-candidates-filter (c)
  (case major-mode
    ((xml-mode nxml-mode) (or (search "XML Schema" c)
                              (search "Namespace" c)))
    (t nil)))

(defun eclim--completion-candidate-menu-item (candidate)
  "Returns the part of the completion candidate to be displayed
in a completion menu."
  (assoc-default (case major-mode
                   (java-mode 'info)
                   (t 'completion)) candidate))

(defun eclim--completion-candidates ()
  (with-no-warnings
    (remove-if #'eclim--completion-candidates-filter
               (mapcar #'eclim--completion-candidate-menu-item
               (eclim--complete)))))

(defun eclim--basic-complete-internal (completion-list)
  "Displays a buffer of basic completions."
  (let* ((window (get-buffer-window "*Completions*" 0))
         (c (eclim--java-identifier-at-point nil t))
         (beg (car c))
         (word (cdr c))
         (compl (try-completion word
                                completion-list)))
    (if (and (eq last-command this-command)
             window (window-live-p window) (window-buffer window)
             (buffer-name (window-buffer window)))
        ;; If this command was repeated, and there's a fresh completion window
        ;; with a live buffer, and this command is repeated, scroll that
        ;; window.
        (with-current-buffer (window-buffer window)
          (if (pos-visible-in-window-p (point-max) window)
              (set-window-start window (point-min))
            (save-selected-window
              (select-window window)
              (scroll-up))))
      (cond
       ((null compl)
        (message "No completions."))
       ((stringp compl)
        (if (string= word compl)
            ;; Show completion buffer
            (let ((list (all-completions word completion-list)))
              (setq list (sort list 'string<))
              (with-output-to-temp-buffer "*Completions*"
                (display-completion-list list word)))
          ;; Complete
          (delete-region beg (point))
          (insert compl)
          ;; close completion buffer if there's one
          (let ((win (get-buffer-window "*Completions*" 0)))
            (if win (quit-window nil win)))))
       (t (message "That's the only possible completion."))))))

(defun eclim-complete ()
  "Attempts a context sensitive completion for the current
element, then displays the possible completions in a separate
buffer."
  (interactive)
  (when eclim-auto-save (save-buffer))
  (eclim--basic-complete-internal
   (eclim--completion-candidates)))

(defun eclim--completion-yasnippet-convert (completion)
  "Convert a completion string to a yasnippet template"
  (apply #' concat
            (loop for c across (replace-regexp-in-string ", " "," completion)
                  collect (case c
                            (40 "(${")
                            (60 "<${")
                            (44 "}, ${")
                            (41 "})")
                            (62 "}>")
                            (t (char-to-string c))))))

(defvar eclim--completion-start)

(defun eclim-completion-start ()
  "Work out the point where completion starts."
  (setq eclim--completion-start
        (save-excursion
          (case major-mode
            ((java-mode javascript-mode js-mode ruby-mode php-mode c-mode c++-mode)
             (progn
               (ignore-errors (beginning-of-thing 'symbol))
               ;; Completion candidates for annotations don't include '@'.
               (when (eq ?@ (char-after))
                 (forward-char 1))
               (point)))
            ((xml-mode nxml-mode)
             (while (not (string-match "[<\n[:blank:]]" (char-to-string (char-before))))
               (backward-char))
             (point))))))

(defun eclim--completion-action-java ()
  (let* ((end (point))
         (completion (buffer-substring-no-properties eclim--completion-start end)))
    (cond ((string-match "\\(.*?\\) :.*- Override method" completion)
           (let ((sig (eclim--java-parse-method-signature (match-string 1 completion))))
             (delete-region eclim--completion-start end)
             (eclim-java-implement (symbol-name (assoc-default :name sig)))))
          ((string-match "\\([^-:]+\\) .*?\\(- *\\(.*\\)\\)?" completion)
           (let* ((insertion (match-string 1 completion))
                  (rest (match-string 3 completion))
                  (package (if (and rest (string-match "\\w+\\(\\.\\w+\\)*" rest)) rest nil))
                  (template (eclim--completion-yasnippet-convert insertion)))
             (delete-region eclim--completion-start end)
             (if (and eclim-use-yasnippet template (featurep 'yasnippet) yas-minor-mode)
                 (yas/expand-snippet template)
               (insert insertion))
             (when package
               (eclim-java-import
                (concat package "." (substring insertion 0 (or (string-match "[<(]" insertion)
                                                               (length insertion)))))))))))

(defun eclim--completion-action-xml ()
  (when (string-match "[\n[:blank:]]" (char-to-string (char-before eclim--completion-start)))
    ;; we are completing an attribute; let's use yasnippet to get som nice completion going
    (let* ((end (point))
           (c (buffer-substring-no-properties eclim--completion-start end))
           (completion (if (s-ends-with? "\"" c) c (concat c "=\"\""))))
      (when (string-match "\\(.*\\)=\"\\(.*\\)\"" completion)
        (delete-region eclim--completion-start end)
        (if (and eclim-use-yasnippet (featurep 'yasnippet)  yas-minor-mode)
            (yas/expand-snippet (format "%s=\"${1:%s}\" $0" (match-string 1 completion) (match-string 2 completion)))
          (insert completion))))))

(defun eclim--completion-action-default ()
  (when (and (= 40 (char-before)) (not (looking-at ")")))
    ;; we've inserted an open paren, so let's close it
    (if (and eclim-use-yasnippet (featurep 'yasnippet) yas-minor-mode)
        (yas/expand-snippet "$1)$0")
      (progn
        (insert ")")
        (backward-char)))))

(defun eclim--completion-action ()
  (case major-mode
    ('java-mode (eclim--completion-action-java))
    ((c-mode c++-mode) (eclim--completion-action-java))
    ('nxml-mode (eclim--completion-action-xml))
    (t (eclim--completion-action-default))))

(defun eclim--render-doc (str)
  "Performs rudimentary rendering of HTML elements in
documentation strings."
  (apply #'concat
         (loop for p = 0 then (match-end 0)
               while (string-match "[[:blank:]]*\\(.*?\\)\\(</?.*?>\\)" str p) collect (match-string 1 str) into ret
               for tag = (downcase (match-string 2 str))
               when (or (string= tag "</p>") (string= tag "<p>")) collect "\n" into ret
               when (string= tag "<br/>") collect " " into ret
               when (string= tag "<li>") collect " * " into ret
               finally return (append ret (list (substring str p))))))

(defun eclim--completion-documentation (symbol)
  "Looks up the documentation string for the given SYMBOL in the
completion candidates list."
  (let ((doc (assoc-default 'info (find symbol eclim--completion-candidates :test #'string= :key #'eclim--completion-candidate-menu-item))))
    (when doc
      (eclim--render-doc doc))))

(provide 'eclim-completion)
