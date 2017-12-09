;;; biblio-tests.el --- Tests for the biblio package -*- lexical-binding: t -*-

;; Copyright (C) 2016  Clément Pit-Claudel

;; Author: Clément Pit-Claudel <clement.pitclaudel@live.com>
;; URL: http://github.com/cpitclaudel/biblio.el

;; This program is free software; you can redistribute it and/or modify
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

;;; Commentary:
;;

;;; Code:

(when (require 'undercover nil t)
  (undercover "*.el"))

(require 'biblio)
(require 'noflet)
(require 'buttercup)
(require 'notifications)

(defun biblio-tests--bypass-shut-up (&rest args)
  "Show a (message ARGS) in a notification."
  (notifications-notify :body (apply #'format args)))

(defconst stallman-bibtex "Stallman_1981, title={EMACS the extensible,
customizable self-documenting display editor}, volume={2},
ISSN=\"0737-819X\",
url={http://dx.doi.org/10.1145/1159890.806466},
DOI={10.1145/1159890.806466}, number={1-2}, journal={ACM SIGOA
Newsletter}, publisher={Association for Computing
Machinery (ACM)}, author={Stallman, Richard M.}, year={1981},
month={Apr}, pages={147–156}}")

(defconst stallman-bibtex-clean "
  author       = {Stallman, Richard M.},
  title	       = {EMACS the extensible, customizable self-documenting
                  display editor},
  year	       = 1981,
  volume       = 2,
  number       = {1-2},
  month	       = {Apr},
  pages	       = {147–156},
  issn	       = {0737-819X},
  doi	       = {10.1145/1159890.806466},
  url	       = {http://dx.doi.org/10.1145/1159890.806466},
  journal      = {ACM SIGOA Newsletter},
  publisher    = {Association for Computing Machinery (ACM)}
}")

(defun biblio--dummy-cleanup-func ()
  "Do nothing with no args.")
(defun biblio-tests--dummy-callback (&optional arg)
  "Return a single (optional) ARG."
  arg)

(defconst sample-items
  '(((backend . biblio-dblp-backend)
     (title . "Who builds a house without drawing blueprints?")
     (authors "Leslie Lamport") (container . "Commun. ACM") (type . "Journal Articles")
     (url . "http://dblp.org/rec/journals/cacm/Lamport15") (direct-url . "http://example.com/paper.pdf"))
    ((backend . biblio-dblp-backend)
     (title . "Turing lecture: The computer science of concurrency: the early years.")
     (authors "Leslie Lamport") (container . "Commun. ACM") (type . "Journal Articles")
     (url . "http://dblp.org/rec/journals/cacm/Lamport15a"))
    ((backend . biblio-dblp-backend)
     (title . "An incomplete history of concurrency chapter 1. 1965-1977.")
     (authors "Leslie Lamport") (container . "PODC") (type . "Conference and Workshop Papers")
     (url . "http://dblp.org/rec/conf/podc/Lamport13"))
    ((backend . biblio-dblp-backend)
     (title . "Euclid Writes an Algorithm: A Fairytale.")
     (authors "Leslie Lamport") (container . "Int. J. Software and Informatics") (type . "Journal Articles")
     (url . "http://dblp.org/rec/journals/ijsi/Lamport11"))
    ((backend . biblio-crossref-backend)
     (title . "Fast Paxos") (authors "Leslie Lamport")
     (publisher . "Springer Science + Business Media") (container . ["Distrib. Comput." "Distributed Computing"])
     (references "10.1007/s00446-006-0005-x") (type . "journal-article")
     (doi . "10.1007/s00446-006-0005-x") (url . "http://dx.doi.org/10.1007/s00446-006-0005-x"))
    ((backend . biblio-crossref-backend)
     (title . "Brief Announcement: Leaderless Byzantine Paxos") (authors "Leslie Lamport")
     (publisher . "Springer Science + Business Media")
     (container . ["Lecture Notes in Computer Science" "Distributed Computing"])
     (references "10.1007/978-3-642-24100-0_10")
     (type . "book-chapter") (url . "http://dx.doi.org/10.1007/978-3-642-24100-0_10"))
    ((backend . biblio-dblp-backend)
     (title . "Implementing dataflow with threads.")
     (authors "Leslie Lamport") (container . "Distributed Computing") (type . "Journal Articles")
     (url . nil) (doi . "10.1007/s00446-008-0065-1"))
    ((backend . biblio-dblp-backend)
     (title . "The PlusCal Algorithm Language.")
     (authors "Leslie Lamport") (container . "ICTAC") (type . "Conference and Workshop Papers")
     (url . nil) (doi . nil))))

(describe "Unit tests:"

  (describe "In biblio's core,"

    (describe "in the compatibility section,"
      (let ((alist '((a . 1) (b . 2) (c . 3) (c . 4)))
            (plist '(a  1 b 2 c 3 c 4)))

        (describe "-alist-get"
          (it "can read values from alists"
            (expect (biblio-alist-get 'a alist) :to-equal 1)
            (expect (biblio-alist-get 'b alist) :to-equal 2)
            (expect (biblio-alist-get 'c alist) :to-equal 3)))

        (describe "-plist-to-alist"
          (it "can convert plists"
            (expect (biblio--plist-to-alist plist) :to-equal alist)))))

    (describe "in the utilities section,"

      (describe "-format-bibtex"
        (it "ignores invalid entries"
          (expect (biblio-format-bibtex "@!!") :to-equal "@!!")
          (expect (biblio-format-bibtex "@article{INVALID KEY,}") :to-equal "@article{INVALID KEY,}"))
        (it "formats a typical example properly"
          (expect (biblio-format-bibtex (concat "@ARTIcle{" stallman-bibtex))
                  :to-equal (concat "@Article{Stallman_1981," stallman-bibtex-clean)))
        (it "properly creates keys"
          (expect (biblio-format-bibtex (concat "@article{" stallman-bibtex) t)
                  :to-equal (concat "@Article{stallman81:emacs," stallman-bibtex-clean)))
        (it "replaces the “@data{” header"
          (expect (biblio-format-bibtex (concat "@data{" stallman-bibtex))
                  :to-match "\\`@misc{"))
        (it "falls back to BibTeX if entry isn't BibLaTeX"
          (expect (biblio-format-bibtex (concat "@techreport{" stallman-bibtex))
                  :to-match "\\`@TechReport{"))
        (it "handles a nil format-function"
          (let ((biblio-cleanup-bibtex-function nil))
            (expect (biblio-format-bibtex (concat "@techreport{" stallman-bibtex))
                    :to-equal (concat "@techreport{" stallman-bibtex))))
        (it "doesn't set the BibTeX dialect globally"
          (with-temp-buffer
            (bibtex-mode)
            (let ((bibtex-dialect 'aaa))
              (biblio-format-bibtex (concat "@techreport{" stallman-bibtex))
              (expect bibtex-dialect :to-equal 'aaa))))
        (it "uses font-lock-ensure when available"
          (unless (functionp #'font-lock-ensure)
            (let ((called-p t))
              (noflet ((font-lock-ensure () (setq called-p t)))
                (biblio-format-bibtex "")
                (expect called-p :to-be-truthy))))))

      (describe "-response-as-utf8"
        (it "decodes Unicode characters properly"
          (let ((unicode-str "É Ç € ← 有"))
            (with-temp-buffer
              (insert unicode-str)
              (goto-char (point-min))
              (set-buffer-multibyte nil)
              (expect (biblio-response-as-utf-8) :to-equal unicode-str)))))

      (let* ((http-error--plist '(error http 406))
             (timeout-error--plist '(error url-queue-timeout "Queue timeout exceeded"))
             (http-error--alist '(http . 406))
             (timeout-error--alist '(url-queue-timeout . "Queue timeout exceeded")))

        (describe "-extract-errors"
          (it "extracts errors on a typical example"
            (expect (biblio--extract-errors `(:error ,http-error--plist :error ,timeout-error--plist))
                    :to-equal `(,http-error--alist ,timeout-error--alist))))

        (describe "-throw-on-unexpected-errors"
          (it "supports empty lists"
            (expect (apply-partially #'biblio--throw-on-unexpected-errors
                                     nil nil)
                    :not :to-throw))
          (it "supports whitelists"
            (expect (apply-partially #'biblio--throw-on-unexpected-errors
                                     `(,http-error--alist) `(,http-error--alist))
                    :not :to-throw))
          (it "returns the first error"
            (expect (apply-partially #'biblio--throw-on-unexpected-errors
                                     `(,http-error--alist ,timeout-error--alist) nil)
                    :to-throw 'biblio--url-error '(http . 406))
            (expect (apply-partially #'biblio--throw-on-unexpected-errors
                                     `(,timeout-error--alist ,http-error--alist) nil)
                    :to-throw 'biblio--url-error 'timeout))))

      (describe "-generic-url-callback"
        :var (url-buffer)
        (before-each
          (spy-on #'biblio-tests--dummy-callback :and-call-through)
          (spy-on #'biblio--dummy-cleanup-func)
          (with-current-buffer (setq url-buffer (get-buffer-create " *url*"))
            (insert "Some\npretty\nheaders\n\nAnd a response.")))
        (after-each
          (kill-buffer url-buffer)
          (biblio-kill-buffers))
        (it "calls the cleanup function"
          (with-current-buffer url-buffer
            (funcall (biblio-generic-url-callback
                      #'ignore #'biblio--dummy-cleanup-func)
                     nil))
          (expect #'biblio--dummy-cleanup-func :to-have-been-called))
        (it "invokes its callback in the right buffer"
          (with-current-buffer url-buffer
            (expect (funcall (biblio-generic-url-callback
                              (lambda () (current-buffer)))
                             nil)
                    :to-equal url-buffer)))
        (it "puts the point in the right spot"
          (with-current-buffer url-buffer
            (expect (funcall (biblio-generic-url-callback
                              (lambda () (looking-at-p "And a response.")))
                             nil)
                    :to-be-truthy)))
        (it "always kills the source buffer"
          (with-current-buffer url-buffer
            (funcall (biblio-generic-url-callback #'ignore) nil))
          (expect (buffer-live-p url-buffer) :not :to-be-truthy))
        (let ((errors '(:error (error http 406))))
          (it "stops when passed unexpected errors"
            (with-current-buffer url-buffer
              (expect (shut-up
                        (funcall (biblio-generic-url-callback
                                  #'biblio-tests--dummy-callback)
                                 errors)
                        (shut-up-current-output))
                      :to-match "\\`Error"))
            (expect #'biblio-tests--dummy-callback :not :to-have-been-called))
          (it "swallows invalid response bodies"
            (expect (lambda () (shut-up
                                 (funcall (biblio-generic-url-callback
                                           #'biblio-tests--dummy-callback #'ignore)
                                          nil)))
                    :not :to-throw)
            (expect #'biblio-tests--dummy-callback :not :to-have-been-called)
            (expect (buffer-live-p url-buffer) :to-be-truthy))
          (it "forwards expected errors"
            (with-current-buffer url-buffer
              (expect (funcall (biblio-generic-url-callback
                                #'biblio-tests--dummy-callback #'ignore '(http . 406))
                               errors)
                      :to-equal '((http . 406))))
            (expect #'biblio-tests--dummy-callback :to-have-been-called))))

      (describe "-cleanup-doi"
        (it "Handles prefixes properly"
          (expect (biblio-cleanup-doi "http://dx.doi.org/10.5281/zenodo.44331")
                  :to-equal "10.5281/zenodo.44331")
          (expect (biblio-cleanup-doi "http://doi.org/10.5281/zenodo.44331")
                  :to-equal "10.5281/zenodo.44331"))
        (it "trims spaces"
          (expect (biblio-cleanup-doi "   10.5281/zenodo.44331 \n\t\r ")
                  :to-equal "10.5281/zenodo.44331"))
        (it "doesn't change clean DOIs"
          (expect (biblio-cleanup-doi "10.5281/zenodo.44331")
                  :to-equal "10.5281/zenodo.44331")))

      (describe "-join"
        (it "removes empty entries before joining"
          (expect (biblio-join ", " "a" nil "b" nil "c" '[]) :to-equal "a, b, c")
          (expect (biblio-join-1 ", " '("a" nil "b" nil "c" [])) :to-equal "a, b, c")))

      (describe "-url-retrieve"
        :var (temp-buffer)
        (before-each
          (spy-on #'biblio-tests--dummy-callback)
          (spy-on #'url-queue-retrieve)
          (setq temp-buffer (get-buffer-create " *temp-url-retrieve*"))
          (spy-on #'url-retrieve-synchronously :and-return-value temp-buffer))
        (it "respects the biblio-synchronous setting when t"
          (let ((biblio-synchronous t))
            (shut-up (biblio-url-retrieve "url" #'biblio-tests--dummy-callback))
            (expect #'url-retrieve-synchronously :to-have-been-called)
            (expect #'biblio-tests--dummy-callback :to-have-been-called-with nil)))
        (it "respects the biblio-synchronous setting when nil"
          (let ((biblio-synchronous nil))
            (shut-up (biblio-url-retrieve "url" #'biblio-tests--dummy-callback))
            (expect #'url-queue-retrieve :to-have-been-called)
            (expect #'biblio-tests--dummy-callback :not :to-have-been-called)))))

    (describe "in the major mode help section"
      :var (temp-buf doc-buf)
      (before-each
        (with-current-buffer (setq temp-buf (get-buffer-create " *temp*"))
          (shut-up
            (biblio-selection-mode)
            (setq doc-buf (biblio--selection-help)))))
      (after-each
        (kill-buffer doc-buf)
        (kill-buffer temp-buf))

      (describe "--help-with-major-mode"
        (it (format "produces a live buffer")
          (expect (buffer-live-p (get-buffer doc-buf)) :to-be-truthy))
        (it "shows bindings in order"
          (expect (with-current-buffer doc-buf
                    (and (search-forward "<up>" nil t)
                         (search-forward "<down>" nil t)))
                  :to-be-truthy))))

    (describe "in the interaction section,"
      :var (target-buffer results-buffer)
      (before-each
        (shut-up
          (setq target-buffer (get-buffer-create " *source*"))
          (setq results-buffer (biblio--make-results-buffer
                                target-buffer "A" #'biblio-dblp-backend))
          (with-current-buffer results-buffer
            (biblio-insert-results sample-items))))
      (after-each
        (kill-buffer target-buffer)
        (biblio-kill-buffers))

      (describe "a local variable"
        (it "tracks the target buffer"
          (expect (bufferp (buffer-local-value 'biblio--target-buffer
                                               results-buffer))
                  :to-be-truthy))
        (it "prevents writing"
          (expect (buffer-local-value 'buffer-read-only results-buffer)
                  :to-be-truthy)))

      (describe "a motion command"
        (it "starts from the right position"
          (with-current-buffer results-buffer
            (expect (point) :to-equal 3)))
        (it "can go down"
          (with-current-buffer results-buffer
            (dotimes (_ 2)
              (expect (point) :not :to-equal (biblio--selection-next)))
            (expect (biblio-alist-get 'title (biblio--selection-metadata-at-point))
                    :to-match "\\`An incomplete history ")))
        (it "can go back to the beginning"
          (with-current-buffer results-buffer
            (dotimes (_ 2)
              (biblio--selection-next))
            (expect (point) :not :to-equal (biblio--selection-first))
            (expect (point) :to-equal 3)))
        (it "cannot go beyond the end"
          (with-current-buffer results-buffer
            (dotimes (_ 50)
              (biblio--selection-next))
            (expect (point) :to-equal (biblio--selection-next))))
        (it "can go up"
          (with-current-buffer results-buffer
            (goto-char (point-max))
            (dotimes (_ (1- (length sample-items)))
              (expect (point) :not :to-equal (biblio--selection-previous))
              (expect (point) :not :to-equal (point-max)))
            (expect (biblio-alist-get 'title (biblio--selection-metadata-at-point))
                    :to-match "\\`Turing lecture")))
        (it "cannot go beyond the beginning"
          (with-current-buffer results-buffer
            (goto-char (point-max))
            (dotimes (_ 50)
              (biblio--selection-previous))
            (expect (point) :to-equal 3)
            (expect (point) :to-equal (biblio--selection-previous)))))

      (describe "-get-url"
        (it "works on each item"
          (with-current-buffer results-buffer
            (dotimes (_ (1- (length sample-items)))
              (expect (biblio-get-url (biblio--selection-metadata-at-point))
                      :to-match "\\`https?://")
              (expect (point) :not :to-equal (biblio--selection-next)))
            (expect (point) :to-equal (biblio--selection-next))))
        (it "uses DOIs if URLs are unavailable"
          (with-current-buffer results-buffer
            (goto-char (point-max))
            (dotimes (_ 2) (biblio--selection-previous))
            (expect (biblio-get-url (biblio--selection-metadata-at-point))
                    :to-match "\\`https://doi.org/"))))

      (describe "a browsing command"
        (before-each
          (spy-on #'browse-url))

        (it "opens the right URL"
          (with-current-buffer results-buffer
            (biblio--selection-browse)
            (expect 'browse-url
                    :to-have-been-called-with
                    "http://dblp.org/rec/journals/cacm/Lamport15")))
        (it "complains about missing URLs"
          (with-current-buffer results-buffer
            (goto-char (1- (point-max)))
            (expect #'biblio--selection-browse
                    :to-throw 'user-error '("This record does not contain a URL"))))
        (it "lets users click buttons"
          (with-current-buffer results-buffer
            (expect (search-forward "http" nil t) :to-be-truthy)
            (push-button (point))
            (expect 'browse-url :to-have-been-called))))

      (let ((bibtex "@Article{empty\n}"))
        (describe "a selection command"
          (before-each
            (spy-on #'biblio-dblp-backend
                    :and-call-fake
                    (lambda (_command _metadata forward-to)
                      (funcall forward-to bibtex))))
          (it "can copy bibtex records"
            (with-current-buffer results-buffer
              (shut-up (biblio--selection-copy))
              (expect (car kill-ring) :to-equal bibtex)
              (expect #'biblio-dblp-backend :to-have-been-called)))
          (it "can copy bibtex records and quit"
            (with-current-buffer results-buffer
              (shut-up (biblio--selection-copy-quit))
              (expect (car kill-ring) :to-equal bibtex)
              (expect #'biblio-dblp-backend :to-have-been-called)))
          (it "can insert bibtex records"
            (with-current-buffer results-buffer
              (shut-up (biblio--selection-insert))
              (with-current-buffer target-buffer
                (expect (buffer-string) :to-equal (concat bibtex "\n\n")))
              (expect #'biblio-dblp-backend :to-have-been-called)))
          (it "can insert bibtex records and quit"
            (with-current-buffer results-buffer
              (shut-up (biblio--selection-insert-quit))
              (with-current-buffer target-buffer
                (expect (buffer-string) :to-equal (concat bibtex "\n\n")))
              (expect #'biblio-dblp-backend :to-have-been-called)))
          (it "complains about empty entries"
            (with-temp-buffer
              (expect #'biblio--selection-copy
                      :to-throw 'user-error '("No entry at point"))))))

      (describe "a buffer change command"
        :var (new-target)
        (before-each
          (setq new-target (get-buffer-create " *biblio-new-target*"))
          (spy-on #'read-buffer :and-return-value (buffer-name new-target)))
        (after-each
          (kill-buffer new-target))
        (it "changes the target buffer"
          (with-current-buffer results-buffer
            (call-interactively #'biblio--selection-change-buffer)
            (expect biblio--target-buffer :to-equal new-target)))
        (it "rejects read-only buffers"
          (with-current-buffer results-buffer
            (with-current-buffer new-target
              (setq buffer-read-only t))
            (expect (lambda () (call-interactively #'biblio--selection-change-buffer))
                    :to-throw 'user-error))))

      (describe "--selection-extended-action for Dissemin"
        (before-each
          (spy-on 'biblio-completing-read-alist
                  :and-return-value #'biblio-dissemin--lookup-record)
          (spy-on #'biblio-dissemin--lookup-record))
        (it "runs an action as expected"
          (with-current-buffer results-buffer
            (call-interactively #'biblio--selection-extended-action)
            (expect #'biblio-dissemin--lookup-record
                    :to-have-been-called-with
                    (biblio--selection-metadata-at-point))))
        (it "complains about missing entries"
          (with-temp-buffer
            (expect (lambda ()
                      (call-interactively #'biblio--selection-extended-action))
                    :to-throw 'user-error))))

      (describe "--selection-extended-action for downloading"
        (before-each
          (spy-on 'biblio-completing-read-alist
                  :and-return-value #'biblio-download--action)
          (spy-on #'biblio-download--action :and-call-through)
          (spy-on #'read-file-name :and-return-value "/target.pdf")
          (spy-on #'url-copy-file))
        (it "runs an action as expected"
          (with-current-buffer results-buffer
            (call-interactively #'biblio--selection-extended-action)
            (expect #'biblio-download--action
                    :to-have-been-called-with
                    (biblio--selection-metadata-at-point))
            (expect #'url-copy-file
                    :to-have-been-called-with
                    "http://example.com/paper.pdf" "/target.pdf")))
        (it "complains about missing entries"
          (with-temp-buffer
            (expect (lambda ()
                      (call-interactively #'biblio--selection-extended-action))
                    :to-throw 'user-error))))

      (dolist (func '(biblio-completing-read biblio-completing-read-alist))
        (describe (format "%S" func)
          (before-each
            (spy-on #'completing-read))
          (it "uses ido by default"
            (let ((completing-read-function #'completing-read-default))
              (funcall func "A" nil)
              (expect #'completing-read :to-have-been-called)
              (expect (biblio--completing-read-function) :to-be #'ido-completing-read)))
          (it "respects users choices"
            (let ((completing-read-function #'ignore))
              (funcall func "A" nil)
              (expect #'completing-read :to-have-been-called)
              (expect (biblio--completing-read-function) :to-be #'ignore)))))

      (describe "the mode line"
        (it "mentions the target buffer"
          (with-current-buffer results-buffer
            (let ((biblio--target-buffer (get-buffer-create " *biblio-dummy-target*")))
              (expect (biblio--selection-mode-name)
                      :to-match (regexp-quote (buffer-name biblio--target-buffer)))
              (kill-buffer biblio--target-buffer)))))

      (describe "-kill-buffers"
        (it "actually kills buffers"
          (biblio-kill-buffers)
          (expect (buffer-live-p results-buffer) :not :to-be-truthy))))

    (describe "in the printing section,"

      (describe "--prepare-authors"
        (it "removes spaces"
          (expect (biblio--prepare-authors '(" A " " B"))
                  :to-equal "A, B"))
        (it "obeys -authors-limit"
          (let ((biblio-authors-limit 2))
            (expect (biblio--prepare-authors '("A" "B" "C" "D"))
                    :to-equal "A, B, C, D")
            (expect (biblio--prepare-authors '("A" "B" "C" "D" "E"))
                    :to-equal "A, B, … (3 more)")))))

    (describe "in the searching section,"

      (describe "--read-backend"
        (before-each
          (spy-on #'biblio-completing-read-alist))
        (it "offers all backends"
          (biblio--read-backend)
          (expect #'biblio-completing-read-alist
                  :to-have-been-called-with
                  "Backend: "
                  '(("arXiv" . biblio-arxiv-backend)
                    ("CrossRef" . biblio-crossref-backend)
                    ("DBLP" . biblio-dblp-backend)
                    ("HAL" . biblio-hal-backend))
                  nil t)))

      (describe "--read-query"
        (before-each
          (spy-on #'read-string))
        (it "asks for a query"
          (biblio--read-query #'biblio-dblp-backend)
          (expect #'read-string :to-have-been-called)))

      (describe "-lookup"
        (before-each
          (spy-on #'biblio--lookup-1)
          (spy-on #'biblio--read-backend :and-return-value #'biblio-dblp-backend)
          (spy-on #'biblio--read-query :and-return-value "query"))
        (it "interactively prompts for a backend"
          (call-interactively #'biblio-lookup)
          (expect #'biblio--read-backend :to-have-been-called))
        (it "interactively prompts for a query string"
          (call-interactively #'biblio-lookup)
          (expect #'biblio--read-query :to-have-been-called-with #'biblio-dblp-backend))
        (it "passes the backend and the query string to --lookup-1"
          (call-interactively #'biblio-lookup)
          (expect #'biblio--lookup-1 :to-have-been-called-with #'biblio-dblp-backend "query")))))

  (describe "In the CrossRef module"

    (describe "-crossref--parse-search-results"
      (it "complains about non-ok statuses"
        (expect (shut-up
                  (with-temp-buffer
                    (save-excursion (insert "{}"))
                    (biblio-crossref--parse-search-results))
                  (shut-up-current-output))
                :to-equal "Warning (biblio-crossref): CrossRef query failed\n"))))

  (describe "In the DBLP module"

    (describe "-dblp--parse-search-results"
      (it "complains about non-ok statuses"
        (expect (shut-up
                  (with-temp-buffer
                    (biblio-dblp--parse-search-results))
                  (shut-up-current-output))
                :to-equal "Warning (biblio-dblp): DBLP query failed\n"))))

  (describe "In the HAL module"

    (describe "-hal--parse-search-results"
      (it "complains about missing results"
        (expect (shut-up
                  (with-temp-buffer
                    (save-excursion (insert "{}"))
                    (biblio-hal--parse-search-results))
                  (shut-up-current-output))
                :to-equal "Warning (biblio-hal): HAL query failed\n"))))

  (describe "In the Dissemin module"

    (describe "-dissemin-parse-record"
      (it "complains about non-ok statuses"
        (expect (shut-up
                  (with-temp-buffer
                    (save-excursion (insert "{}"))
                    (biblio-dissemin--parse-buffer))
                  (shut-up-current-output))
                :to-equal "Warning (biblio-dissemin): Dissemin query failed\n")))

    (describe "-dissemin--translate-classification"
      (it "lets unexpected classifications through"
        (expect (biblio-dissemin--translate-classification 'argh)
                :to-be 'argh)))

    (describe "-dissemin--lookup-record"
      (before-each
        (spy-on #'biblio-dissemin-lookup))
      (it "passes a DOI to -dissemin-lookup"
        (let ((doi (make-symbol "AAA")))
          (biblio-dissemin--lookup-record `((doi . ,doi)))
          (expect #'biblio-dissemin-lookup :to-have-been-called-with doi)))
      (it "complains if the record contains no DOI"
        (expect (lambda () (biblio-dissemin--lookup-record nil))
                :to-throw 'user-error '("Dissemin needs a DOI, but this record does not contain one"))
        (expect #'biblio-dissemin-lookup :not :to-have-been-called)))))

(defconst biblio-tests--script-full-path
  (or (and load-in-progress load-file-name)
      (bound-and-true-p byte-compile-current-file)
      (buffer-file-name))
  "Full path of this script.")

(defconst biblio-tests--feature-tests
  '((crossref "renear -ontologies" "Strategic Reading" biblio-crossref-backend)
    (dblp "author:lamport" "Who builds a house" biblio-dblp-backend)
    (hal "coq inria" "The Coq Proof Assistant" biblio-hal-backend)
    (arxiv "all:electron" "Impact of Electron-Electron Cusp" biblio-arxiv-backend)))

(defun biblio-tests--cache-file-path (fname)
  "Compute full name of cache file FNAME."
  (let ((test-dir (file-name-directory biblio-tests--script-full-path)))
    (expand-file-name fname (expand-file-name "cache" test-dir))))

(defun biblio-tests--url (backend-sym query)
  "Compute a URL from BACKEND-SYM and QUERY."
  (funcall (intern (format "biblio-%S--url" backend-sym)) query))

(defconst biblio-tests--cache
  (seq-map (lambda (pair) (cons (biblio-tests--cache-file-path (car pair)) (cdr pair)))
           (append
            '(("1159890.806466" . "http://doi.org/10.1145/1159890.806466")
              ("science.1157784" . "http://doi.org/10.1126/science.1157784")
              ("Lamport15" . "http://dblp.org/rec/bib2/journals/cacm/Lamport15")
              ("1.1383585" . "http://doi.org/10.1063/1.1383585")
              ;; ("arxiv-higgs-response" . "http://export.arxiv.org/api/query?search_query=higgs%20boson")
              ;; ("dissemin-higgs-boson" . "http://dissem.in/api/10.1016/j.physletb.2003.06.057")
              ;; ("doi-higgs-boson" . "http://doi.org/10.1016/j.physletb.2003.06.057")
              ("dissemin-j.paid.2009.02.013" . "http://dissem.in/api/10.1016/j.paid.2009.02.013")
              ("dissemin-1159890.806466" . "http://dissem.in/api/10.1145/1159890.806466")
              ("dissemin-science.1157784" . "http://dissem.in/api/10.1126/science.1157784")
              ("crosscite-zenodo.44331" . "http://crosscite.org/citeproc/format?doi=10.5281/zenodo.44331&style=bibtex&lang=en-US"))
            (seq-map (lambda (test)
                       (pcase test
                         (`(,server ,query . ,_)
                          (cons (format "%S-response" server) (biblio-tests--url server query)))))
                     biblio-tests--feature-tests))))

(defun biblio-tests--store-responses (force)
  "Download and save responses from various tested APIs.
With FORCE, update existing records."
  (interactive "P")
  (pcase-dolist (`(,fpath . ,url) biblio-tests--cache)
    (let ((url-mime-accept-string
           (unless (string-match-p "response$" fpath)
             biblio-doi--dx-mime-accept)))
      (unless (and (file-exists-p fpath) (not force))
        (with-current-buffer (url-retrieve-synchronously url)
          (write-file fpath)
          (kill-buffer))))))

(defconst biblio-tests--reverse-cache
  (seq-map (lambda (p) (cons (cdr p) (car p))) biblio-tests--cache))

(defmacro biblio-tests--intercept-url-requests (&optional which-events)
  "Set up buttercup to intercept URL queries.
Queries for stored urls (in `biblio-tests--reverse-cache') are
serviced from disk; others are handled as an http error (expect
if WHICH-EVENTS is given; in that case, WHICH-EVENTS is used
instead."
  `(spy-on #'url-queue-retrieve
           :and-call-fake
           (lambda (url callback &optional cbargs)
             (with-temp-buffer
               (-if-let* ((file-name (cdr (assoc url biblio-tests--reverse-cache))))
                   (progn
                     (insert-file-contents-literally file-name nil)
                     (apply callback nil cbargs))
                 (apply callback (or ,which-events '(:error (error http "Resource not cached"))) cbargs))))))

(describe "Feature tests:"

  (pcase-dolist (`(,sym ,query ,first-result ,backend) biblio-tests--feature-tests)
    (when backend
      (describe (format "The %S backend" sym)
        :var (results-buffer)
        (before-each
          (biblio-tests--intercept-url-requests)
          (spy-on #'read-string :and-return-value query)
          (spy-on #'browse-url))

        (it "downloads results properly"
          (expect
           (shut-up
             (setq results-buffer
                   (funcall (intern (concat (symbol-name sym) "-lookup"))))
             (shut-up-current-output))
           :to-match "\\`Fetching "))

        (describe "produces a result buffer that"
          (it "is live"
            (expect (buffer-live-p results-buffer) :to-be-truthy))
          (it "has the right major mode"
            (with-current-buffer results-buffer
              (expect major-mode :to-equal 'biblio-selection-mode)))
          (it "has at least one entry matching the entry regexp"
            (with-current-buffer results-buffer
              (expect (buffer-size) :to-be-greater-than 10)
              (goto-char (point-min))
              (expect (point) :not :to-equal (biblio--selection-next))
              (expect (save-excursion
                        (beginning-of-line)
                        (looking-at-p biblio--search-result-marker-regexp))
                      :to-be-truthy)))
          (it "has an entry with the right title"
            (with-current-buffer results-buffer
              (expect (looking-at-p first-result))))
          (pcase sym
            (`crossref
             (it "has at least the right fields, in the right order"
               (with-current-buffer results-buffer
                 (expect (search-forward "In: " nil t) :to-be-truthy)
                 (expect (search-forward "Type: " nil t) :to-be-truthy)
                 (expect (search-forward "Publisher: " nil t) :to-be-truthy)
                 (expect (search-forward "References: " nil t) :to-be-truthy)
                 (expect (search-forward "URL: " nil t) :to-be-truthy)
                 (expect (button-label (button-at (1- (point-at-eol)))) :to-match "http://")
                 (expect (search-backward "\n\n" nil t) :not :to-be-truthy)))
             (it "complains about missing direct URLs"
               (with-current-buffer results-buffer
                 (biblio--selection-first)
                 (expect #'biblio--selection-browse-direct
                         :to-throw 'user-error '("This record does not contain a direct URL (try arXiv or HAL)")))))
            (`arxiv
             (it "shows affiliations"
               (with-current-buffer results-buffer
                 (biblio--selection-first)
                 (expect (search-forward " (NMRC, University College, Cork, Ireland)" nil t) :to-be-truthy)))
             (it "opens the right URL when browsing to PDF"
               (with-current-buffer results-buffer
                 (biblio--selection-browse-direct)
                 (expect 'browse-url
                         :to-have-been-called-with
                         "http://arxiv.org/pdf/cond-mat/0102536v1")))))
          (it "has no empty titles"
            (with-current-buffer results-buffer
              (expect (search-forward "\n\n> \n" nil t) :not :to-be-truthy)))
          (describe "can compute a proper BibTeX entry that"
            :var (bibtex)
            (it "is correctly forwarded"
              (with-current-buffer results-buffer
                (shut-up
                  (biblio--selection-forward-bibtex
                   (lambda (bib _meta) (setq bibtex bib))))))
            (it "is a string"
              (expect (stringp bibtex) :to-be-truthy))
            (it "is not empty"
              (expect (seq-empty-p bibtex) :not :to-be-truthy))
            (it "starts with @"
              (expect bibtex :to-match "\\`@"))
            (it "is properly formatted"
              (expect bibtex :to-equal (biblio-format-bibtex bibtex)))
            (it "can be auto-generated"
              (with-current-buffer results-buffer
                (let (auto-bibtex)
                  (expect
                   (shut-up
                     (biblio-arxiv--forward-bibtex
                      (cons '(doi . nil) (biblio--selection-metadata-at-point))
                      (lambda (auto-bib) (setq auto-bibtex auto-bib)))
                     (shut-up-current-output))
                   :to-match "\\`Auto-generating a BibTeX entry")
                  (expect auto-bibtex :to-match "\\`@Online{")))))))))

  (describe "biblio-doi"
    (before-each
      (biblio-tests--intercept-url-requests '(:error (error http 406)))
      (spy-on #'biblio-insert-results :and-call-through)
      (spy-on #'biblio-crossref-backend :and-call-through)
      (spy-on #'biblio-doi--crosscite-url :and-call-through))
    (it "downloads and formats a record properly"
      (with-temp-buffer
        (shut-up (doi-insert-bibtex "10.1145/1159890.806466"))
        (expect (buffer-string)
                :to-equal (concat (biblio-format-bibtex (buffer-string)) "\n\n"))
        (expect (buffer-string)
                :to-match "journal += {ACM SIGOA Newsletter}")
        (expect url-mime-accept-string :to-equal nil)))
    (it "falls back to crosscite if doi.org returns a 406"
      (with-temp-buffer
        (let ((buf (current-buffer))
              (output (shut-up
                        (doi-insert-bibtex "10.5281/zenodo.44331")
                        (shut-up-current-output))))
          (expect output :to-match "\\`Fetching http://doi")
          (expect output :to-match "^Fetching http://crosscite.org")
          (expect (current-buffer) :to-be buf)
          (expect (buffer-live-p buf) :to-be-truthy)
          (expect #'biblio-insert-results :not :to-have-been-called)
          (expect #'biblio-crossref-backend :not :to-have-been-called)
          (expect #'biblio-doi--crosscite-url :to-have-been-called)
          ;; Note lack of spacing, due to invalid BibTeX key being created by CrossCite
          (expect (buffer-string) :to-match "author={Pit-Claudel")
          (expect url-mime-accept-string :to-equal nil)))))

  (describe "biblio-dissemin"
    (before-each
      (biblio-tests--intercept-url-requests))

    (dolist (doi '("http://doi.org/10.1145/1159890.806466" "10.1016/j.paid.2009.02.013" "10.1126/science.1157784"))
      (describe (format "(for DOI %S)" doi)
        :var (buf)
        (it "creates a results buffer properly"
          (shut-up (setq buf (dissemin-lookup doi t)))
          (expect (buffer-live-p buf) :to-be-truthy)
          (expect (buffer-name buf) :to-match "Dissemin")
          (expect (buffer-size buf) :to-be-greater-than 0))
        (it "puts the point at the beginning of the buffer"
          (with-current-buffer buf
            (expect (point) :to-equal 1)))
        (if (string= doi "10.1126/science.1157784")
            (it "shows a message when no records are available"
              (with-current-buffer buf
                (expect (search-forward "(no records)" nil t) :to-be-truthy)))
          (it "loads records, when available"
            (with-current-buffer buf
              (expect (search-forward ">> ft" nil t) :to-be-truthy)))
          (it "hyperlinks URLs"
            (with-current-buffer buf
              (expect (search-forward "  http://" nil t) :to-be-truthy)
              (expect (button-at (point)) :to-be-truthy)))
          (it "does not duplicate urls inside a given record"
            (with-temp-buffer
              (let ((temp (current-buffer)))
                (with-current-buffer buf
                  (copy-to-buffer temp (point-min) (point-max)))
                (goto-char (point-min))
                (expect (buffer-size) :to-equal
                        (progn
                          (when (fboundp #'delete-duplicate-lines)
                            (delete-duplicate-lines (point-min) (point-max)))
                          (buffer-size)))))))))))

(provide 'biblio-tests)
;;; biblio-tests.el ends here
