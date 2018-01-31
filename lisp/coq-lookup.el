;;; coq-lookup.el --- jump to x86 instruction documentation -*- lexical-binding: t; -*-

;; This is free and unencumbered software released into the public domain.

;; Author: Christopher Wellons <wellons@nullprogram.com>
;; URL: https://github.com/skeeto/coq-lookup
;; Package-Version: 20161215.448
;; Version: 1.1.1
;; Package-Requires: ((emacs "24.3") (cl-lib "0.3"))

;;; Commentary:

;; Requires the following:
;; * pdftotext command line program from Poppler
;; * Intel 64 and IA-32 Architecture Software Developer Manual PDF

;; http://www.intel.com/content/www/us/en/processors/architectures-software-developer-manuals.html

;; Building the index specifically requires Poppler's pdftotext, not
;; just any PDF to text converter. It has a critical feature over the
;; others: conventional line feed characters (U+000C) are output
;; between pages, allowing precise tracking of page numbers. These are
;; the markers Emacs uses for `forward-page' and `backward-page'.

;; Your copy of the manual must contain the full instruction set
;; reference in a single PDF. Set `coq-lookup-pdf' to this file name.
;; Intel optionally offers the instruction set reference in two
;; separate volumes, but don't use that.

;; Choose a PDF viewer by setting `coq-lookup-browse-pdf-function'. If
;; you provide a custom function, your PDF viewer should support
;; linking to a specific page (e.g. not supported by xdg-open,
;; unfortunately). Otherwise there's no reason to use this package.

;; Once configured, the main entrypoint is `coq-lookup'. You may want
;; to bind this to a key. The interactive prompt will default to the
;; mnemonic under the point. Here's a suggestion:

;;   (global-set-key (kbd "C-h x") #'coq-lookup)

;; This package pairs well with `nasm-mode'!

;;; Code

(require 'cl-lib)
(require 'doc-view)

(defgroup coq-lookup ()
  "Options for Coq reference manual lookup."
  :group 'extensions)

(defcustom coq-lookup-pdf nil
  "Path to the Coq reference manual"
  :group 'coq-lookup
  :type '(choice (const nil)
                 (file :must-match t)))

(defcustom coq-lookup-pdftotext-program "pdftotext"
  "Path to pdftotext, part of Popper."
  :group 'coq-lookup
  :type 'string)

(defcustom coq-lookup-browse-pdf-function #'coq-lookup-browse-pdf-any
  "A function that launches a PDF viewer at a specific page.
This function accepts two arguments: filename and page number."
  :group 'coq-lookup
  :type '(choice (function-item :tag "First suitable PDF reader" :value
                                coq-lookup-browse-pdf-any)
                 (function-item :tag "Evince" :value
                                coq-lookup-browse-pdf-evince)
                 (function-item :tag "Xpdf" :value
                                coq-lookup-browse-pdf-xpdf)
                 (function-item :tag "Okular" :value
                                coq-lookup-browse-pdf-okular)
                 (function-item :tag "gv" :value
                                coq-lookup-browse-pdf-gv)
                 (function-item :tag "zathura" :value
                                coq-lookup-browse-pdf-zathura)
                 (function-item :tag "MuPDF" :value
                                coq-lookup-browse-pdf-mupdf)
                 (function-item :tag "browse-url"
                                :value coq-lookup-browse-pdf-browser)
                 (function :tag "Your own function")))

(defcustom coq-lookup-cache-directory
  (let ((base (or (getenv "XDG_CACHE_HOME")
                  (getenv "LocalAppData")
                  "~/.cache")))
    (expand-file-name "coq-lookup" base))
  "Directory where the PDF mnemonic index with be cached."
  :type 'string)

(defvar coq-lookup-index nil
  "Alist mapping instructions to page numbers.")

(defun coq-lookup--expand (name pages-string)
  "Expand string of PDF-sourced mnemonics into user-friendly mnemonics."
  (let* ((pages (split-string pages-string ",\\s-*"))
         (has-many (> (length pages) 1)))
    (cl-loop for page in pages
             for idx from 1
             collect (cons (if has-many
                               (format "%s (#%d)" name idx)
                             name)
                           page))))

(cl-defun coq-lookup-create-index (&optional (pdf coq-lookup-pdf))
  "Create an index alist from PDF mapping mnemonics to page numbers.
This function requires the pdftotext command line program."
  (let ((coding-system-for-read 'utf-8)
        (coding-system-for-write 'utf-8)
        (case-fold-search nil))
    (with-temp-buffer
      (call-process coq-lookup-pdftotext-program nil t nil
                    (file-truename pdf) "-")
      (goto-char (point-min))
      (re-search-forward "^Global Index$")
      (cl-loop while (< (point) (point-max))
               when (looking-at "^\\(.+?\\), \\([0-9, ]+\\)")
               nconc (coq-lookup--expand (match-string 1) (match-string 2)) into index
               do (forward-line)
               finally (cl-return
                        (cl-remove-duplicates
                         index :key #'car :test #'string= :from-end t))))))

(defun coq-lookup--index-file (pdf)
  "Return index filename from PDF filename."
  (concat (sha1 pdf) "_v3"))

(defun coq-lookup--save-index (pdf index)
  "Save INDEX for PDF in `coq-lookup-cache-directory'."
  (let* ((index-file (coq-lookup--index-file pdf))
         (cache-path (expand-file-name index-file coq-lookup-cache-directory)))
    (mkdir coq-lookup-cache-directory t)
    (with-temp-file cache-path
      (prin1 index (current-buffer)))
    index))

(defun coq-lookup--load-index (pdf)
  "Return index PDF from `coq-lookup-cache-directory'."
  (let* ((index-file (coq-lookup--index-file pdf))
         (cache-path (expand-file-name index-file coq-lookup-cache-directory)))
    (when (file-exists-p cache-path)
      (with-temp-buffer
        (insert-file-contents cache-path)
        (setf (point) (point-min))
        (ignore-errors (read (current-buffer)))))))

(defun coq-lookup-ensure-index ()
  "Ensure the PDF index has been created, returning the index."
  (when (null coq-lookup-index)
    (cond
     ((null coq-lookup-pdf)
      (error "No PDF available. Set `coq-lookup-pdf'."))
     ((not (file-exists-p coq-lookup-pdf))
      (error "PDF not found. Check `coq-lookup-pdf'."))
     ((setf coq-lookup-index (coq-lookup--load-index coq-lookup-pdf))
      coq-lookup-index)
     ((progn
        (message "Generating mnemonic index ...")
        (setf coq-lookup-index (coq-lookup-create-index))
        (coq-lookup--save-index coq-lookup-pdf coq-lookup-index)))))
  coq-lookup-index)

(defun coq-lookup-browse-pdf (pdf page)
  "Launch a PDF viewer using `coq-lookup-browse-pdf-function'."
  (funcall coq-lookup-browse-pdf-function pdf page))

;;;###autoload
(defun coq-lookup (mnemonic)
  "Jump to the PDF documentation for MNEMONIC.
Defaults to the mnemonic under point."
  (interactive
   (progn
     (coq-lookup-ensure-index)
     (let* ((mnemonics (mapcar #'car coq-lookup-index))
            (thing (thing-at-point 'word))
            (mnemonic (if (member thing mnemonics) thing nil))
            (prompt (if mnemonic
                        (format "Keyword (default %s): " mnemonic)
                      "Keyword: ")))
       (list
        (completing-read prompt mnemonics nil t nil nil mnemonic)))))
  (let ((page (cdr (assoc mnemonic coq-lookup-index))))
    (coq-lookup-browse-pdf (file-truename coq-lookup-pdf) page)))

;; PDF viewers:

(defun coq-lookup-browse-pdf-pdf-tools (pdf page)
  "View PDF at PAGE using Emacs' `pdf-view-mode' and `display-buffer'."
  (require 'pdf-tools)
  (prog1 t
    (with-selected-window (display-buffer (find-file-noselect pdf :nowarn))
      (with-no-warnings
        (pdf-view-goto-page page)))))

(defun coq-lookup-browse-pdf-doc-view (pdf page)
  "View PDF at PAGE using Emacs' `doc-view-mode' and `display-buffer'."
  (prog1 t
    (unless (doc-view-mode-p 'pdf)
      (error "doc-view not available for PDF"))
    (with-selected-window (display-buffer (find-file-noselect pdf :nowarn))
      (doc-view-goto-page page))))

(defun coq-lookup-browse-pdf-xpdf (pdf page)
  "View PDF at PAGE using xpdf."
  (start-process "xpdf" nil "xpdf" "--" pdf (format "%d" page)))

(defun coq-lookup-browse-pdf-evince (pdf page)
  "View PDF at PAGE using Evince."
  (start-process "evince" nil "evince" "-p" (format "%d" page) "--" pdf))

(defun coq-lookup-browse-pdf-okular (pdf page)
  "View PDF at PAGE file using Okular."
  (start-process "okular" nil "okular" "-p" (format "%d" page) "--" pdf))

(defun coq-lookup-browse-pdf-gv (pdf page)
  "View PDF at PAGE using gv."
  (start-process "gv" nil "gv" "-nocenter" (format "-page=%d" page) "--" pdf))

(defun coq-lookup-browse-pdf-zathura (pdf page)
  "View PDF at PAGE using zathura."
  (start-process "zathura" nil "zathura" "-P" (format "%d" page) "--" pdf))

(defun coq-lookup-browse-pdf-mupdf (pdf page)
  "View PDF at PAGE using MuPDF."
  ;; MuPDF doesn't have a consistent name across platforms.
  ;; Furthermore, Debian ships with a broken "mupdf" wrapper shell
  ;; script and must be avoided. Here we use `executable-find' to
  ;; avoid calling it as mupdf-x11 on non-X11 platforms.
  (let ((exe (or (executable-find "mupdf-x11") "mupdf")))
    (start-process "mupdf" nil exe "--" pdf (format "%d" page))))

(defun coq-lookup-browse-pdf-browser (pdf page)
  "Visit PDF using `browse-url' with a fragment for the PAGE."
  (browse-url (format "file://%s#%d" pdf page)))

(defun coq-lookup-browse-pdf-any (pdf page)
  "Try visiting PDF using the first viewer found."
  (or (ignore-errors (coq-lookup-browse-pdf-pdf-tools pdf page))
      (ignore-errors (coq-lookup-browse-pdf-doc-view pdf page))
      (ignore-errors (coq-lookup-browse-pdf-evince pdf page))
      (ignore-errors (coq-lookup-browse-pdf-xpdf pdf page))
      (ignore-errors (coq-lookup-browse-pdf-okular pdf page))
      (ignore-errors (coq-lookup-browse-pdf-gv pdf page))
      (ignore-errors (coq-lookup-browse-pdf-zathura pdf page))
      (ignore-errors (coq-lookup-browse-pdf-mupdf pdf page))
      (ignore-errors (coq-lookup-browse-pdf-browser pdf page))
      (error "Could not find a PDF viewer.")))

(provide 'coq-lookup)

;;; coq-lookup.el ends here
