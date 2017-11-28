;;; nov.el --- Featureful EPUB reader mode

;; Copyright (C) 2017 Vasilij Schneidermann <mail@vasilij.de>

;; Author: Vasilij Schneidermann <mail@vasilij.de>
;; URL: https://github.com/wasamasa/nov.el
;; Version: 0.2.1
;; Package-Requires: ((dash "2.12.0") (esxml "0.3.3") (emacs "24.4"))
;; Keywords: hypermedia, multimedia, epub

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
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

;; nov.el provides a major mode for reading EPUB documents.
;;
;; Features:
;;
;; - Basic navigation (jump to TOC, previous/next chapter)
;; - Remembering and restoring the last read position
;; - Jump to next chapter when scrolling beyond end
;; - Renders EPUB2 (.ncx) and EPUB3 (<nav>) TOCs
;; - Hyperlinks to internal and external targets
;; - Supports textual and image documents
;; - View source of document files
;; - Metadata display
;; - Image rescaling

;;; Code:

(require 'cl-lib)
(require 'dash)
(require 'esxml-query)
(require 'shr)
(require 'url-parse)

(when (not (fboundp 'libxml-parse-xml-region))
  (message "Your Emacs wasn't compiled with libxml support"))


;;; EPUB preparation

(defgroup nov nil
  "EPUB reader mode"
  :group 'multimedia)

(defcustom nov-unzip-program (executable-find "unzip")
  "Path to `unzip` executable."
  :type '(file :must-match t)
  :group 'nov)

(defcustom nov-variable-pitch t
  "Non-nil if a variable pitch face should be used.
Otherwise the default face is used."
  :type 'boolean
  :group 'nov)

(defcustom nov-text-width nil
  "Width filled text shall occupy.
An integer is interpreted as the number of columns.  If nil, use
the full window's width.  Note that this variable only has an
effect in Emacs 25.1 or greater."
  :type '(choice (integer :tag "Fixed width in characters")
                 (const   :tag "Use the width of the window" nil))
  :group 'nov)

(defcustom nov-render-html-function 'nov-render-html
  "Function used to render HTML.
It's called without arguments with a buffer containing HTML and
should change it to contain the rendered version of it.")

(defcustom nov-pre-html-render-hook nil
  "Hook run before `nov-render-html'."
  :type 'hook
  :group 'nov)

(defcustom nov-post-html-render-hook nil
  "Hook run after `nov-render-html'."
  :type 'hook
  :group 'nov)

(defcustom nov-save-place-file (locate-user-emacs-file "nov-places")
  "File name where last reading places are saved to and restored from.
If set to `nil', no saving and restoring is performed."
  :type '(choice (file  :tag "File name")
                 (const :tag "Don't save last reading places" nil))
  :group 'nov)

(defvar-local nov-temp-dir nil
  "Temporary directory containing the buffer's EPUB files.")

(defvar-local nov-content-file nil
  "Path of the EPUB buffer's .opf file.")

(defvar-local nov-epub-version nil
  "Version string of the EPUB buffer.")

(defvar-local nov-metadata nil
  "Metadata of the EPUB buffer.")

(defvar-local nov-documents nil
  "Alist for the EPUB buffer's documents.
Each alist item consists of the identifier and full path.")

(defvar-local nov-documents-index 0
  "Index of the currently rendered document in the EPUB buffer.")

(defvar-local nov-toc-id nil
  "TOC identifier of the EPUB buffer.")

(defun nov-make-path (directory file)
  "Create a path from DIRECTORY and FILE."
  (concat (file-name-as-directory directory) file))

(defun nov-directory-files (directory)
  "Returns a list of files in DIRECTORY except for . and .."
  (--remove (string-match-p "/\\.\\(?:\\.\\)?\\'" it)
            (directory-files directory t)))

(defun nov-contains-nested-directory-p (directory)
  "Non-nil if DIRECTORY contains exactly one directory."
  (let* ((files (nov-directory-files directory))
         (file (car files)))
    (and (= (length files) 1)
         (file-directory-p file)
         file)))

(defun nov-unnest-directory (directory child)
  "Move contents of CHILD into DIRECTORY, then delete CHILD."
  ;; FIXME: this will most certainly fail for con/con
  (dolist (item (nov-directory-files child))
    (rename-file item directory))
  (delete-directory child))

(defun nov--fix-permissions (file-or-directory)
  (->> (file-modes file-or-directory)
       (file-modes-symbolic-to-number "+r")
       (set-file-modes file-or-directory)))

(defun nov-fix-permissions (directory)
  "Iterate recursively through DIRECTORY to fix its files."
  (nov--fix-permissions directory)
  (dolist (file (nov-directory-files directory))
    (if (file-directory-p file)
        (nov-fix-permissions file)
      (nov--fix-permissions file))))

(defun nov-unzip-epub (directory filename)
  "Extract FILENAME into DIRECTORY.
Unnecessary nesting is removed with `nov-unnest-directory'."
  (let ((status (call-process nov-unzip-program nil nil t
                              "-d" directory filename))
        child)
    (while (setq child (nov-contains-nested-directory-p directory))
      (nov-unnest-directory directory child))
    ;; HACK: unzip preserves file permissions, no matter how silly they
    ;; are, so ensure files and directories are readable
    (nov-fix-permissions directory)
    status))

(defmacro nov-ignore-file-errors (&rest body)
  "Like `ignore-errors', but for file errors."
  `(condition-case nil (progn ,@body) (file-error nil)))

(defun nov-slurp (filename &optional parse-xml-p)
  "Return the contents of FILENAME.
If PARSE-XML-P is t, return the contents as parsed by libxml."
  (with-temp-buffer
    (insert-file-contents filename)
    (if parse-xml-p
        (libxml-parse-xml-region (point-min) (point-max))
      (buffer-string))))

(defun nov-mimetype-valid-p (directory)
  "Return t if DIRECTORY contains a valid EPUB mimetype file."
  (nov-ignore-file-errors
    (let ((filename (nov-make-path directory "mimetype")))
      (equal (nov-slurp filename) "application/epub+zip"))))

(defun nov-container-filename (directory)
  "Return the container filename for DIRECTORY."
  (let ((filename (nov-make-path directory "META-INF")))
    (nov-make-path filename "container.xml")))

(defun nov-container-content-filename (content)
  "Return the content filename for CONTENT."
  (let* ((query "container>rootfiles>rootfile[media-type='application/oebps-package+xml']")
         (node (esxml-query query content)))
    (esxml-node-attribute 'full-path node)))

(defun nov-container-valid-p (directory)
  "Return t if DIRECTORY holds a valid EPUB container."
  (let ((filename (nov-container-filename directory)))
    (when (and filename (file-exists-p filename))
      (let* ((content (nov-slurp filename t))
             (content-file (nov-container-content-filename content)))
        (when (and content content-file)
          (file-exists-p (nov-make-path directory content-file)))))))

(defun nov-epub-valid-p (directory)
  "Return t if DIRECTORY makes up a valid EPUB document."
  (and (nov-mimetype-valid-p directory)
       (nov-container-valid-p directory)))

(defun nov-content-version (content)
  "Return the EPUB version for CONTENT."
  (let* ((node (esxml-query "package" content))
         (version (esxml-node-attribute 'version node)))
    (when (not version)
      (error "Version not specified"))
    version))

(defun nov-content-unique-identifier-name (content)
  "Return the UUID name for CONTENT.
This is used in `nov-content-unique-identifier' to retrieve the
UUID."
  (let* ((node (esxml-query "package[unique-identifier]" content))
         (name (esxml-node-attribute 'unique-identifier node)))
    (when (not name)
      (error "Unique identifier name not specified"))
    name))

(defun nov-content-unique-identifier (content)
  "Return the UUID for CONTENT."
  (let* ((name (nov-content-unique-identifier-name content))
         (selector (format "package>metadata>identifier[id='%s']"
                           (regexp-quote name)))
         (id (car (esxml-node-children (esxml-query selector content)))))
    (when (not id)
      (error "Unique identifier not found by its name: %s" name))
    (intern id)))

;; NOTE: unique identifier is queried separately as identifiers can
;; appear more than once and only one of them can be the unique one
(defvar nov-required-metadata-tags '(title language)
  "Required metadata tags used for `nov-content-metadata'.")

(defvar nov-optional-metadata-tags
  '(contributor coverage creator date description format
    publisher relation rights source subject type)
  "Optional metadata tags used for 'nov-content-metadata'.")

(defun nov-content-metadata (content)
  "Return a metadata alist for CONTENT.
Required keys are 'identifier and everything in
`nov-required-metadata-tags', optional keys are in
`nov-optional-metadata-tags'."
  (let* ((identifier (nov-content-unique-identifier content))
         (candidates (mapcar (lambda (node)
                               (cons (esxml-node-tag node)
                                     (car (esxml-node-children node))))
                             (esxml-query-all "package>metadata>*" content)))
         (required (mapcar (lambda (tag)
                             (let ((candidate (cdr (assq tag candidates))))
                               (when (not candidate)
                                 ;; NOTE: this should ideally be a
                                 ;; warning, but `warn' is too obtrusive
                                 (message "Required metadatum %s not found" tag))
                               (cons tag candidate)))
                           nov-required-metadata-tags))
         (optional (mapcar (lambda (tag) (cons tag (cdr (assq tag candidates))))
                           nov-optional-metadata-tags)))
    (append `((identifier . ,identifier)) required optional)))

(defun nov-content-manifest (directory content)
  "Extract an alist of manifest files for CONTENT in DIRECTORY.
Each alist item consists of the identifier and full path."
  (mapcar (lambda (node)
            (-let [(&alist 'id id 'href href) (esxml-node-attributes node)]
              (cons (intern id)
                    (nov-make-path directory href))))
          (esxml-query-all "package>manifest>item" content)))

(defun nov-content-spine (content)
  "Extract a list of spine identifiers for CONTENT."
  (mapcar (lambda (node) (intern (esxml-node-attribute 'idref node)))
          (esxml-query-all "package>spine>itemref" content)))

(defun nov--content-epub2-files (content manifest files)
  (let* ((node (esxml-query "package>spine[toc]" content))
         (id (esxml-node-attribute 'toc node)))
    (when (not id)
      (error "EPUB 2 NCX ID not found"))
    (setq nov-toc-id (intern id))
    (let ((toc-file (assq nov-toc-id manifest)))
      (when (not toc-file)
        (error "EPUB 2 NCX file not found"))
      (cons toc-file files))))

(defun nov--content-epub3-files (content manifest files)
  (let* ((node (esxml-query "package>manifest>item[properties=nav]" content))
         (id (esxml-node-attribute 'id node)))
    (when (not id)
      (error "EPUB 3 <nav> ID not found"))
    (setq nov-toc-id (intern id))
    (let ((toc-file (assq nov-toc-id manifest)))
      (when (not toc-file)
        (error "EPUB 3 <nav> file not found"))
      (setq files (--remove (eq (car it) nov-toc-id) files))
      (cons toc-file files))))

(defun nov-content-files (directory content)
  "Create correctly ordered file alist for CONTENT in DIRECTORY.
Each alist item consists of the identifier and full path."
  (let* ((manifest (nov-content-manifest directory content))
         (spine (nov-content-spine content))
         (files (mapcar (lambda (item) (assq item manifest)) spine)))
    (if (version< nov-epub-version "3.0")
        (nov--content-epub2-files content manifest files)
      (nov--content-epub3-files content manifest files))))

(defun nov--walk-ncx-node (node depth)
  (let ((tag (esxml-node-tag node))
        (children (--filter (eq (esxml-node-tag it) 'navPoint)
                            (esxml-node-children node))))
    (cond
     ((eq tag 'navMap)
      (insert "<ol>\n")
      (mapc (lambda (node) (nov--walk-ncx-node node (1+ depth))) children)
      (insert "</ol>\n"))
     ((eq tag 'navPoint)
      (let* ((label-node (esxml-query "navLabel>text" node))
             (content-node (esxml-query "content" node))
             (href (esxml-node-attribute 'src content-node))
             (label (car (esxml-node-children label-node))))
        (when (not href)
          (error "Navigation point is missing href attribute"))
        (let ((link (format "<a href=\"%s\">%s</a>" href (or label href))))
          (if children
              (progn
                (insert (format "<li>\n%s\n<ol>\n" link))
                (mapc (lambda (node) (nov--walk-ncx-node node (1+ depth)))
                      children)
                (insert (format "</ol>\n</li>\n")))
            (insert (format "<li>\n%s\n</li>\n" link)))))))))

(defun nov-ncx-to-html (path)
  "Convert NCX document at PATH to HTML."
  (let ((root (esxml-query "navMap" (nov-slurp path t))))
    (with-temp-buffer
      (nov--walk-ncx-node root 0)
      (buffer-string))))


;;; UI

(defvar nov-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "g") 'nov-render-document)
    (define-key map (kbd "v") 'nov-view-source)
    (define-key map (kbd "V") 'nov-view-content-source)
    (define-key map (kbd "m") 'nov-display-metadata)
    (define-key map (kbd "n") 'nov-next-document)
    (define-key map (kbd "]") 'nov-next-document)
    (define-key map (kbd "p") 'nov-previous-document)
    (define-key map (kbd "[") 'nov-previous-document)
    (define-key map (kbd "t") 'nov-goto-toc)
    (define-key map (kbd "RET") 'nov-browse-url)
    (define-key map (kbd "<follow-link>") 'mouse-face)
    (define-key map (kbd "<mouse-2>") 'nov-browse-url)
    (define-key map (kbd "TAB") 'shr-next-link)
    (define-key map (kbd "M-TAB") 'shr-previous-link)
    (define-key map (kbd "<backtab>") 'shr-previous-link)
    (define-key map (kbd "SPC") 'nov-scroll-up)
    (define-key map (kbd "S-SPC") 'nov-scroll-down)
    (define-key map (kbd "DEL") 'nov-scroll-down)
    (define-key map (kbd "<home>") 'beginning-of-buffer)
    (define-key map (kbd "<end>") 'end-of-buffer)
    map))

(defun nov-clean-up ()
  "Delete temporary files of the current EPUB buffer."
  (when nov-temp-dir
    (let ((identifier (cdr (assq 'identifier nov-metadata)))
          (index (if (integerp nov-documents-index)
                     nov-documents-index
                   0)))
      (nov-save-place identifier index (point)))
    (nov-ignore-file-errors
     (delete-directory nov-temp-dir t))))

(defun nov-clean-up-all ()
  "Delete temporary files of all opened EPUB buffers."
  (dolist (buffer (buffer-list))
    (with-current-buffer buffer
      (when (eq major-mode 'nov-mode)
        (nov-clean-up)))))

(defun nov-external-url-p (url)
  "Return t if URL refers to an external document."
  (and (url-type (url-generic-parse-url url)) t))

(defun nov-url-filename-and-target (url)
  "Return a list of URL's filename and target."
  (setq url (url-generic-parse-url url))
  (list (url-filename url) (url-target url)))

(defun nov-insert-image (path)
  "Insert an image for PATH at point.
This function honors `shr-max-image-proportion' if possible."
  ;; adapted from `shr-rescale-image'
  (if (fboundp 'imagemagick-types)
      (let ((edges (window-inside-pixel-edges
                    (get-buffer-window (current-buffer)))))
        (insert-image
         (create-image path 'imagemagick nil
                       :ascent 100
                       :max-width (truncate (* shr-max-image-proportion
                                               (- (nth 2 edges)
                                                  (nth 0 edges))))
                       :max-height (truncate (* shr-max-image-proportion
                                                (- (nth 3 edges)
                                                   (nth 1 edges)))))))
    (insert-image (create-image path nil nil :ascent 100))))

(defvar nov-original-shr-tag-img-function
  (symbol-function 'shr-tag-img))

(defun nov-render-img (dom &optional url)
  "Custom <img> rendering function for DOM.
Uses `shr-tag-img' for external paths and `nov-insert-image' for
internal ones."
  (let ((url (or url (cdr (assq 'src (cadr dom))))))
    (if (nov-external-url-p url)
        ;; HACK: avoid hanging in an infinite loop when using
        ;; `cl-letf' to override `shr-tag-img' with a function that
        ;; might call `shr-tag-img' again
        (funcall nov-original-shr-tag-img-function dom url)
      (setq url (expand-file-name url))
      (nov-insert-image url))))

(defun nov-render-title (dom)
  "Custom <title> rendering function for DOM.
Sets `header-line-format' to a combination of the EPUB title and
chapter title."
  (let ((title (cdr (assq 'title nov-metadata)))
        (chapter-title (car (esxml-node-children dom))))
    (when (not chapter-title)
      (setq chapter-title '(:propertize "No title" face italic)))
    ;; this shouldn't happen for properly authored EPUBs
    (when (not title)
      (setq title '(:propertize "No title" face italic)))
    (setq header-line-format (list title ": " chapter-title))))

(defvar nov-shr-rendering-functions
  '(;; default function uses url-retrieve and fails on local images
    (img . nov-render-img)
    ;; titles are rendered *inside* the document by default
    (title . nov-render-title))
  "Alist of rendering functions used with `shr-render-region'.")

(defun nov-render-html ()
  "Render HTML in current buffer with shr."
  (run-hooks 'nov-pre-html-render-hook)
  (let (;; HACK: make buttons use our own commands
        (shr-map nov-mode-map)
        (shr-external-rendering-functions nov-shr-rendering-functions)
        (shr-use-fonts nov-variable-pitch)
        (shr-width nov-text-width))
    ;; HACK: `shr-external-rendering-functions' doesn't cover
    ;; every usage of `shr-tag-img'
    (cl-letf (((symbol-function 'shr-tag-img) 'nov-render-img))
      (shr-render-region (point-min) (point-max))))
  (run-hooks 'nov-post-html-render-hook))

(defun nov-render-document ()
  "Render the document referenced by `nov-documents-index'.
If the document path refers to an image (as determined by
`image-type-file-name-regexps'), an image is inserted, otherwise
the HTML is rendered with `nov-render-html-function'."
  (interactive)
  (let* ((document (aref nov-documents nov-documents-index))
         (id (car document))
         (path (cdr document))
         ;; HACK: this should be looked up in the manifest
         (imagep (--find (string-match-p (car it) path)
                         image-type-file-name-regexps))
         ;; NOTE: allows resolving image references correctly
         (default-directory (file-name-directory path))
         buffer-read-only)
    (erase-buffer)

    (cond
     (imagep
      (nov-insert-image path))
     ((and (version< nov-epub-version "3.0")
           (eq id nov-toc-id))
      (insert (nov-ncx-to-html path)))
     (t
      (insert (nov-slurp path))))

    (when (not imagep)
      (funcall nov-render-html-function))
    (goto-char (point-min))))

(defun nov-find-document (predicate)
  "Return first item in `nov-documents' PREDICATE is true for."
  (let ((i 0)
        done)
    (while (and (not done)
                (< i (length nov-documents)))
      (when (funcall predicate (aref nov-documents i))
        (setq done t))
      (setq i (1+ i)))
    (when done
      (1- i))))

(defun nov-goto-toc ()
  "Go to the TOC index and render the TOC document."
  (interactive)
  (let ((index (nov-find-document (lambda (doc) (eq (car doc) nov-toc-id)))))
    (when (not index)
      (error "Couldn't locate TOC"))
    (setq nov-documents-index index)
    (nov-render-document)))

(defun nov-view-source ()
  "View the source of the current document in a new buffer."
  (interactive)
  (find-file (cdr (aref nov-documents nov-documents-index))))

(defun nov-view-content-source ()
  "View the source of the content file in a new buffer."
  (interactive)
  (find-file nov-content-file))

(defun nov-display-metadata ()
  "View the metadata of the EPUB document in a new buffer."
  (interactive)
  (let ((buffer "*EPUB metadata*")
        (metadata nov-metadata)
        (version nov-epub-version))
    (with-current-buffer (get-buffer-create buffer)
      (special-mode)
      (let (buffer-read-only)
        (erase-buffer)
        (insert (format "EPUB Version: %s\n" version))
        (dolist (item metadata)
          (-let [(key . value) item]
            (insert (format "%s: " (capitalize (symbol-name key))))
            (if value
                (if (eq key 'description)
                    (let ((beg (point)))
                      (insert value)
                      (shr-render-region beg (point)))
                  (insert (format "%s" value)))
              (insert (propertize "None" 'face 'italic)))
            (insert "\n")))
        (goto-char (point-min))))
    (pop-to-buffer buffer)))

(defun nov-next-document ()
  "Go to the next document and render it."
  (interactive)
  (when (< nov-documents-index (1- (length nov-documents)))
    (setq nov-documents-index (1+ nov-documents-index))
    (nov-render-document)))

(defun nov-previous-document ()
  "Go to the previous document and render it."
  (interactive)
  (when (> nov-documents-index 0)
    (setq nov-documents-index (1- nov-documents-index))
    (nov-render-document)))

(defun nov-scroll-up (arg)
  "Scroll with `scroll-up' or visit next chapter if at bottom."
  (interactive "P")
  (if (>= (window-end) (point-max))
      (nov-next-document)
    (scroll-up arg)))

(defun nov-scroll-down (arg)
  "Scroll with `scroll-down' or visit previous chapter if at top."
  (interactive "P")
  (if (and (<= (window-start) (point-min))
           (> nov-documents-index 0))
      (progn
        (nov-previous-document)
        (goto-char (point-max)))
    (scroll-down arg)))

(defun nov-visit-relative-file (filename target)
  "Visit the document as specified by FILENAME and TARGET."
  (let* ((current-path (cdr (aref nov-documents nov-documents-index)))
         (directory (file-name-directory current-path))
         (path (file-truename (nov-make-path directory filename)))
         (index (nov-find-document
                 (lambda (doc) (equal path (file-truename (cdr doc)))))))
    (when (not index)
      (error "Couldn't locate document"))
    (setq nov-documents-index index)
    (let ((shr-target-id target))
      (nov-render-document))
    (when target
      (let ((pos (next-single-property-change (point-min) 'shr-target-id)))
        (when (not pos)
          (error "Couldn't locate target"))
        (goto-char pos)
        (recenter (1- (max 1 scroll-margin)))))))

;; adapted from `shr-browse-url'
(defun nov-browse-url (&optional mouse-event)
  "Follow an external url with `browse-url'.
Internal URLs are visited with `nov-visit-relative-file'."
  (interactive (list last-nonmenu-event))
  (mouse-set-point mouse-event)
  (let ((url (get-text-property (point) 'shr-url)))
    (when (not url)
      (user-error "No link under point"))
    (if (nov-external-url-p url)
        (browse-url url)
      (apply 'nov-visit-relative-file (nov-url-filename-and-target url)))))

(defun nov-saved-places ()
  "Retrieve saved places in `nov-save-place-file'."
  (when (and nov-save-place-file (file-exists-p nov-save-place-file))
    (with-temp-buffer
      (insert-file-contents-literally nov-save-place-file)
      (goto-char (point-min))
      (read (current-buffer)))))

(defun nov-saved-place (identifier)
  "Retrieve saved place for IDENTIFIER in `nov-saved-place-file'."
  (cdr (assq identifier (nov-saved-places))))

(defun nov-save-place (identifier index point)
  "Save place as identified by IDENTIFIER, INDEX and POINT.
Saving is only done if `nov-save-place-file' is set."
  (when nov-save-place-file
    (let* ((place `(,identifier (index . ,index)
                                (point . ,point)))
           (places (cons place (assq-delete-all identifier (nov-saved-places))))
           print-level
           print-length)
      (with-temp-file nov-save-place-file
        (insert (prin1-to-string places))))))

;;;###autoload
(define-derived-mode nov-mode special-mode "EPUB"
  "Major mode for reading EPUB documents"
  (add-hook 'kill-buffer-hook 'nov-clean-up nil t)
  (add-hook 'kill-emacs-hook 'nov-clean-up-all)
  (add-hook 'change-major-mode-hook 'nov-clean-up nil t)
  (when (not buffer-file-name)
    (error "EPUB must be associated with file"))
  (setq nov-temp-dir (make-temp-file "nov-" t ".epub"))
  (let ((exit-code (nov-unzip-epub nov-temp-dir buffer-file-name)))
    (when (not (integerp exit-code))
      (nov-clean-up)
      (error "EPUB extraction aborted by signal %s" exit-code))
    (when (not (zerop exit-code))
      (nov-clean-up)
      (error "EPUB extraction failed with exit code %d" exit-code)))
  (when (not (nov-epub-valid-p nov-temp-dir))
    (nov-clean-up)
    (error "Invalid EPUB file"))
  (let* ((content (nov-slurp (nov-container-filename nov-temp-dir) t))
         (content-file (->> (nov-container-content-filename content)
                            (nov-make-path nov-temp-dir)))
         (work-dir (file-name-directory content-file))
         (content (nov-slurp content-file t)))
    (setq nov-content-file content-file)
    (setq nov-epub-version (nov-content-version content))
    (setq nov-metadata (nov-content-metadata content))
    (setq nov-documents (->> (nov-content-files work-dir content)
                             (apply 'vector)))
    (setq nov-documents-index 0))
  (setq buffer-undo-list t)
  (set-visited-file-name nil t) ; disable autosaves and save questions
  (let ((place (nov-saved-place (cdr (assq 'identifier nov-metadata)))))
    (if place
        (let ((index (cdr (assq 'index place)))
              (point (cdr (assq 'point place))))
          (setq nov-documents-index index)
          (nov-render-document)
          (goto-char point))
      (nov-render-document))))

(provide 'nov)
;;; nov.el ends here
