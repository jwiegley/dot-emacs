;;; ipa.el --- In-place annotations

;; Copyright (C) 2007  Tamas Patrovics
;; Updated 2012  Ido Magal

;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 2, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;;; With this package you can add annotations to your files without
;;; modifying them. Each file can have multiple annotations at various
;;; buffer positions. The annotation texts are not parts of the files,
;;; they are stored separately.
;;;
;;; All annotations are stored in a common file, so searching
;;; annotations is trivial.
;;;
;;;
;;; Installation:
;;;
;;;   (require 'ipa)
;;;
;;;
;;; The following commands can be used:
;;;
;;;   ipa-insert   - insert annotation at point
;;;
;;;   ipa-edit     - edit the first annotation after point
;;;                  (with universal argument: before point)
;;;
;;;   ipa-next     - goes to the next annotation in the buffer
;;;
;;;   ipa-previous - goes to the previous annotation in the buffer
;;;
;;;   ipa-move     - move the first annotation after point
;;;                  (with universal argument: before point)
;;;
;;;   ipa-toggle   - hide/show annotations
;;;
;;;   ipa-show     - show all saved annotations for the current file
;;;                  (in the storage buffer you can press Enter on any 
;;;                   annotation to go to its location)
;;;
;;;   ipa-jump     - jump to any annotation with id completion
;;;                  
;;;                  Annotations can optionally have ids in their
;;;                  text with the following format: [id]annotation-text
;;;
;;;                  The id itself doesn't appear in the annotated
;;;                  buffer. It only serves the purpose of giving a
;;;                  unique id to the annotation, so that you can jump
;;;                  to it quickly.
;;;
;;;                  If an annotation has an id, but no other text
;;;                  then it is effectively the same as a usual
;;;                  bookmark in emacs.
;;;
;;;                  Only annotations appearing in `ipa-file' can be
;;;                  jumped to, so unsaved annotations does not count.
;;;                  If there are more annotations defined with the
;;;                  same id then the first one found in `ipa-file' is
;;;                  used.
;;;
;;;
;;; Annotations are saved when the file itself is saved. If the file
;;; is not modified annotations are saved immediately when
;;; added/changed.
;;;

;; Tested on Emacs 24.

;;; Changes by Ido Magal
;;
;;	- Created customization group 'ipa for easier customization.
;;
;;	- Added support for sidecar .ipa files ( annotations for file.txt are
;;		are	stored in file.txt.ipa
;;
;;	- Added support for above-line annotation (rubikitch)
;;
;;; Code:

;; User configuration

(defgroup ipa nil
  "In-place annotation."
  :version 0.1
  :group 'text)

(defcustom ipa-file "~/.ipa"
  "File where annotations are stored, but see also
  `ipa-file-function'"
  :type 'file
  :group 'ipa)

(defcustom ipa-file-function 'ipa-get-global-file
  "Function to get the name of the annotation storage file. By
  default it returns `ipa-file', but it can be used, for example,
  to use different storage files in each directory. See
  `ipa-get-directory-file'"
  :type 'function
  :group 'ipa)

(defcustom ipa-overlay-position "inline"
  "Determines where annotations are positioned. Options are
 'inline or 'above."
  :type '(choice
          (string :tag "inline" :value "inline")
          (string :tag "above" :value "above"))
  :group 'ipa)

(defcustom ipa-context-size 16
  "Length of before and after context of annotation position in
  characters used to reposition the annotation if the annotated
  file is changed behind Emacs's back."
  :group 'ipa)

(defcustom ipa-annotation-face 'highlight
  "Face for annotations."
  :type 'face
  :group 'ipa)

(defcustom ipa-file-face 'header-line
  "Face for header lines in the IpA buffer."
  :type 'face
  :group 'ipa)

;;----------------------------------------------------------------------

(defvar ipa-annotations-in-buffer nil)

(make-variable-buffer-local 'ipa-annotations-in-buffer)

(defvar ipa-annotation-display t)

(defconst ipa-line-continuation "|")

(defconst ipa-file-marker "\f")

(defconst ipa-file-regexp (concat "^" ipa-file-marker "\\s-*"))

(defconst ipa-annotation-id-regexp "\\s-*\\[\\(.+\\)?\\]\\(.*\\)")



(defvar ipa-pos-info-face '(face nil invisible t))

(defvar ipa-font-lock-keywords `((,(concat ipa-file-regexp
                                           "\\(.*\\)\n") . ipa-file-face)
                                 ("^|" . (0 ipa-annotation-face t))
                                 (ipa-font-lock-pos-info .
                                  ((1 ipa-pos-info-face t)
                                   (2 ipa-annotation-face t)))))


(define-derived-mode ipa-mode fundamental-mode "IPA"
  (set (make-local-variable 'font-lock-defaults) '(ipa-font-lock-keywords)))

(define-key ipa-mode-map (kbd "<return>") 'ipa-go-to-annotation)


(defvar ipa-overriding-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<left>") 'ipa-move-left)
    (define-key map (kbd "<right>") 'ipa-move-right)
    (define-key map (kbd "<up>") 'ipa-move-line-up)
    (define-key map (kbd "<down>") 'ipa-move-line-down)
    (define-key map (kbd "<prior>") 'ipa-move-page-up)
    (define-key map (kbd "<next>") 'ipa-move-page-down)
    (define-key map (kbd "<return>") 'ipa-move-finish)
    (define-key map (kbd "<escape>") 'ipa-move-cancel)
    (define-key map (kbd "h") 'ipa-move-help)
    map))

(defvar ipa-old-global-map nil)

(defvar ipa-overlay-being-moved nil)

(defvar ipa-original-position-of-overlay-being-moved nil)
 
(defun ipa-set-overlay-text-function()
  (cond
   ((string= ipa-overlay-position "inline") 'ipa-set-overlay-text-inline)
   ((string= ipa-overlay-position "above") 'ipa-set-overlay-text-above)))

(defun ipa-create-overlay-function()
  (cond
   ((string= ipa-overlay-position "inline") 'ipa-create-overlay-inline)
   ((string= ipa-overlay-position "above") 'ipa-create-overlay-above)))

(defun ipa-insert ()
 (interactive)
 (unless ipa-annotation-display
   (ipa-toggle))

 (let ((text (read-string "text: ")))
   (if (equal text  "")
       (message "Empty annotations are not inserted.")
       
     (funcall (ipa-create-overlay-function) (point) text)

     (if (ipa-get-buffer-file-name)
         (ipa-save-annotations-if-necessary)

       (message "Annotations in this buffer will be saved only if you save the buffer as a file.")))))
 

(defun ipa-edit (&optional arg)
 (interactive "P")
 (unless ipa-annotation-display
   (ipa-toggle))

 (let ((annotation (if arg
                       (ipa-previous)
                     (ipa-next))))
   (if annotation
       (let* ((text (read-string "text (empty to remove): " (cdr  annotation))))
         (if (equal text "")
             (progn
               (delete-overlay (car annotation))
               (setq ipa-annotations-in-buffer
                     (delq annotation ipa-annotations-in-buffer))
               (message "Deleted annotation."))

           (funcall (ipa-set-overlay-text-function) (car annotation) text)
           (setcdr annotation text)
           (message "Updated annotation."))

         (ipa-save-annotations-if-necessary t)))))


(defun ipa-move (&optional arg)
 (interactive "P")
 (unless ipa-annotation-display
   (ipa-toggle))

 (let ((annotation (if arg
                       (ipa-previous)
                     (ipa-next))))
   (when annotation
     (setq ipa-overlay-being-moved (car annotation))
     (setq ipa-original-position-of-overlay-being-moved
           (overlay-start ipa-overlay-being-moved))
     (setq ipa-old-global-map global-map)
     (use-global-map ipa-overriding-map)
     (setq overriding-terminal-local-map ipa-overriding-map)
     (add-hook 'post-command-hook 'ipa-show-help))))


(defun ipa-show-help ()
  (message (substitute-command-keys
            (concat "Press \\[ipa-move-help] for help, "
                    "\\[ipa-move-cancel] to cancel."))))


(defun ipa-move-cancel ()
  (interactive)
  (goto-char ipa-original-position-of-overlay-being-moved)
  (move-overlay ipa-overlay-being-moved (point) (point))
  (ipa-cleanup)
  (message "Moving of annotation is canceled."))


(defun ipa-move-help ()
  (interactive)
  (tooltip-show (substitute-command-keys "\\{ipa-overriding-map}")))


(defun ipa-move-finish ()
  (interactive)
  (ipa-cleanup)
  (ipa-sort-overlays)
  (ipa-save-annotations-if-necessary))


(defun ipa-cleanup ()
  (use-global-map ipa-old-global-map)
  (setq overriding-terminal-local-map nil)
  (remove-hook 'post-command-hook 'ipa-show-help))


(defun ipa-move-left ()
  (interactive)
  (ipa-move-overlay 'backward-char))


(defun ipa-move-right ()
  (interactive)
  (ipa-move-overlay 'forward-char))


(defun ipa-move-line-up ()
  (interactive)
  (ipa-move-overlay 'previous-line))


(defun ipa-move-line-down ()
  (interactive)
  (ipa-move-overlay 'next-line))


(defun ipa-move-page-up ()
  (interactive)
  (ipa-move-overlay 'scroll-down))


(defun ipa-move-page-down ()
  (interactive)
  (ipa-move-overlay 'scroll-up))


(defun ipa-move-overlay (movefunc)
  (condition-case nil
      (funcall movefunc)
    (beginning-of-buffer (goto-char (point-min)))
    (end-of-buffer (goto-char (point-max))))

  (move-overlay ipa-overlay-being-moved (point) (point)))



(defun ipa-next ()
  (interactive)
  (unless ipa-annotation-display
    (ipa-toggle))

  (let ((annotations ipa-annotations-in-buffer)
        annotation)
    (while (and annotations
                (not annotation))
      (if (> (overlay-start (car (car annotations))) (point))
          (setq annotation (car annotations))
        (pop annotations)))

    (if (not annotation)
        (message "No annotations found after point.")

      (goto-char (overlay-start (car annotation)))
      (ipa-warn-if-annotation-is-empty (car annotation)))

    annotation))


(defun ipa-previous ()
  (interactive)
  (unless ipa-annotation-display
    (ipa-toggle))

  (let ((annotations ipa-annotations-in-buffer)
        (continue t)
        annotation)
    (while (and annotations continue)
      (if (> (overlay-start (car (car annotations))) (point))
          (setq continue nil)
      
        (setq annotation (pop annotations))))

    (if (not annotation)
        (message "No annotations found before point.")

      (goto-char (1- (overlay-start (car annotation))))
      (ipa-warn-if-annotation-is-empty (car annotation)))

    annotation))


(defun ipa-warn-if-annotation-is-empty (overlay)
  (if (equal (overlay-get overlay 'before-string) "")
      (message "The text of this annotation is empty.")))


(defun ipa-toggle (&optional arg)
    (interactive "P")
    (setq ipa-annotation-display (if arg
                                     (> (prefix-numeric-value arg) 0)
                                   (not ipa-annotation-display)))    
    (if ipa-annotation-display
        (dolist (buffer (buffer-list))
          (with-current-buffer buffer
            (dolist (annotation ipa-annotations-in-buffer)
              (funcall (ipa-set-overlay-text-function) (car annotation) (cdr annotation))
              (message "Annotations are shown."))))

      (dolist (buffer (buffer-list))
        (with-current-buffer buffer
          (dolist (annotation ipa-annotations-in-buffer)
            (funcall (ipa-set-overlay-text-function) (car annotation) "")
            (message "Annotations are hidden."))))))


(defun ipa-show ()
  (interactive)
  (if (not (ipa-get-buffer-file-name))
      (message "This buffer has no associated file.")

    (let ((filename (ipa-get-buffer-file-name)))
      (with-current-buffer (ipa-find-storage-file)
        (goto-char (point-min))
        (if (re-search-forward (concat ipa-file-regexp
                                       filename "\n")
                               nil t)
            (switch-to-buffer (current-buffer))

          (message "No annotations found for file."))))))


(defun ipa-save-annotations-in-buffer (&optional even-if-empty)
  (when (or ipa-annotations-in-buffer
            even-if-empty)
    (let ((filename (ipa-get-buffer-file-name))
          (buffer (current-buffer))
          (annotations ipa-annotations-in-buffer))
      (with-current-buffer (ipa-find-storage-file)
        (save-excursion
          (goto-char (point-min))
      
          (unless (re-search-forward (concat ipa-file-regexp
                                             filename "\n")
                                     nil t)
            (goto-char (point-max))
            (insert ipa-file-marker " " filename "\n"))

          (let ((start (point)))
            (if (re-search-forward ipa-file-regexp nil t)
                (beginning-of-line)
              (goto-char (point-max)))
            (delete-region start (point)))

          (if annotations
              (dolist (annotation annotations)
                (let* ((pos (overlay-start (car annotation)))
                       (pos-info
                        (with-current-buffer buffer
                          (list 'pos pos
                                'before (if (>= (- pos (point-min))
                                                ipa-context-size)
                                            (buffer-substring-no-properties
                                             (- pos ipa-context-size) pos))
                                'after (if (>= (- (point-max) pos)
                                               ipa-context-size)
                                           (buffer-substring-no-properties
                                            pos (+ pos ipa-context-size)))))))
                  (insert (let ((print-escape-newlines t))
                            (prin1-to-string pos-info))
                          ":"
                          (replace-regexp-in-string
                           "\n" (concat "\n" ipa-line-continuation)
                           (cdr annotation))
                          "\n\n")))

            ;; delete header
            (let ((end (point)))
              (forward-line -1)
              (delete-region (point) end)))

          (save-buffer)
          (message "Annotations saved."))))))


(add-hook 'after-save-hook 'ipa-save-annotations-in-buffer)

     
(defun ipa-load-annotations-into-buffer ()
  (let ((filename (ipa-get-buffer-file-name))
        (buffer (current-buffer)))
    (if (ipa-find-storage-file-p) 
    (with-current-buffer (ipa-find-storage-file)
      (save-excursion
        (goto-char (point-min))
        (if (re-search-forward (concat ipa-file-regexp filename "\n") 
                               nil t)
            (let ((end (save-excursion
                         (if (re-search-forward ipa-file-regexp nil t)
                             (line-beginning-position)
                           (point-max)))))
              (with-current-buffer buffer
                (setq ipa-annotations-in-buffer nil))

              (let (text pos)
                (while (< (point) end)
                  (if (and (not (looking-at ipa-line-continuation))
                           text)
                      (with-current-buffer buffer
                        (funcall (ipa-create-overlay-function) pos text)
                        (setq text nil)
                        (setq pos nil)))

                  (cond ((let ((pos-info (ipa-get-pos-info)))
                           (when pos-info
                             (let ((after (plist-get pos-info 'after))
                                   (before (plist-get pos-info 'before)))
                               (with-current-buffer buffer
                                 (save-excursion
                                   ;; using the same algorithm as bookmarks
                                   (goto-char (plist-get pos-info 'pos))

                                   (if (and after
                                            (search-forward after nil t))
                                       (goto-char (match-beginning 0)))
                                   (if (and before 
                                            (search-backward before nil t))
                                       (goto-char (match-end 0)))

                                   (setq pos (point)))))

                             (if (looking-at ":\\(.+\\)")
                                 (setq text (match-string 1))
                               (error "Annotation storage format error"))

                             ;; making it explicit
                             t)))

                        ((looking-at ipa-line-continuation)
                         (setq text 
                               (concat text "\n"
                                       (buffer-substring (1+ (point))
                                                         (line-end-position)))))

                        (t
                         'skip))

                  (forward-line 1)))

              (message "Resaving annotations so that positions are updated...")
              (with-current-buffer buffer
                (ipa-save-annotations-in-buffer))
              
              (message "Annotations loaded."))))))))

(add-hook 'find-file-hook 'ipa-load-annotations-into-buffer)
(add-hook 'dired-after-readin-hook 'ipa-load-annotations-into-buffer)


(defun ipa-get-pos-info ()
  (and (looking-at "(")
       (read (current-buffer))))

(defun ipa-save-annotations-if-necessary (&optional even-if-empty)
  (if (and (ipa-get-buffer-file-name)
           (not (buffer-modified-p)))
      (ipa-save-annotations-in-buffer even-if-empty)))

;; OVERLAY ABOVE THE LINE

 (defun string-repeat (str n)
   (let ((retval ""))
     (dotimes (i n)
       (setq retval (concat retval str)))
     retval))
 
 (defun ipa-set-overlay-text-above (overlay text)
   (if (string-match ipa-annotation-id-regexp text)
       (setq text (match-string 2 text)))
  (save-excursion
    (let ((ipa-indent-level (current-indentation)))
    (beginning-of-line)
    (overlay-put overlay 'before-string
                 (if (equal text "") ""
    	   (propertize
    	    (concat
    	     (string-repeat " " ipa-indent-level) "* " text "\n")
    	    'face ipa-annotation-face))))))

(defun ipa-create-overlay-above (pos text)
  (save-excursion
    (goto-char pos)
    (setq pos (point-at-bol))
    (let ((overlay (make-overlay pos pos nil t nil)))
     (funcall (ipa-set-overlay-text-function) overlay text)
     (push (cons overlay text) ipa-annotations-in-buffer)
     (ipa-sort-overlays))))

(defun ipa-set-overlay-text-inline (overlay text)
  (if (string-match ipa-annotation-id-regexp text)
      (setq text (match-string 2 text)))
  (overlay-put overlay 'before-string
               (if (equal text "")
                   ""
                 (propertize (concat "[" text "]") 'face ipa-annotation-face))))

(defun ipa-create-overlay-inline (pos text)
  (let ((overlay (make-overlay pos pos nil t nil)))
    (funcall (ipa-set-overlay-text-function) overlay text)
    (push (cons overlay text) ipa-annotations-in-buffer)
    (ipa-sort-overlays)))

(defun ipa-sort-overlays ()
  (setq ipa-annotations-in-buffer
        (sort ipa-annotations-in-buffer
              (lambda (first second)
                (< (overlay-start (car first))
                   (overlay-start (car second)))))))

(defun ipa-find-storage-file ()
  (if (funcall ipa-file-function)
      (with-current-buffer (find-file-noselect (funcall ipa-file-function))
        (ipa-mode)
        (current-buffer))))

(defun ipa-find-storage-file-p ()
  (if (funcall ipa-file-function)
      (file-exists-p (funcall ipa-file-function))))

  
(defun ipa-get-global-file ()
  ipa-file)

(defun ipa-get-sidecar-file ()
  (let ((current-file (ipa-get-buffer-file-name)))
    (if (and current-file (not (string= (file-name-extension current-file) "ipa")))
        (concat (if (file-directory-p current-file)
                    current-file
                  current-file)
                ".ipa"))))

(defun ipa-get-directory-file ()
  (let ((current-file (ipa-get-buffer-file-name)))
    (if current-file
        (concat (if (file-directory-p current-file)
                    current-file
                  (file-name-directory current-file))
                (file-name-nondirectory ipa-file)))))


(defun ipa-go-to-annotation ()
  (interactive)
  (cond ((save-excursion
           (beginning-of-line)
           (looking-at (concat ipa-file-regexp "\\(.*\\)")))
         (unless ipa-annotation-display
           (ipa-toggle))
         (find-file (match-string 1)))

        ((let ((pos-info (save-excursion
                           (beginning-of-line)
                           (ipa-get-pos-info))))
           (when pos-info
             (save-excursion
               (if (not (re-search-backward ipa-file-regexp nil t))
                   (error "Containing file header is not found")

                 (ipa-go-to-annotation)
                 (goto-char (plist-get pos-info 'pos))
                 t)))))

        ((save-excursion
           (beginning-of-line)
           (looking-at ipa-line-continuation))
         (save-excursion
            (if (re-search-backward "^(" nil t)
                (ipa-go-to-annotation)
              (error "Containing annotation is not found"))))

        (t
         (message "There is nothing on the current line."))))


(defun ipa-font-lock-pos-info (limit)
  (when (re-search-forward "^(" limit t)
    (beginning-of-line)
    (let ((sexp-start (point))
          sexp-end colon-end)
      (forward-sexp)
      (setq sexp-end (point))
      (forward-char)
      (setq colon-end (point))
      (set-match-data (list sexp-start ;; whole
                            colon-end
                            sexp-start ;; sexp
                            sexp-end
                            sexp-end ;; colon
                            colon-end)))
    t))


(defun ipa-jump ()
  (interactive)
  (with-current-buffer (ipa-find-storage-file)
    (save-excursion
      (goto-char (point-min))
      (let (ids)        
        (while (re-search-forward "^(" nil t)
          (backward-char)
          (forward-sexp)
          (if (looking-at (concat ":" ipa-annotation-id-regexp))
              (let ((id (match-string-no-properties 1)))
                (unless (some (lambda (id-info)
                                (equal (car id-info) id))
                              ids)
                  (push (cons id (point)) ids)))))

        (if ids
            (let ((selected (completing-read "Jump to annotation: " ids nil t)))
              (unless (equal selected "")
                (goto-char (assoc-default selected ids))
                (ipa-go-to-annotation)))

          (message "There are no annotations with ids."))))))


(defun ipa-get-buffer-file-name ()
  (let ((name (or (buffer-file-name)
                  (save-excursion
                    (goto-char (point-min))
                    (dired-current-directory)))))
    (if name
        (file-truename name))))


(provide 'ipa)
;;; ipa.el ends here
