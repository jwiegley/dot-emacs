;;; dircmp.el --- Compare and sync directories.

;; Copyright (C) 2012 Matt McClure

;; Author: Matt McClure -- http://matthewlmcclure.com
;; URL: https://github.com/matthewlmcclure/dircmp-mode
;; Version: 1
;; Keywords: unix, tools

;; dircmp-mode is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by the
;; Free Software Foundation, either version 3 of the License, or (at your
;; option) any later version.

;; dircmp-mode is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with dircmp-mode.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; Add to your Emacs startup file:
;;
;;    (load "/path/to/dircmp.el")
;;
;; Then:
;;
;;    M-x compare-directories RET dir1 RET dir2 RET
;;
;; The author uses dircmp-mode with git-diffall (https://github.com/thenigan/git-diffall) as follows:
;;
;;    git diffall -x /path/to/dircmp-mode/emacs-git-difftool.sh

;;; Code:

(defvar rsync-comparison-extended-width 11)
(defvar view-comparison-width 7) ;; TODO: Vary.

(define-derived-mode dircmp-mode
  fundamental-mode "DirCmp"
  "Major mode for comparing and syncing two directories.
\\{dircmp-mode-map}"
  (setq goal-column (+ view-comparison-width 2)))

;; Sorted with M-x sort-lines
(define-key dircmp-mode-map " " 'next-line)
(define-key dircmp-mode-map "+" 'toggle-compare-recursively)
(define-key dircmp-mode-map "1" 'toggle-include-present-only-in-dir1)
(define-key dircmp-mode-map "2" 'toggle-include-present-only-in-dir2)
(define-key dircmp-mode-map "<" 'dircmp-do-sync-dir2-to-dir1)
(define-key dircmp-mode-map "=" 'toggle-show-equivalent)
(define-key dircmp-mode-map ">" 'dircmp-do-sync-dir1-to-dir2)
(define-key dircmp-mode-map "G" 'toggle-compare-group)
(define-key dircmp-mode-map "\177" 'previous-line)
(define-key dircmp-mode-map "\C-m" 'dircmp-do-ediff)
(define-key dircmp-mode-map "a" 'toggle-compare-acls)
(define-key dircmp-mode-map "c" 'set-compare-content)
(define-key dircmp-mode-map "d" 'toggle-preserve-devices-and-specials)
(define-key dircmp-mode-map "g" 'recompare-directories)
(define-key dircmp-mode-map "m" 'toggle-compare-permissions)
(define-key dircmp-mode-map "n" 'next-line)
(define-key dircmp-mode-map "o" 'toggle-compare-owner)
(define-key dircmp-mode-map "p" 'previous-line)
(define-key dircmp-mode-map "q" 'dircmp-quit)
(define-key dircmp-mode-map "s" 'toggle-preserve-symlinks)
(define-key dircmp-mode-map "t" 'toggle-compare-times)
(define-key dircmp-mode-map "x" 'toggle-compare-extended-attributes)
(define-key dircmp-mode-map [mouse-2] 'dircmp-mouse-do-ediff)

(define-key dircmp-mode-map [menu-bar dircmp]
  (cons "DirCmp" (make-sparse-keymap "DirCmp")))
(define-key dircmp-mode-map [menu-bar dircmp dircmp-quit]
  '("Quit DirCmp" . dircmp-quit))
(define-key dircmp-mode-map [menu-bar dircmp separator-3]
  '(menu-item "--"))
(define-key dircmp-mode-map [menu-bar dircmp toggle-preserve-devices-and-specials]
  '(menu-item "Preserve devices and special files" toggle-preserve-devices-and-specials
              :button (:toggle . dircmp-preserve-devices-and-specials)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-preserve-symlinks]
  '(menu-item "Preserve symbolic links" toggle-preserve-symlinks
              :button (:toggle . dircmp-preserve-symlinks)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-compare-extended-attributes]
  '(menu-item "Compare extended attributes" toggle-compare-extended-attributes
              :button (:toggle . dircmp-compare-extended-attributes)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-compare-acls]
  '(menu-item "Compare ACLs" toggle-compare-acls
              :button (:toggle . dircmp-compare-acls)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-compare-times]
  '(menu-item "Compare times" toggle-compare-times
              :button (:toggle . dircmp-compare-times)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-compare-permissions]
  '(menu-item "Compare permissions" toggle-compare-permissions
              :button (:toggle . dircmp-compare-permissions)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-compare-group]
  '(menu-item "Compare group" toggle-compare-group
              :button (:toggle . dircmp-compare-group)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-compare-owner]
  '(menu-item "Compare owner" toggle-compare-owner
              :button (:toggle . dircmp-compare-owner)))
(define-key dircmp-mode-map [menu-bar dircmp set-compare-content]
  '("Compare content using..." . set-compare-content))
(define-key dircmp-mode-map [menu-bar dircmp separator-2]
  '(menu-item "--"))
(define-key dircmp-mode-map [menu-bar dircmp toggle-include-present-only-in-dir2]
  '(menu-item "Include files only present in dir2" toggle-include-present-only-in-dir2
              :button (:toggle . dircmp-include-present-only-in-dir2)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-include-present-only-in-dir1]
  '(menu-item "Include files only present in dir1" toggle-include-present-only-in-dir1
              :button (:toggle . dircmp-include-present-only-in-dir1)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-show-equivalent]
  '(menu-item "Show equivalent files" toggle-show-equivalent
              :button (:toggle . dircmp-show-equivalent)))
(define-key dircmp-mode-map [menu-bar dircmp toggle-compare-recursively]
  '(menu-item "Compare recursively" toggle-compare-recursively
              :button (:toggle . dircmp-compare-recursively)))
(define-key dircmp-mode-map [menu-bar dircmp separator-1]
  '(menu-item "--"))
(define-key dircmp-mode-map [menu-bar dircmp dircmp-do-sync-dir2-to-dir1]
  '("Sync from dir2 to dir1" . dircmp-do-sync-dir2-to-dir1))
(define-key dircmp-mode-map [menu-bar dircmp dircmp-do-sync-dir1-to-dir2]
  '("Sync from dir1 to dir2" . dircmp-do-sync-dir1-to-dir2))
(define-key dircmp-mode-map [menu-bar dircmp recompare-directories]
  '("Recompare directories" . recompare-directories))
(define-key dircmp-mode-map [menu-bar dircmp dircmp-do-ediff]
  '("Ediff files" . dircmp-do-ediff))

(defvar rsync-width-buffer " *dircmp-rsync-width*")
(defvar rsync-output-buffer " *dircmp-rsync-output*")
(defvar diff-output-buffer " *dircmp-diff-output*")
(defvar comparison-view-buffer "*DirCmp*")
(defcustom dircmp-show-equivalent nil "Show equivalent files")
(make-variable-buffer-local 'dircmp-show-equivalent)
(defun toggle-show-equivalent ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-show-equivalent (not dircmp-show-equivalent))))
(defcustom dircmp-compare-recursively t "Compare directories recursively")
(make-variable-buffer-local 'dircmp-compare-recursively)
(defun toggle-compare-recursively ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-compare-recursively (not dircmp-compare-recursively))))
(defcustom dircmp-preserve-symlinks t "Preserve symlinks when syncing")
(make-variable-buffer-local 'dircmp-preserve-symlinks)
(defun toggle-preserve-symlinks ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-preserve-symlinks (not dircmp-preserve-symlinks))))
(defcustom dircmp-compare-permissions t "Compare permissions")
(make-variable-buffer-local 'dircmp-compare-permissions)
(defun toggle-compare-permissions ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-compare-permissions (not dircmp-compare-permissions))))
(defcustom dircmp-compare-acls nil "Compare ACLs")
(make-variable-buffer-local 'dircmp-compare-acls)
(defun toggle-compare-acls ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-compare-acls (not dircmp-compare-acls))))
(defcustom dircmp-compare-extended-attributes nil "Compare extended attributes")
(make-variable-buffer-local 'dircmp-compare-extended-attributes)
(defun toggle-compare-extended-attributes ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-compare-extended-attributes (not dircmp-compare-extended-attributes))))
(defcustom dircmp-compare-times t "Compare times")
(make-variable-buffer-local 'dircmp-compare-times)
(defun toggle-compare-times ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-compare-times (not dircmp-compare-times))))
(defcustom dircmp-compare-group t "Compare groups")
(make-variable-buffer-local 'dircmp-compare-group)
(defun toggle-compare-group ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-compare-group (not dircmp-compare-group))))
(defcustom dircmp-compare-owner t "Compare owners")
(make-variable-buffer-local 'dircmp-compare-owner)
(defun toggle-compare-owner ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-compare-owner (not dircmp-compare-owner))))
(defcustom dircmp-preserve-devices-and-specials t "Preserve device files and special files")
(make-variable-buffer-local 'dircmp-preserve-devices-and-specials)
(defun toggle-preserve-devices-and-specials ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-preserve-devices-and-specials (not dircmp-preserve-devices-and-specials))))
(defcustom dircmp-include-present-only-in-dir1 t "Include files only present in dir1 in comparison view")
(make-variable-buffer-local 'dircmp-include-present-only-in-dir1)
(defun toggle-include-present-only-in-dir1 ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-include-present-only-in-dir1 (not dircmp-include-present-only-in-dir1))))
(defcustom dircmp-include-present-only-in-dir2 t "Include files only present in dir2 in comparison view")
(make-variable-buffer-local 'dircmp-include-present-only-in-dir2)
(defun toggle-include-present-only-in-dir2 ()
  (interactive)
  (with-current-buffer comparison-view-buffer
    (set 'dircmp-include-present-only-in-dir2 (not dircmp-include-present-only-in-dir2))))
(defcustom dircmp-compare-content "size" "Method for comparing file content"
  :type '(choice (const "size")
                 (const "checksum")
                 (const "byte by byte")
                 (const "ignore whitespace")
                 ;; (const "by file type") ; unimplemented
                 ))
(make-variable-buffer-local 'dircmp-compare-content)
(defun set-compare-content (method)
  (interactive "sCompare file content using: \n")
  (with-current-buffer comparison-view-buffer
    (set-variable 'dircmp-compare-content method)))

(defun compare-directories (adir1 adir2)
  (interactive "DDir1 directory: \nDDir2 directory: ")
  (get-buffer-create comparison-view-buffer)
  (set-buffer comparison-view-buffer)
  (dircmp-mode)
  (recompare-directories adir1 adir2))

(defun recompare-directories (&optional adir1 adir2)
  (interactive)
  (get-buffer-create rsync-output-buffer)
  (set-buffer rsync-output-buffer)
  (erase-buffer)
  (let ((normalized-dir1 (if adir1 (normalize-dir-string adir1) dir1))
        (normalized-dir2 (if adir2 (normalize-dir-string adir2) dir2)))
    (set (make-local-variable 'dir1) normalized-dir1)
    (set (make-local-variable 'dir2) normalized-dir2)
    (compare-with-rsync dir1 dir2)
    (refine-comparison-byte-by-byte)
    (refine-comparison-with-diff)
    (update-comparison-view dir1 dir2)))

(defun compare-with-rsync (adir1 adir2)
  (let ((args (append (list "rsync" nil rsync-output-buffer nil)
                      (rsync-comparison-options)
                      (list adir1 adir2))))
    (apply 'call-process args)))

(defun rsync-comparison-options ()
  (with-current-buffer comparison-view-buffer
    (append
     (list
      (concat
       "-ni"
       (if (or dircmp-show-equivalent
               (equal dircmp-compare-content "byte by byte")) "i")
       (if dircmp-compare-recursively "r" "d") 
       (if (equal dircmp-compare-content "checksum") "c")
       (if dircmp-preserve-symlinks "l")
       (if dircmp-compare-permissions "p")
       (if dircmp-compare-acls "A")
       (if dircmp-compare-extended-attributes "X")
       (if dircmp-compare-times "t")
       (if dircmp-compare-group "g")
       (if dircmp-compare-owner "o")
       (if dircmp-preserve-devices-and-specials "D")))
     (if (not dircmp-include-present-only-in-dir1) (list "--existing"))
     (if dircmp-include-present-only-in-dir2 (list "--delete")))))

(defun dircmp-line-number ()
  (1+ (count-lines 1 (line-beginning-position))))

(defun refine-comparison-byte-by-byte ()
  (if (equal (with-current-buffer comparison-view-buffer dircmp-compare-content) "byte by byte")
      (save-excursion
        (set-buffer rsync-output-buffer)
        (goto-char (point-min))
        (let ((lines (count-lines (point-min) (point-max))))
          (while (<= (dircmp-line-number) lines)
            (progn
              (if (and
                   (string-equal "f" (substring (comparison-on-current-rsync-line) 1 2))
                   (string-equal "." (substring (comparison-on-current-rsync-line) 2 3))
                   (string-equal "." (substring (comparison-on-current-rsync-line) 3 4)))
                  (let ((equivalent
                         (equal 0 (call-process
                                   "cmp" nil nil nil "-s" (path1-on-current-rsync-line) (path2-on-current-rsync-line)))))
                    (if (not equivalent)
                        (progn
                          (goto-char (+ (line-beginning-position) 2))
                          (delete-char 2)
                          (insert "c.")))))
              (forward-line)))))))

(defun refine-comparison-with-diff ()
  (if (equal (with-current-buffer comparison-view-buffer dircmp-compare-content) "ignore whitespace")
      (save-excursion
        (get-buffer-create diff-output-buffer)
        (get-buffer-create diff-output-buffer)
        (set-buffer diff-output-buffer)
        (erase-buffer)
        (set-buffer rsync-output-buffer)
        (goto-char (point-min))
        (let ((lines (count-lines (point-min) (point-max))))
          (while (<= (dircmp-line-number) lines)
            (if (or (string-equal "c" (substring (comparison-on-current-rsync-line) 2 3))
                    (string-equal "s" (substring (comparison-on-current-rsync-line) 3 4)))
                (progn
                  (set-buffer diff-output-buffer)
                  (erase-buffer)
                  (call-process
                   "diff" nil diff-output-buffer nil "-q" "-s" "-w" (path1-on-current-rsync-line) (path2-on-current-rsync-line))
                  (if (re-search-backward " are identical\n" nil t)
                      (progn
                        (set-buffer rsync-output-buffer)
                        (goto-char (+ (line-beginning-position) 2))
                        (delete-char 2)
                        (insert "..")))))
            (set-buffer rsync-output-buffer)
            (forward-line))))))

(defun normalize-dir-string (dir)
  (file-name-as-directory (expand-file-name dir)))

(defun update-comparison-view (adir1 adir2)
  (set-buffer rsync-output-buffer)
  (let ((rsync-output (buffer-string)))
    (switch-to-buffer comparison-view-buffer)
    (let ((line (dircmp-line-number)))
      (set 'buffer-read-only nil)
      (erase-buffer)
      (insert (format "Directory comparison:\n\nDir1: %s\nDir2: %s\n\n" adir1 adir2))
      (format-rsync-output rsync-output)
      (switch-to-buffer comparison-view-buffer)
      (insert """
Key:
    .: equivalent
    c: content differs
    1: only present in dir1
    2: only present in dir2
    t: timestamps differ
    p: permissions differ
    o: owner differs
    g: group differs
""")
      (set 'buffer-read-only t)
      (set 'line (if (< line 6) 6 line))
      (goto-char (point-min))
      (forward-line (- line 1))
      (if (> (- (line-end-position) (line-beginning-position)) goal-column) (forward-char goal-column)))))

(defun dircmp-do-ediff (&optional adir1 adir2)
  (interactive)
  (let* ((file-A (or adir1 (path1-on-current-view-line)))
         (file-B (or adir2 (path2-on-current-view-line)))
         (buf-A (or (get-file-buffer file-A) (find-file-noselect file-A)))
         (buf-B (or (get-file-buffer file-B) (find-file-noselect file-B))))
    (add-hook 'ediff-mode-hook (lambda () (setq default-directory "/")))
    (ediff-buffers buf-A buf-B)
    (add-hook 'ediff-quit-hook (lambda () (progn (switch-to-buffer comparison-view-buffer) (delete-other-windows))) t)))

(defun dircmp-mouse-do-ediff (event)
  ;; Lifted from dired-mouse-find-file-other-window
  (interactive "e")
  (let (window pos dir1-file dir2-file)
    (save-excursion
      (setq window (posn-window (event-end event))
            pos (posn-point (event-end event)))
      (if (not (windowp window))
          (error "No file chosen"))
      (set-buffer (window-buffer window))
      (goto-char pos)
      (setq dir1-file (path1-on-current-view-line))
      (setq dir2-file (path2-on-current-view-line)))
    (dircmp-do-ediff dir1-file dir2-file)))

(defun dircmp-do-sync-dir1-to-dir2 ()
  (interactive)
  (call-process "rsync" nil nil nil "-idlptgoD" "--delete"
                (directory-file-name (path1-on-current-view-line))
                (file-name-directory (directory-file-name (path2-on-current-view-line))))
  (recompare-directories))

(defun dircmp-do-sync-dir2-to-dir1 ()
  (interactive)
  (call-process "rsync" nil nil nil "-idlptgoD" "--delete"
                (directory-file-name (path2-on-current-view-line))
                (file-name-directory (directory-file-name (path1-on-current-view-line))))
  (recompare-directories))

(defun dircmp-quit ()
  (interactive)
  (if (y-or-n-p "Quit directory comparison? ")
      (progn
        (kill-buffer (get-buffer-create rsync-width-buffer))
        (kill-buffer (get-buffer-create rsync-output-buffer))
        (kill-buffer (get-buffer-create diff-output-buffer))
        (kill-buffer (get-buffer-create comparison-view-buffer)))))

(defvar computed-rsync-file-name-index nil)

(defun rsync-file-name-index ()
  (if computed-rsync-file-name-index
      computed-rsync-file-name-index
    (setq computed-rsync-file-name-index
          (save-excursion
            (with-current-buffer (get-buffer-create rsync-width-buffer)
              (let ((file (make-temp-file "")))
                (erase-buffer)
                ;; `rsync -niiId . .` ; search for ./
                (call-process "rsync" nil rsync-width-buffer nil "-nii" file file)
                (delete-file file)
                (goto-char (point-min))
                (search-forward (file-name-nondirectory file))
                (- (match-beginning 0) (line-beginning-position))))))))

(defun rsync-comparison-width ()
  (- (rsync-file-name-index) 1))

(defun file-on-current-rsync-line ()
  (save-excursion
    (switch-to-buffer rsync-output-buffer)
    (buffer-substring-no-properties (+ (line-beginning-position) (rsync-file-name-index)) (line-end-position))))

(defun comparison-on-current-rsync-line ()
  (save-excursion
    (switch-to-buffer rsync-output-buffer)
    (buffer-substring-no-properties (line-beginning-position) (+ (line-beginning-position) (rsync-comparison-width)))))

(defun file-on-current-view-line ()
  (save-excursion
    (switch-to-buffer comparison-view-buffer)
    (buffer-substring-no-properties (+ (line-beginning-position) 9) (line-end-position))))

(defun path1-on-current-rsync-line ()
  (save-excursion
    (switch-to-buffer rsync-output-buffer)
    (concat dir1 (file-on-current-rsync-line))))

(defun path2-on-current-rsync-line ()
  (save-excursion
    (switch-to-buffer rsync-output-buffer)
    (concat dir2 (file-on-current-rsync-line))))

(defun path1-on-current-view-line ()
  (save-excursion
    (switch-to-buffer rsync-output-buffer)
    (concat dir1 (file-on-current-view-line))))

(defun path2-on-current-view-line ()
  (save-excursion
    (switch-to-buffer rsync-output-buffer)
    (concat dir2 (file-on-current-view-line))))

(defun format-rsync-output (rsync-output)
  (progn
    (switch-to-buffer rsync-output-buffer)
    (goto-char (point-min))
    (while (> (- (line-end-position) (line-beginning-position)) (rsync-file-name-index))
      (let ((formatted-comparison (format-comparison (comparison-on-current-rsync-line)))
            (file (file-on-current-rsync-line)))
        (if (or
             (with-current-buffer comparison-view-buffer dircmp-show-equivalent)
             (not (equivalent formatted-comparison)))
            (progn
              (switch-to-buffer comparison-view-buffer)
              (insert (format "%8s %s\n" formatted-comparison file))
              (switch-to-buffer rsync-output-buffer)))
        (forward-line)))))

(defun equivalent (formatted-comparison)
  (not (string-match "[a-z0-9]" formatted-comparison)))

(defun format-comparison (rsync-comparison)
  (let ((padded-comparison
         (mapconcat
          (function (lambda (c) (format "%c" (if (equal ?\  c) ?\. c))))
          (if (< (length rsync-comparison) rsync-comparison-extended-width)
              (format (format "%%-%ds" rsync-comparison-extended-width) rsync-comparison)
            rsync-comparison) "")))
    (cond ((string-equal "*deleting" (substring padded-comparison 0 9))
           "2......")
          ((string-equal ">f+++++++" (substring padded-comparison 0 9))
           "1......")
          ((string-equal "c" (substring padded-comparison 0 1))
           "1......")
          ((or (string-equal "c" (substring padded-comparison 2 3))
               (string-equal "s" (substring padded-comparison 3 4)))
           (concat "c" (substring padded-comparison 4 (- rsync-comparison-extended-width 1))))
          (t
           (concat (substring padded-comparison 2 3) (substring padded-comparison 4 (- rsync-comparison-extended-width 1))))
          )))

(provide 'dircmp-mode)

;;; dircmp.el ends here
