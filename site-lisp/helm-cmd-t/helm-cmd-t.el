;;; helm-cmd-t.el --- cmd-t style completion

;; this file is not part of Emacs

;; Copyright (C) 2011, 2012 Le Wang
;; Author: Le Wang
;; Maintainer: Le Wang
;; Description: cmd-t style completion of files in repository
;; Author: Le Wang
;; Maintainer: Le Wang

;; Created: Sat Nov  5 16:42:32 2011 (+0800)
;; Version: 0.1
;; URL: https://github.com/lewang/helm-cmd-t
;; Keywords: helm project-management completion convenience cmd-t textmate
;; Compatibility:

;;; Installation:

;; 1. install `helm' from github
;;
;; 2. clone the `helm-cmd-t' repository to "~/.emacs.d/helm-cmd-t"
;;
;; 3. add to your config
;;
;;      (push "~/.emacs.d/helm-cmd-t" load-path)
;;      (require 'helm-config)
;;      (require 'helm-cmd-t)
;;      (global-set-key (kbd "M-t") 'helm-cmd-t)
;;
;; 4. additional optional helm settings to make helm more responsive.
;;
;;      (setq helm-ff-lynx-style-map nil
;;            helm-input-idle-delay 0.1
;;            helm-idle-delay 0.1
;;      )
;;
;; 5. have a look at helm-C-x-b.el for more examples of how to use the
;;    `helm-cmd-t' source to craft your own master file chooser.
;;
;; 6. read the self-documenting code for additional configuration options.
;;


;;; Commentary:

;; This package provides a helm source for repository (git, hg, etc) based
;; file selection.  The emphasis is on fast file-name completion.  The concept
;; of a "respository" is configurable through `helm-cmd-t-repo-types'.
;;
;; Each repository is cached for fast access (see
;; `helm-cmd-t-cache-threshhold'), and in the future, options will be
;; available to interact with the repository (i.e. grep, etc).
;;
;; `helm-cmd-t' is the simple predefined command that opens a file in the
;; current repository, however, it's highly recommended that you add a helm
;; source like recentf that keeps track of recent files you've worked with.
;; This way, you don't have to worry about your respository cache being out of
;; sync.  See "helm-C-x-b.el" for an example of a custom drop-in
;; replacement for `switch-to-buffer' or "C-x b".
;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 3, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Code:

(eval-when-compile (require 'cl))


(require 'helm-config)
(require 'helm-files)
(require 'helm-grep)

(declare-function helm-cmd-t-dumb-glob-to-regexp "helm-cmd-t-find")
(declare-function helm-cmd-t-insert-tree-1 "helm-cmd-t-find")

(defcustom helm-cmd-t-cache-threshhold 1000
  "If a repo has more entries than this value it will be cached.

`nil' to disable caching completely.

Alternatively, this can be a function that takes three parameters:

    repository-type
    repo-root
    entries

It should return nil to stop caching.
"
  :group 'helm-command
  :type 'sexp)

(defcustom helm-cmd-t-default-repo nil
  "A path that points to a default repo root.

Can be a string or function that returns a string.

If the current file does not belong to a repo then this path is used.

"
  :group 'helm-command
  :type 'string)

(defcustom helm-cmd-t-find-prunes '("SCCS" "RCS" "CVS" "MCVS" ".svn" ".git" ".hg" ".bzr" "_MTN" "_darcs" "{arch}")
  "list used to prune \"find\" search.

see: `grep-find-ignored-directories' for inspiration"
  :group 'helm-command
  :type 'list)

(defcustom helm-cmd-t-find-ignored-files (nconc '("#*#" ".#*" "*.o" "*~" "*.bin" "*.lbin" "*.so" "*.a" "*.ln" "*.blg" "*.bbl" "*.elc" "*.lof" "*.glo" "*.idx" "*.lot" "*.fmt" "*.tfm" "*.class" "*.fas" "*.lib" "*.mem" "*.x86f" "*.sparcf" "*.dfsl" "*.pfsl" "*.d64fsl" "*.p64fsl" "*.lx64fsl" "*.lx32fsl" "*.dx64fsl" "*.dx32fsl" "*.fx64fsl" "*.fx32fsl" "*.sx64fsl" "*.sx32fsl" "*.wx64fsl" "*.wx32fsl" "*.fasl" "*.ufsl" "*.fsl" "*.dxl" "*.lo" "*.la" "*.gmo" "*.mo" "*.toc" "*.aux" "*.cp" "*.fn" "*.ky" "*.pg" "*.tp" "*.vr" "*.cps" "*.fns" "*.kys" "*.pgs" "*.tps" "*.vrs" "*.pyc" "*.pyo")
                                                 helm-cmd-t-find-prunes)
  "list of file extensions which should be ignored.

see `grep-find-ignored-files' for inspiration."
  :group 'helm-command
  :type 'list)

(defvar helm-cmd-t-data nil
  "data only relevant in helm source buffer.")

(defvar helm-cmd-t-find-command "find"
  "command to execute to get list of files it should be some variant of the Unix `find' command.")


(defvar helm-cmd-t-repo-types
  `(("git"         ".git"           "cd %d && git --no-pager ls-files --full-name")
    ("hg"          ".hg"            "cd %d && hg manifest")
    ("bzr"         ".bzr"           "cd %d && bzr ls --versioned")
    ("perforce"    ".perforce"      helm-cmd-t-get-find)
    ("dir-locals"  ".dir-locals.el" helm-cmd-t-get-find)
    (""            ""               helm-cmd-t-get-find))
  "root types supported.
this is an alist of (type cookie format-string).

\"%d\" is replaced with the project root in the format-string.

format string can also be symbol that takes:

    repo-root

as its parameter. ")

(defvar helm-cmd-t-anti-cookie ".emacs-helm-no-spider"
  "Marker file that disqualifies a directory from being considered a repo.")

(defvar helm-cmd-t-source-buffer-format
  " *helm-cmd-t source - [%s]*")

(defvar helm-cmd-t-header-format
  "[%r] (%t %l %a)"
  "format for project header
  %r - project root
  %t - type of repo
  %a - age of cache
  %l - line count")

;;; helm delays source initialization
(setq helm-source-buffers-list (or helm-source-buffers-list
                                  (helm-make-source "Buffers" 'helm-source-buffers)))

(defun helm-cmd-t-root (&optional buff)
  "return repo root of buffer as string"
  (with-current-buffer (or buff
                           (and helm-alive-p
                                helm-current-buffer)
                           (current-buffer))
    (cdr (helm-cmd-t-root-data))))

(defun helm-cmd-t-get-repo-root (dir)
  "return first ancestor that has any file in files
return (<repo type> . <root.>)"
  (if (null dir)
      nil)
  (let (best-root
        best-type
        cookie
        root)
    (dolist (cookie-data helm-cmd-t-repo-types)
      (setq cookie (nth 1 cookie-data)
            root   dir)
      (loop while (and (setq root (helm-cmd-t-locate-dominating-file root cookie))
                       (file-exists-p (expand-file-name helm-cmd-t-anti-cookie root))
                       (setq root (expand-file-name ".." root))))
      (when root
        (if (> (length root) (length best-root))
            (setq best-root root
                  best-type (nth 0 cookie-data)))))
    (when best-root
      (cons best-type best-root))))

(defun helm-cmd-t-locate-dominating-file (file name)
  (if (zerop (length name))
      nil
    (locate-dominating-file file name)))

(defun helm-cmd-t-root-data (&optional file no-default)
  "Get repo directory of file.
return (<repo type> . <root>)

if NO-DEFAULT is specified, don't look for the default.

return NIL if no root found.

If `helm-cmd-t-data' is defined and no parameters are
specified, then it is used to construct the root-data. "
  (if (and (null file)
         (null no-default)
         helm-cmd-t-data)
      (cons (cdr (assq 'repo-type helm-cmd-t-data))
            (cdr (assq 'repo-root helm-cmd-t-data)))
    (setq file (or file
                   default-directory))
    (or (helm-cmd-t-get-repo-root file)
        (let ((default (when (and (null no-default)
                                  helm-cmd-t-default-repo)
                         (file-name-as-directory (if (functionp helm-cmd-t-default-repo)
                                                     (funcall helm-cmd-t-default-repo)
                                                   helm-cmd-t-default-repo)))))
          (and default
               (helm-cmd-t-get-repo-root default))))))

(defun helm-cmd-t-format-age (age)
  "convert age in float to reasonable time explanation"
  (cond ((= age 0)
         "not cached")
        ((< age 3600)
         (format "cached %i min ago" (ceiling (/ age 60))))
        (t
         (format "cached %.1f hours ago" (/ age 3600)))))

(defun helm-cmd-t-format-lines (lines)
  "convert lines to reasonable presentation"
  (cond ((= lines 0)
         "")
        ((< lines 1000)
         (format "%s files" lines))
        (t
         (format "%.1fk files" (/ lines 1000.0)))))

(defun helm-cmd-t-format-title (data)
  "format header line according to `helm-cmd-t-header-format'"
  (let* ((repo-root (cdr (assq 'repo-root data)))
         (repo-type (cdr (assq 'repo-type data)))
         (cached-p (cdr (assq 'cached-p data)))
         (age (if cached-p
                  (- (float-time) (cdr (assq 'time-stamp data)))
                0))
         (age-str (helm-cmd-t-format-age age))
         (lines (helm-cmd-t-format-lines
                 (cdr (assq 'lines data)))))
    (setq repo-type (if (zerop (length repo-type))
                        "dir"
                      (concat repo-type " repo")))
    (format-spec helm-cmd-t-header-format (format-spec-make ?r repo-root
                                                            ?t repo-type
                                                            ?a age-str
                                                            ?l lines))))
(defun helm-cmd-t-transform-candidates (candidates source)
  "convert each candidate to cons of (disp . real)"
  (loop with root = (cdr (assq 'repo-root
                               (buffer-local-value 'helm-cmd-t-data
                                                   (helm-candidate-buffer))))
        for i in candidates
        for abs = (expand-file-name i root)
        for disp = i
        collect (cons (propertize disp 'face 'helm-ff-file) abs)))

(defun helm-cmd-t-cache-p (line-count repo-type repo-root)
  (cond ((functionp helm-cmd-t-cache-threshhold)
         (not (funcall helm-cmd-t-cache-threshhold repo-type repo-root line-count)))
        ((numberp helm-cmd-t-cache-threshhold)
         (>= line-count helm-cmd-t-cache-threshhold))
        ((not helm-cmd-t-cache-threshhold))))

(defun helm-cmd-t-get-create-source (repo-root-data &optional skeleton)
  "Get cached source or create new one.
SKELETON is used to ensure a repo is listed without doing any
extra work to laod it. This can be used to ensure the 'current'
repo is always listed when selecting repos."
  (let* ((repo-root (cdr repo-root-data))
         (repo-type (car repo-root-data))
         (source-buffer-name (helm-cmd-t-get-source-buffer-name repo-root))
         (candidate-buffer (get-buffer-create source-buffer-name))
         (data (buffer-local-value 'helm-cmd-t-data candidate-buffer))
         (my-source (when (cdr (assq 'cached-p data))
                        (cdr (assq 'helm-source data)))))
    (or my-source
        (with-current-buffer candidate-buffer
          (erase-buffer)
          (setq default-directory (file-name-as-directory repo-root))
          (unless skeleton
           (helm-cmd-t-insert-listing repo-type repo-root))
          (let* ((lines (count-lines (point-min) (point-max)))
                 (new-data (list (cons 'repo-root repo-root)
                                 (cons 'repo-type repo-type)
                                 (cons 'time-stamp (float-time))
                                 (cons 'lines lines)
                                 (cons 'cached-p (if skeleton nil
                                                  (helm-cmd-t-cache-p lines repo-type repo-root))))))
            (setq my-source `((name . ,(format "[%s]" (abbreviate-file-name repo-root)))
                              (header-name . (lambda (_)
                                               (helm-cmd-t-format-title (quote ,new-data))))
                              (init . (lambda ()
                                        (helm-candidate-buffer ,candidate-buffer)))
                              (candidates-in-buffer)
                              (keymap . ,helm-generic-files-map)
                              (filtered-candidate-transformer . helm-cmd-t-transform-candidates)
                              (action-transformer helm-transform-file-load-el)
                              (action . ,(helm-actions-from-type-file))
                              ;; not for helm, but for lookup if needed
                              (candidate-buffer . ,candidate-buffer)))
            (push (cons 'helm-source my-source) new-data)
            (set (make-local-variable 'helm-cmd-t-data) new-data))
          my-source))))

(defun helm-cmd-t-get-create-source-dir (dir)
  "create a source from DIR, coercing if necessary."
  (helm-cmd-t-get-create-source (helm-cmd-t-make-root dir)))

(defun helm-cmd-t-make-root (dir)
  "If DIR is a natural repo root, return its data.

Else, force DIR to be a blank repo type.

This is a convenience function for external libraries."
  (unless (file-directory-p dir)
    (error (format "\"%s\" is not a directory." dir)))
  (setq dir (file-name-as-directory dir))
  (let ((root-data (helm-cmd-t-root-data dir)))
    (if (equal dir (cdr root-data))
        root-data
      (cons "" dir))))

(defun helm-cmd-t-get-source-buffer-name (root)
  (format helm-cmd-t-source-buffer-format (file-name-as-directory root)))

(defun helm-cmd-t-repos-transformer (candidates)
  "Transform a list of buffers to list of
 (pretty-name . buffer)
"
  (mapcar (lambda (buffer-name)
            (let ((buffer (get-buffer buffer-name)))
              (cons (helm-cmd-t-format-title (buffer-local-value 'helm-cmd-t-data buffer)) buffer)))
          candidates))


(defun helm-cmd-t-insert-listing (repo-type repo-root)
  (let ((cmd (nth 2 (assoc repo-type helm-cmd-t-repo-types))))
    (if (functionp cmd)
        (funcall cmd repo-root)
      (shell-command (format-spec cmd (format-spec-make ?d (shell-quote-argument (expand-file-name repo-root)))) t))))

(defun helm-cmd-t-get-caches ()
  "return list of buffer names for caches suitable for transformation"
  (let (res)
    (mapc (lambda (buffer)
            (when (buffer-local-value 'helm-cmd-t-data buffer)
              (push (buffer-name buffer) res)))
          (buffer-list))
    res))

(defvar helm-source-cmd-t-caches
  `((name . "Cmd-t repo caches")
    (candidates . helm-cmd-t-get-caches)
    (candidate-transformer . helm-cmd-t-repos-transformer)
    (persistent-action . helm-cmd-t-run-grep)
    (persistent-help . "grep")
    (action . (("cmd-t"      . helm-cmd-t-for-buffer)
               ("grep"   .   tbd)
               ("INVALIDATE" . helm-kill-marked-buffers)))
    (action-transformer . helm-cmd-t-repos-action-tr)))

(defun helm-cmd-t-repos-action-tr (actions candidate-buffer)
  "Redirect to proper grep,
Remove invalidate if not cached."
  (let* ((data (buffer-local-value 'helm-cmd-t-data candidate-buffer))
         (repo-type (cdr (assq 'repo-type data)))
         (cached-p (cdr (assq 'cached-p data)))
         res)
    (mapc (lambda (action)
            (cond ((string-match "\\`grep\\'" (car action))
                   (push (cond ((string= repo-type "git")
                                (cons "git grep" 'helm-cmd-t-grep))
                               ((string= repo-type "")
                                (cons "recursive grep" 'helm-cmd-t-grep)))
                         res))
                  ((and (string-match "INVALIDATE" (car action))
                      (not cached-p)))
                  (t
                   (push action res))))
          actions)
    (reverse res)))

;;;###autoload
(defun helm-cmd-t (&optional arg)
  "Choose file from current repo.

With prefix arg C-u, run `helm-cmd-t-repos'.
"
  (interactive "P")
  (if (consp arg)
      (call-interactively 'helm-cmd-t-repos)
    (let ((root-data (helm-cmd-t-root-data)))
      (if root-data
          (helm :sources (helm-cmd-t-get-create-source root-data)
                :candidate-number-limit 20
                :buffer "*helm-cmd-t:*")
        (error "No repository for %s" default-directory)))))

;;;###autoload
(defun helm-cmd-t-repos (&optional preselect-root)
  "Manage helm-cmd-t caches."
  (interactive)
  (setq preselect-root (or preselect-root (helm-cmd-t-root)))
  (helm-cmd-t-get-create-source (helm-cmd-t-root-data preselect-root) 'skeleton)
  (helm :sources helm-source-cmd-t-caches
        :preselect (helm-aif (get-buffer
                              (helm-cmd-t-get-source-buffer-name preselect-root))
                       (regexp-quote (helm-cmd-t-format-title (buffer-local-value 'helm-cmd-t-data it))))))

(defun helm-cmd-t-read-glob ()
  (format "'%s'" (read-string "OnlyExt(e.g. *.rb *.erb): ")))

(defun helm-cmd-t-run-grep (arg)
  "Run Grep action from `helm-cmd-t-repos'."
  (interactive)
  (with-helm-alive-p
    (helm-quit-and-execute-action 'helm-cmd-t-grep_)))

(defun helm-cmd-t-grep_ (candidate-buffer)
  (apply 'run-with-timer 0.01 nil
         #'helm-cmd-t-grep
         candidate-buffer
         (when helm-current-prefix-arg
           (list (helm-cmd-t-read-glob)))))

;;;###autoload
(defun helm-cmd-t-grep (candidate-buffer &optional globs)
  "Grep action run from `helm-cmd-t-repos'.

Redirect to the correct grep based on `candidate-buffer'."
  (interactive (list (current-buffer)
                     (when current-prefix-arg
                       (helm-cmd-t-read-glob))))
  (let* ((repo-type (or (cdr (assq 'repo-type (buffer-local-value 'helm-cmd-t-data candidate-buffer)))
                       (with-current-buffer candidate-buffer
                         (car (helm-cmd-t-root-data))))))
    (funcall (cond ((string= repo-type "git")
                    'helm-cmd-t-git-grep)
                   ((string= repo-type "")
                    'helm-cmd-t-dir-grep))
             candidate-buffer globs)))

(defun helm-cmd-t-git-grep (cache-buffer &optional globs)
  "Do git grep.  Accessible as command or from the repos source.

Use C-U to narrow by extensions."
  ;; We set it here in case of nil, which breaks resume.
  (setq helm-ff-default-directory (or helm-ff-default-directory
                                     (helm-cmd-t-root cache-buffer)))
  (let* ((helm-grep-default-command "git grep -n%cH --full-name -E %p %f")
         (helm-grep-default-recurse-command helm-grep-default-command)
         (globs (cond (globs
                       (list "--" globs))
                      ((list
                        (helm-cmd-t-root cache-buffer)))))
         ;; `helm-grep-init' initialize `default-directory' to this value,
         ;; So set this value (i.e `helm-ff-default-directory') to
         ;; something else.
         (helm-ff-default-directory (helm-cmd-t-root cache-buffer))
         (helm-default-directory helm-ff-default-directory)
         ;; Expand filename of each candidate with the git root dir.
         ;; The filename will be in the help-echo prop.
         (helm-grep-default-directory-fn `(lambda ()
                                              ,helm-ff-default-directory)))
    (helm-do-grep-1 globs)))

(defun helm-cmd-t-dir-grep (cache-buffer &optional globs)
  "Dir based grep."
  ;; helm does not invoke this interactively
  (when helm-current-prefix-arg
    (setq globs (helm-cmd-t-read-glob)))
  (helm-do-grep-1 (list (cdr (assq 'repo-root
                                   (buffer-local-value 'helm-cmd-t-data cache-buffer))))
                  'recurse nil globs))

(defun helm-cmd-t-for-buffer (buffer)
  "used as action from `helm-cmd-t-repos' "
  (with-current-buffer buffer
    (helm-cmd-t)))

(defun helm-cmd-t-elisp-find-insert (root)
  "insert contents of directory recursively."
  (require 'helm-cmd-t-find)
  (let ((reject-regexp (helm-cmd-t-dumb-glob-to-regexp (append
                                                        helm-cmd-t-find-ignored-files
                                                        helm-cmd-t-find-prunes
                                                        '("." "..")))))
    (helm-cmd-t-insert-tree-1 nil reject-regexp)))

(defun helm-cmd-t-shell-find-insert (root)
  (let ((cmd (let ((default-directory "."))
               (find-cmd `(prune (name ,@helm-cmd-t-find-prunes))
                         `(not (name ,@helm-cmd-t-find-ignored-files))))))
    (shell-command cmd t)
    (goto-char (point-min))
    (while (re-search-forward "^\\./?\n?" nil t)
      (replace-match "" nil nil))))


(defun helm-cmd-t-get-find (root)
  "defer to `helm-cmd-t-elisp-find-insert' or `helm-cmd-t-shell-find-insert'
based on system type.
"
  (if (eq system-type 'windows-nt)
      (helm-cmd-t-elisp-find-insert root)
    (helm-cmd-t-shell-find-insert root)))


(provide 'helm-cmd-t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; helm-cmd-t.el ends here
