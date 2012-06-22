;;; build.el

;; emacs -Q -L . -l $PWD/build -batch -f batch-build-environment [OPTS]
;;
;; Accepts these options:
;;     clean            Clean first
;;     fullclean        Really clean first (recompile the world)

(require 'cl)
(require 'bytecomp)

(defconst build-dir (if load-file-name
                        (file-name-directory load-file-name)
                      "."))
(message "Build Emacs environment in %s..." build-dir)

(load (expand-file-name "lisp/emacs-async/async" build-dir))

(defconst build-debug nil)
(defconst build-use-autoloads nil)
(defconst build-directories '("override" "lisp" "lib" "site-lisp"))
(defconst build-special-files '("cus-dirs.el" "autoloads.el"))
(defconst build-source-files
  (apply #'append (mapcar #'(lambda (dir)
                              (directory-files dir t "\\`[^.].+\\.el\\'"))
                          build-directories)))
(defconst build-target-files
  (mapcar #'(lambda (file)
              (replace-regexp-in-string "\\.el\\'" ".elc" file))
          (append build-special-files build-source-files)))

(defvar build-clean-first nil)
(defvar build-dryrun-mode t)
(defvar build-try-to-compile-all-files nil)

(defvar build-Orig-message-function (symbol-function #'message))

;; MY_LOADPATH = -L . $(patsubst %,-L %,$(DIRS))
;; BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

(defun delete-file-if-exists (file)
  (if (file-exists-p file)
      (delete-file file)))

(defun files-in-directory (directory regexp)
  "List the .el files in DIRECTORY and in its sub-directories."
  ;; Although the function will be used non-interactively,
  ;; it will be easier to test if we make it interactive.
  ;; The directory will have a name such as
  ;;  "/usr/local/share/emacs/22.1.1/lisp/"
  (interactive "DDirectory name: ")
  (let (files-list)
    ;; while we are in the current directory
    (dolist (entry (directory-files-and-attributes directory t))
      (if (eq t (cadr entry))
          (unless (string-match "\\`\\.\\.?\\'"
                                (file-name-nondirectory (car entry)))
            ;; descend into the directory and repeat the process
            (setq files-list
                  (append (files-in-directory (car entry) regexp)
                          files-list)))
        (if (string-match regexp (car entry))
            (setq files-list (cons (car entry) files-list)))))
    files-list))

(defun build-file (file)
  (expand-file-name file build-dir))

(defun build-should-compile-file (file broken)
  (and (not (or (string-match (concat (regexp-opt
                                    '(
                                      "emacs.d/broken"
                                      "emacs.d/build"
                                      ".dir-locals"
                                      ".dir-settings"
                                      ".status"
                                      ) t)
                                   "\\.el\\'")
                              file)
                (string-match "-tests?\\.el\\'" file)
                (string-match "/tests?/" (file-name-directory file))
                (string-match "\\`test-" (file-name-nondirectory file))))

       (file-newer-than-file-p
        file (concat (file-name-sans-extension file) ".elc"))

       (or build-try-to-compile-all-files
           (null broken)
           (< (cdr broken) 4))))

(defun build-recompile-file (file broken-files)
  (let ((broken (assoc file broken-files)))
    (when (build-should-compile-file file broken)
      (if (null
           (progn
             (message "Would recompile %s..." file)
             (when nil
               (let ((proc
                      (async-start
                       `(lambda ()
                          (require 'bytecomp)
                          ,(async-inject-variables "\\`load-path\\'")
                          (let ((default-directory ,(file-name-directory file)))
                            (add-to-list 'load-path default-directory)
                            (ignore-errors
                              (load ,file))
                            ;; returns nil if there were any errors
                            (byte-compile-file ,file)
                            (load ,file))))))

                 ;; (async-wait proc)
                 ;; (with-current-buffer (process-buffer proc)
                 ;;   (delete-blank-lines)
                 ;;   (unless (eobp)
                 ;;     (princ (buffer-string))))

                 (unless (condition-case err
                             (async-get proc)
                           (error
                            (ignore (message "Error: %s" err))))
                   (ignore (message "Recompiling %s...FAILED" file)))))))

          (if broken
              (setcdr broken (1+ (cdr broken)))
            (setq broken-files (cons (cons file 1) broken-files)))

        (setq broken-files (delete broken broken-files))))

    broken-files))

(defun batch-build-environment ()
  (interactive)

  ;; Process command-line options
  (when (or (member "clean" command-line-args-left)
            (member "fullclean" command-line-args-left))
    (message "Deleting .elc files in current directory...")
    (mapc #'delete-file (directory-files build-dir t "\\.elc\\'"))
    (delete-file-if-exists (build-file "autoloads.el"))
    (delete-file-if-exists (build-file "cus-dirs.el")))

  (when (member "fullclean" command-line-args-left)
    (message "Deleting .elc files in %s..."
             (mapconcat 'identity build-directories " "))
    (delete-file-if-exists (build-file "broken.el"))
    (mapc #'delete-file
          (append
           (mapcar #'(lambda (dir)
                       (files-in-directory dir "\\.elc\\'"))
                   build-directories))))

  (setq build-try-to-compile-all-files
        (member "rebuild" command-line-args-left)
        build-dryrun-mode
        (member "dryrun" command-line-args-left))

  ;; Byte-compile load-path.el if necessary, then load it
  (byte-recompile-file "load-path.el" nil 0 t)

  ;; Sniff out :load-path and :build cookies from init.el
  (let (builders)
    (with-temp-buffer
      (insert-file-contents (build-file "init.el"))
      (goto-char (point-min))
      (let (sexp load-path)
        (condition-case nil
            (while (and (not (eobp))
                        (setq sexp (read (current-buffer))))
              (when (eq 'use-package (car sexp))
                (if (setq load-path (plist-get (cddr sexp) :load-path))
                    (add-to-list 'load-path
                                 (expand-file-name load-path
                                                   user-emacs-directory) t))
                (if (setq builder (plist-get (cddr sexp) :build))
                    (add-to-list 'builders builder))))
          (end-of-file))))

    (mapc #'funcall builders))

  ;; Show the load-path in debug mode, before we start byte-compiling
  (when build-debug
    (message "Current load-path:")
    (message "((")
    (dolist (path load-path)
      (princ path)
      (terpri))
    (message "))")
    (kill-emacs 0))

  ;; Byte-compile everything in the subdirectories; this refreshes anything
  ;; init.el might depend on.
  (let (broken-files broken-files-before)
    (if (file-readable-p (build-file "broken.el"))
        (with-temp-buffer
          (insert-file-contents (build-file "broken.el"))
          (goto-char (point-min))
          (setq broken-files (read (current-buffer))
                broken-files-before (copy-tree broken-files))))

    (mapc
     #'(lambda (dir)
         (flet ((message
                 (&rest args)
                 (unless (and (stringp (car args))
                              (string-match "^Checking " (car args)))
                   (apply build-Orig-message-function args))))
           (mapc #'(lambda (file)
                     (setq broken-files
                           (build-recompile-file file broken-files)))
                 (progn
                   (message "Finding all Emacs Lisp files in %s..." dir)
                   (files-in-directory dir "\\.el\\'")))))
     build-directories)

    (unless (equal broken-files broken-files-before)
      (with-temp-buffer
        (prin1 broken-files (current-buffer))
        (write-file (build-file "broken.el")))))

  (let* ((target (build-file "init.elc"))
         (init-out-of-date
          (if (not (file-exists-p target))
              'not-exist
            (message "Checking if any .elc is file is newer than init.elc...")
            (and (or (file-newer-than-file-p (build-file "init.el") target)
                     (catch 'result
                       (ignore
                        (mapc
                         #'(lambda (file)
                             (when (and (not (string-match (build-file "dot-")
                                                           file))
                                        (file-newer-than-file-p file target))
                               (message "Yes, %s is newer" file)
                               (throw 'result t)))
                         (files-in-directory build-dir "\\.elc\\'")))))
                 'out-of-date))))

    ;; If init.elc is even potentially out of date, recompile it.
    (when init-out-of-date
      (if build-dryrun-mode
          (progn
            (message
             "Would rebuild customization dependencies file, cus-dirs.el...")
            (message "Would rebuild init.el and dependencies because it %s..."
                     (if (eq init-out-of-date 'not-exist)
                         "does not exist" "is out of date")))

        ;; Re-build the customize dependencies file if anything was out of date.
        (message "Rebuilding customize dependencies file, cus-dirs.el...")
        (load "cus-dep")
        (let ((command-line-args-left build-directories))
          (delete-file-if-exists (build-file "cus-dirs.el"))
          (custom-make-dependencies)
          (rename-file "cus-load.el" (build-file "cus-dirs.el")))

        ;; Rebuild the autoloads.el file, if we are using that mechanism.
        (when (and build-use-autoloads
                   (catch 'result
                     (ignore
                      (mapc #'(lambda (file)
                                (if (file-newer-than-file-p
                                     file (build-file "autoloads.el"))
                                    (throw 'result t)))
                            build-target-files))))
          (message "Rebuilding generated autoloads.el file...")

          (copy-file (build-file "autoloads.in")
                     (build-file "autoloads.el"))
          (delete-file-if-exists (build-file "autoloads.elc"))

          (load (build-file "autoloads"))
          (load "easy-mmode")

          (let ((command-line-args-left
                 (append
                  (mapcar
                   #'(lambda (dir)
                       (delq
                        nil
                        (mapcar
                         #'(lambda (entry)
                             (and (not (string-match "\\`\\.\\.?\\'"
                                                     (file-name-nondirectory
                                                      (car entry))))
                                  (eq t (cadr entry))
                                  entry))
                         (directory-files-and-attributes dir t))))
                   build-directories))))
            (generate-autoloads))

          (byte-compile-file (build-file "autoloads.el") t))

        ;; Delete compiled versions of any dot-*.el files, to avoid them
        ;; bringing in outdated definitions (since we haven't recompiled them
        ;; yet).
        (mapc #'delete-file (directory-files "." t "\\`dot-.*\\.elc\\'"))

        ;; Is _any_ .elc newer than init.el?  If so, re-byte-compile it to
        ;; make sure we base our compiled init file on current definitions.
        (message
         "Rebuilding init.el and dependencies because it %s..."
         (if (eq init-out-of-date 'not-exist)
             "does not exist" "is out of date"))

        (delete-file-if-exists (build-file "init.elc"))
        (load (build-file "init.el"))
        (byte-compile-file (build-file "init.el"))

        ;; Now byte-compile the dot-*.el files, with all the information
        ;; from init.el compiled in.
        (mapc #'byte-compile-file
              (directory-files "." t "\\`dot-.*\\.el\\'")))))

  (message "Done updating Emacs environment."))

(provide 'build)

;;; build.el ends here
