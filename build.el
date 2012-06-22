;;; build.el

;; Run as: $(EMACS) -Q -L . -l build -batch -f batch-build-environment
;;
;; Accepts these options:
;;     --clean                Clean first
;;     --fullclean            Really clean first (recompile the world)

(require 'cl)
(require 'bytecomp)

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
(defvar build-try-to-compile-all-files nil)

(defvar build-Orig-message-function (symbol-function #'message))

;; MY_LOADPATH = -L . $(patsubst %,-L %,$(DIRS))
;; BATCH_LOAD  = $(EMACS_BATCH) $(MY_LOADPATH)

(defun delete-file-if-exists (file)
  (if (file-exists-p file)
      (delete-file file)))

(defun build-find (dirs &rest args)
  (with-temp-buffer
    (let ((output (string= (car (last args)) "-print")))
      (apply #'call-process "find" nil output nil (append dirs args))
      (and output
           (split-string (buffer-string) "\n" t)))))

(defun batch-build-environment ()
  (interactive)
  (when (or (member "--clean" command-line-args-left)
            (member "--fullclean" command-line-args-left))
    (message "Deleting .elc files in current directory...")
    (mapc #'delete-file (directory-files "." t "\\.elc\\'"))
    (delete-file-if-exists "./autoloads.el")
    (delete-file-if-exists "./cus-dirs.el"))

  (when (member "--fullclean" command-line-args-left)
    (message "Deleting .elc files in %s..."
             (mapconcat 'identity build-directories " "))
    (build-find build-directories "-name" "*.elc" "-type" "f" "-delete"))

  (setq build-try-to-compile-all-files
        (member "--tryall" command-line-args-left))

  ;; Byte-compile load-path.el if necessary, then load it; do not load
  ;; init.el, just byte-recompile it if necessary.
  (byte-recompile-file "./load-path.el" nil 0 t)
  (byte-recompile-file "./init.el" nil 0 nil)

  ;; Byte-compile everything in the subdirectories; this refreshes anything
  ;; emacs.el might depend on.
  (when nil
    (let (broken-files)
      (if (file-readable-p "./broken.el")
          (with-temp-buffer
            (insert-file-contents "./broken.el")
            (goto-char (point-min))
            (setq broken-files (read (current-buffer)))))

      (mapc
       #'(lambda (dir)
           (flet ((message
                   (&rest args)
                   (unless (and (stringp (car args))
                                (string-match "^Checking " (car args)))
                     (apply build-Orig-message-function args))))
             (mapc
              #'(lambda (file)
                  (let ((broken (assoc file broken-files)))
                    (if (and (not (string-match "/\\(broken\\|build\\)\\.el\\'"
                                                file))
                             (or build-try-to-compile-all-files
                                 (null broken)
                                 (< (cdr broken) 5))
                             (not (ignore-errors
                                    (byte-recompile-file file nil 0))))
                        (if broken
                            (setcdr broken (1+ (cdr broken)))
                          (setq broken-files (cons (cons file 1)
                                                   broken-files))))))
              (build-find (list dir) "-name" "*.el"
                          "-type" "f" "-print"))))
       build-directories)

      (if broken-files
          (progn
            (with-temp-buffer
              (prin1 broken-files (current-buffer))
              (write-file "./broken.el"))))))

  ;; Is _any_ .elc newer than emacs.el?  If so, re-byte-compile it to make
  ;; sure we base our compiled init file on current definitions.
  (message "Checking if any dependency is newer than emacs.el...")
  (when (some #'(lambda (file)
                  (file-newer-than-file-p file "./emacs.el"))
              (build-find '(".") "-name" "*.elc" "-type" "f" "-print"))
    (message "Yes, rebuilding emacs.el and its dependencies...")

    ;; Re-build the customize dependencies file.
    (message "Rebuilding customize dependencies file, cus-load.el...")
    (load "cus-dep")
    (let ((command-line-args-left build-directories))
      (custom-make-dependencies))

    ;; Rebuild the autoloads.el file, if we are using that mechanism.
    (when (and build-use-autoloads
               (some #'(lambda (file)
                         (file-newer-than-file-p file "./autoloads.el"))
                     build-target-files))
      (message "Rebuilding generated autoloads.el file...")

      (copy-file "./autoloads.in" "./autoloads.el")
      (delete-file-if-exists "./autoloads.elc")

      (load "./autoloads")
      (load "easy-mmode")

      (let ((command-line-args-left
             (build-find "find" build-directories "-maxdepth" "1"
                         "-type" "d" "-print")))
        (generate-autoloads))

      (byte-compile-file "./autoloads.el" t))

    ;; Delete compiled versions of any dot-*.el files, to avoid them bringing
    ;; in outdated definitions (since we haven't recompiled them yet).
    (let ((dot-files ))
      (mapc #'delete-file (directory-files "." t "\\`dot-.*\\.elc\\'"))

      (delete-file-if-exists "./emacs.elc")
      (load "./emacs.el")
      (byte-compile-file "./emacs.el")

      ;; Now byte-compile the dot-*.el files, with all the information from
      ;; emacs.el compiled in.
      (mapc #'byte-compile-file (directory-files "." t "\\`dot-.*\\.el\\'")))
    )

  (message "Done updating Emacs environment."))

(provide 'build)

;;; build.el ends here
