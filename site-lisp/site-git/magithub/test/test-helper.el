;;; Allow loading package files
(require 'cask)

(let ((source-directory (locate-dominating-file load-file-name "Cask")))
  (cask-initialize source-directory)
  (add-to-list 'load-path source-directory)
  (setq magithub-dir (expand-file-name ".cask" source-directory)))

(defun magithub-in-test-dir (file)
  "Expand FILE in the test directory."
  (let ((dir default-directory))
    (while (and (not (string= dir "/"))
                (not (file-exists-p (expand-file-name ".git" dir))))
      (setq dir (file-name-directory (directory-file-name dir))))
    (when (string= dir "/")
      (error "Project root not found"))
    (setq dir (expand-file-name "test" dir))
    (expand-file-name file dir)))

(defun magithub-mock-data-crunch (data)
  "Crunch DATA into a string appropriate for a filename."
  (substring (sha1 (prin1-to-string data)) 0 8))

(defun magithub-mock-ghub-request (method resource &optional params data)
  "Mock a call to the GitHub API.

If the call has not been mocked and the AUTOTEST environment
variable is not set, offer to save a snapshot of the real API's
response."
  (message "(mock-ghub-request %S %S %S %S)" method resource params data)
  (when (eq t magithub-cache)
    (error "Did not respect cache"))
  (let* ((parts (cdr (s-split "/" resource)))
         (directory (mapconcat (lambda (s) (concat s ".d"))
                               (butlast parts) "/"))
         (filename (magithub-in-test-dir
                    (format "mock-data/%s/%s/%s"
                            (downcase method)
                            directory
                            (car (last parts))))))
    (dolist (v `(("P" . ,params) ("D" . ,data)))
      (when (cdr v)
        (setq filename (format "%s.%s-%s"
                               filename
                               (car v)
                               (magithub-mock-data-crunch (cdr v))))))
    (if (file-readable-p filename)
        (prog1 (with-temp-buffer
                 (insert-file-contents-literally filename)
                 (read (current-buffer)))
          (message "Found %S" filename))
      (message "Did not find %S" filename)
      (if (and (not (getenv "AUTOTEST"))
               (y-or-n-p (format "Request not mocked; mock now?")))
          (progn
            (make-directory directory t)
            (let ((real-data (ghub-request method resource params data)))
              (pp-display-expression real-data "*GitHub API Response*")
              (if (y-or-n-p "API response displayed; is this ok?")
                  (with-temp-buffer
                    (insert (pp-to-string real-data))
                    (write-file filename)
                    (message "Wrote %s" filename))
                (error "API response rejected"))))
        (error "Unmocked test: %S %S %S %S" method resource params data)))))
