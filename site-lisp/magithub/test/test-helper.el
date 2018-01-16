;;; Allow loading package files
(require 'cask)
(require 'cl-lib)

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

(cl-defun magithub-mock-ghub-request (method resource &optional params
                                             &key query payload headers unpaginate
                                             noerror reader username auth host)
  "Mock a call to the GitHub API.

If the call has not been mocked and the AUTOTEST environment
variable is not set, offer to save a snapshot of the real API's
response."
  (message "(mock-ghub-request %S %S %S :query %S :payload %S :headers %S :unpaginate %S :noerror %S :reader %S :username %S :auth %S :host %S)"
           method resource params query payload headers unpaginate noerror reader username auth host)
  (when (eq t magithub-cache)
    (error "Did not respect cache"))
  (let* ((parts (cdr (s-split "/" resource)))
         (directory (mapconcat (lambda (s) (concat s ".d"))
                               (butlast parts) "/"))
         (filename (magithub-in-test-dir
                    (format "mock-data/%s/%s/%s.%s"
                            (downcase method)
                            directory
                            (car (last parts))
                            (magithub-mock-data-crunch
                             (list method resource params query payload headers
                                   unpaginate noerror reader username auth host))))))
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
            (let ((real-data (ghub-request method resource params
                                           :query query
                                           :payload payload
                                           :headers headers
                                           :unpaginate unpaginate
                                           :noerror noerror
                                           :reader reader
                                           :username username
                                           :auth auth
                                           :host host)))
              (pp-display-expression real-data "*GitHub API Response*")
              (if (y-or-n-p "API response displayed; is this ok?")
                  (with-temp-buffer
                    (insert (pp-to-string real-data))
                    (write-file filename)
                    (message "Wrote %s" filename))
                (error "API response rejected"))))
        (error "Unmocked test!")))))
