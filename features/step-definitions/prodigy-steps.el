(Given "^I start prodigy$"
  (lambda ()
    (call-interactively 'prodigy)))

(Then "^I should be in prodigy mode$"
  (lambda ()
    (should (equal major-mode 'prodigy-mode))
    (should (equal mode-name "Prodigy"))))

(Then "^the buffer should be read only$"
  (lambda ()
    (should buffer-read-only)))

(Then "^the variable \"\\([^\"]+\\)\" should be undefined$"
  (lambda (variable-name)
    (should-not (boundp (intern variable-name)))))

(Then "^the variable \"\\([^\"]+\\)\" should have value \"\\([^\"]+\\)\"$"
  (lambda (variable-name value)
    (should (equal (eval (intern variable-name)) value))))

(Then "^I should not be in prodigy mode$"
  (lambda ()
    (should-not (equal major-mode 'prodigy-mode))))

(Given "^I add the following services:$"
  (lambda (table)
    (let* ((head (car table))
           (rows (cdr table))
           (name-index (-elem-index "name" head))
           (tags-index (-elem-index "tags" head))
           (cwd-index (-elem-index "cwd" head))
           (command-index (-elem-index "command" head))
           (args-index (-elem-index "args" head))
           (init-index (-elem-index "init" head))
           (path-index (-elem-index "path" head)))
      (mapc
       (lambda (row)
         (prodigy-define-service
           :name (nth name-index row)
           :tags (and tags-index (read (nth tags-index row)))
           :cwd (or (and cwd-index (f-expand (nth cwd-index row) prodigy-servers-path)) "cwd")
           :command (or (and command-index (nth command-index row)) "command")
           :args (and args-index (read (nth args-index row)))
           :init (and init-index (read (nth init-index row)))
           :path (and path-index (--map (f-expand it prodigy-servers-path) (read (nth path-index row))))))
       rows))))

(Then "^I should see services:$"
  (lambda (table)
    (let* ((head (car table))
           (name-index (-elem-index "name" head))
           (highlighted-index (-elem-index "highlighted" head))
           (marked-index (-elem-index "marked" head))
           (tags-index (-elem-index "tags" head))
           (started-index (-elem-index "started" head))
           (rows (cdr table)))
      (save-excursion
        (goto-char (point-min))
        (-each
         rows
         (lambda (row)
           (let ((name (nth name-index row))
                 (highlighted
                  (when highlighted-index
                    (read (nth highlighted-index row))))
                 (marked
                  (when marked-index
                    (read (nth marked-index row))))
                 (tags
                  (when tags-index
                    (read (nth tags-index row))))
                 (started
                  (when started-index
                    (read (nth started-index row)))))
             (let ((line (buffer-substring-no-properties (line-beginning-position) (line-end-position))))
               (if marked
                   (should (s-starts-with? (concat "* " name) line))
                 (should (s-starts-with? (concat "  " name) line)))
               (if started
                   (should (s-contains? "Running" line))
                 (should-not (s-contains? "Running" line)))
               (let ((match (s-matches? (format "\\[%s\\]" (s-join ", " (-map 'symbol-name tags))) line)))
                 (if tags
                     (should match)
                   (should-not match))))
             (when highlighted
               (should (eq (get-text-property (1+ (line-beginning-position)) 'face) 'prodigy-line-face))
               (should (eq (get-text-property (line-end-position) 'face) 'prodigy-line-face)))
             (forward-line 1))))))))

;; Using Curl here because for some weird reason, using
;; `url-retrieve-synchronously' fails with the message "Emacs is not
;; compiled with network support". That however only is an issue
;; inside the step.
;;
;; We are also sleeping before making the request to give the server
;; time to start.
(Then "^requesting \"\\([^\"]+\\)\" should respond with:$"
  (lambda (url body callback)
    (async-start
     `(lambda ()
        (with-temp-buffer
          (sleep-for 2)
          (call-process "curl" nil (current-buffer) nil "-s" ,url)
          (buffer-string)))
     `(lambda (response)
        (should (equal (s-trim response) (s-trim ,body)))
        (funcall ,callback)))))

(Then "^requesting \"\\([^\"]+\\)\" should fail$"
  (lambda (url callback)
    (async-start
     `(lambda ()
        (with-temp-buffer
          (sleep-for 2)
          (call-process "curl" nil (current-buffer) nil "-I" ,url)
          (buffer-string)))
     `(lambda (response)
        (should-not (s-contains? "HTTP/1.1" response))
        (funcall ,callback)))))

(Then "^I should be in prodigy log mode$"
  (lambda ()
    (should (eq major-mode 'prodigy-log-mode))
    (should (equal mode-name "Prodigy Log"))))

(Then "^the buffer \"\\([^\"]+\\)\" should exist$"
  (lambda (buffer-name)
    (should (get-buffer buffer-name))))

(When "^I kill the prodigy buffer$"
  (lambda ()
    (kill-buffer prodigy-buffer-name)))

(Then "^I should not be in prodigy log mode$"
  (lambda ()
    (should-not (eq major-mode 'prodigy-log-mode))))
