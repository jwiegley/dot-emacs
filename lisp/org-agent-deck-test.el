;;; org-agent-deck-test.el --- Tests for org-agent-deck -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)
(require 'org-agent-deck)
(require 'ob-agent-deck)

(ert-deftest org-agent-deck-read-session-completes-active-list ()
  (let (prompt collection)
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (_input &rest arguments)
                 (should (equal arguments '("list" "--json")))
                 "[{\"id\":\"one\",\"title\":\"First\",\"group\":\"work\",\"status\":\"waiting\",\"archived\":false},{\"id\":\"old\",\"title\":\"Old\",\"status\":\"stopped\",\"archived\":true}]"))
              ((symbol-function 'completing-read)
               (lambda (given-prompt given-collection &rest _)
                 (setq prompt given-prompt
                       collection given-collection)
                 (caar given-collection))))
      (should (equal (org-agent-deck--read-session "Session: ") "one")))
    (should (equal prompt "Session: "))
    (should (= (length collection) 1))
    (should (string-match-p "First — work \\[waiting\\] (one)"
                            (caar collection)))))

(ert-deftest org-agent-deck-send-entry-exports-current-subtree ()
  (with-temp-buffer
    (org-mode)
    (insert "* Before\nOutside\n"
            "* Container\n"
            "** TODO Current\nBody with *emphasis*.\n"
            "*** Child\nNested body.\n"
            "** Sibling\nNot sent.\n"
            "* After\nOutside\n")
    (goto-char (point-min))
    (re-search-forward "Body with")
    (let (input arguments)
      (cl-letf (((symbol-function 'org-agent-deck--read-session)
                 (lambda (_prompt) "session-1"))
                ((symbol-function 'org-agent-deck--call)
                 (lambda (given-input &rest given-arguments)
                   (setq input given-input
                         arguments given-arguments)
                   "")))
        (org-agent-deck-send-entry))
      (should (equal arguments
                     '("session" "send" "session-1" "--message-file" "-")))
      (should (string-match-p "^# Current$" input))
      (should (string-match-p "^## Child$" input))
      (should (string-match-p (regexp-quote "Body with **emphasis**.") input))
      (should-not (string-match-p "TODO" input))
      (should-not (string-match-p "Sibling" input))
      (should-not (string-match-p "Outside" input)))))

(ert-deftest org-agent-deck-insert-latest-output-creates-note ()
  (with-temp-buffer
    (org-mode)
    (let ((org-todo-keywords '((sequence "TODO" "NOTE" "|" "DONE"))))
      (insert "* Parent\nBody.\n* Following\nKeep.\n")
      (goto-char (point-min))
      (search-forward "Body")
      (cl-letf (((symbol-function 'org-agent-deck--read-session)
                 (lambda (_prompt) "session-2"))
                ((symbol-function 'org-agent-deck--latest-output)
                 (lambda (session-id)
                   (should (equal session-id "session-2"))
                   '("Remote session" . "# Result\n\n- one\n- two")))
                ((symbol-function 'org-agent-deck--markdown-to-org)
                 (lambda (markdown)
                   (should (equal markdown "# Result\n\n- one\n- two"))
                   "* Result\n\n- one\n- two")))
        (org-agent-deck-insert-latest-output))
      (should
       (equal (buffer-string)
              "* Parent\nBody.\n* NOTE Remote session\n** Result\n\n- one\n- two\n\n* Following\nKeep.\n")))))

(ert-deftest org-agent-deck-markdown-to-org-invokes-pandoc-without-shell ()
  (let ((org-agent-deck-pandoc-program "/test/pandoc")
        command input)
    (cl-letf (((symbol-function 'org-agent-deck--run)
               (lambda (given-command &optional given-input)
                 (setq command given-command
                       input given-input)
                 "* Result\n")))
      (should (equal (org-agent-deck--markdown-to-org "# Result")
                     "* Result")))
    (should (equal command
                   '("/test/pandoc" "-f" "markdown-auto_identifiers"
                     "-t" "org")))
    (should (equal input "# Result"))))

(ert-deftest org-agent-deck-markdown-to-org-converts-with-pandoc ()
  (skip-unless (executable-find org-agent-deck-pandoc-program))
  (let ((org (org-agent-deck--markdown-to-org
              "# Result\n\n**bold**\n\n- one\n- two\n")))
    (should (string-match-p "^\\* Result$" org))
    (should (string-match-p "^\\*bold\\*$" org))
    (should (string-match-p "^- one$" org))))

(ert-deftest org-agent-deck-command-prefix-covers-list-send-and-output ()
  (let ((org-agent-deck-command '("ssh" "hera" "agent-deck"))
        calls)
    (cl-letf (((symbol-function 'call-process-region)
               (lambda (start _end program _delete _buffer _display &rest arguments)
                 (push (list program arguments start) calls)
                 (erase-buffer)
                 (cond
                  ((equal (last arguments 2) '("list" "--json"))
                   (insert "[{\"id\":\"remote\",\"title\":\"Hera\",\"status\":\"idle\",\"archived\":false}]"))
                  ((equal (last arguments 4)
                          '("session" "output" "remote" "--json"))
                   (insert "{\"success\":true,\"session_title\":\"Hera\",\"content\":\"Done\"}")))
                 0)))
      (should (equal (plist-get (car (org-agent-deck--sessions)) :id)
                     "remote"))
      (org-agent-deck--call "Prompt" "session" "send" "remote"
                            "--message-file" "-")
      (should (equal (org-agent-deck--latest-output "remote")
                     '("Hera" . "Done"))))
    (should (= (length calls) 3))
    (dolist (call calls)
      (should (equal (car call) "ssh"))
      (should (equal (seq-take (cadr call) 2)
                     '("hera" "agent-deck"))))
    (should (seq-some (lambda (call) (equal (nth 2 call) "Prompt")) calls))))

(ert-deftest org-agent-deck-run-reports-command-failure ()
  (let (stderr-file)
    (cl-letf (((symbol-function 'call-process-region)
               (lambda (_start _end _program _delete buffer _display &rest _)
                 (setq stderr-file (cadr buffer))
                 (with-temp-file stderr-file
                   (insert "remote agent-deck is unavailable\n"))
                 255)))
      (let ((error
             (should-error
              (org-agent-deck--run '("ssh" "hera" "agent-deck"))
              :type 'user-error)))
        (should (string-match-p "exit 255" (error-message-string error)))
        (should (string-match-p "remote agent-deck is unavailable"
                                (error-message-string error)))))))

(defun org-agent-deck-test--launch-reply (body arguments &optional id)
  "Return a successful CLI response for BODY, ARGUMENTS and ID."
  (json-serialize
   `(:success t :session_id ,(or id "fresh-session")
     :title ,(or (cadr (member "--title" arguments)) "Project")
     :group ,(cadr (member "--group" arguments))
     :path ,(car (last arguments)) :tool ,(cadr (member "--cmd" arguments))
     :status "running" :message_pending :false
     :message ,(replace-regexp-in-string "[\r\n]+\\'" "" body))))

(ert-deftest org-agent-deck-babel-presets ()
  (dolist (case '(("work" "Positron" "openai-codex/gpt-6-astra" "max")
                  ("personal" "my-sessions" "omlx-hera/GLM-5.3-Flash-oQ4e" nil)))
    (let ((body "Review λ and فارسی.\nKeep \"quotes\", 'apostrophes', $HOME and `code`.\n")
          calls result)
      (cl-letf (((symbol-function 'org-agent-deck--call)
                 (lambda (input &rest args)
                   (push (cons input args) calls)
                   (org-agent-deck-test--launch-reply input args))))
        (setq result
              (org-babel-execute:agent-deck
               body `((:preset . ,(nth 0 case)) (:directory . "~/remote only/project")))))
      (should (= (length calls) 1))
      (let* ((args (cdar calls))
             (wrapper (cadr (member "--wrapper" args))))
        (should (equal (caar calls) body))
        (should (equal (car args) "launch"))
        (should (equal (car (last args)) "~/remote only/project/"))
        (should (equal (cadr (member "--cmd" args)) "pi"))
        (should (equal (cadr (member "--group" args)) (nth 1 case)))
        (should (equal (cadr (member "--message-file" args)) "-"))
        (should (member "--no-parent" args))
        (should (member "--no-assert-done" args))
        (should-not (member "--no-wait" args))
        (should-not (member "--model" args))
        (should (equal wrapper
                       (concat "{command} --model " (nth 2 case)
                               (when (nth 3 case)
                                 (concat " --thinking " (nth 3 case)))))))
      (should (string-match-p "Session: fresh-session" result))
      (should (string-match-p
               (regexp-quote (concat "Requested model: " (nth 2 case))) result))
      (should (string-match-p
               (regexp-quote (concat "Requested thinking: "
                                     (or (nth 3 case) "(harness default)")))
               result)))))

(ert-deftest org-agent-deck-babel-protects-trailing-directory-quotes ()
  (dolist (directory '("/remote/project'" "/remote/project\"" "~/project'\""))
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (body &rest args)
                 ;; Agent-deck applies strings.Trim(path, "'\"").
                 (let ((path (car (last args))))
                   (should (equal path (concat directory "/")))
                   (should (equal (string-trim path "['\"]+" "['\"]+") path)))
                 (org-agent-deck-test--launch-reply body args))))
      (org-babel-execute:agent-deck
       "Prompt" `((:preset . "work") (:directory . ,directory))))))

(ert-deftest org-agent-deck-babel-inherits-overrides-and-launches-fresh ()
  (with-temp-buffer
    (insert "#+PROPERTY: header-args:agent-deck :preset work :directory ~/remote-project\n"
            "* Project\n:PROPERTIES:\n"
            ":header-args:agent-deck+: :group my-sessions :model provider/inherited :thinking low\n"
            ":END:\n"
            "#+begin_src agent-deck :model provider/override :thinking high :title \"Design review\"\n"
            "Review λ.\nKeep \"quotes\" and $HOME.\n#+end_src\n")
    (org-mode)
    (let ((org-confirm-babel-evaluate nil)
          (count 0) calls)
      (cl-letf (((symbol-function 'org-agent-deck--call)
                 (lambda (body &rest args)
                   (push (cons body args) calls)
                   (org-agent-deck-test--launch-reply
                    body args (format "fresh-%d" (cl-incf count))))))
        (dotimes (_ 2)
          (goto-char (point-min))
          (search-forward "#+begin_src")
          (org-ctrl-c-ctrl-c)))
      (should (= count 2))
      (should (equal (caar calls) "Review λ.\nKeep \"quotes\" and $HOME."))
      (dolist (call calls)
        (should (equal (car (last call)) "~/remote-project/"))
        (should (equal (cadr (member "--group" call)) "my-sessions"))
        (should (equal (cadr (member "--wrapper" call))
                       "{command} --model provider/override --thinking high"))
        (should (string-prefix-p "Design review [" (cadr (member "--title" call)))))
      (should-not (equal (cadr (member "--title" (car calls)))
                         (cadr (member "--title" (cadr calls)))))
      (should (string-match-p (regexp-quote "#+RESULTS:") (buffer-string)))
      (should (string-match-p ": Session: fresh-2" (buffer-string)))
      (should-not (string-match-p "fresh-1" (buffer-string))))))

(ert-deftest org-agent-deck-babel-native-harness-overrides ()
  (dolist (case '(("claude" "max") ("codex" "high")
                  ("gemini" "default") ("opencode" "default")))
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (body &rest args)
                 (should (equal (cadr (member "--cmd" args)) (car case)))
                 (should (equal (cadr (member "--model" args)) "native-model"))
                 (should (equal (cadr (member "--effort" args))
                                (unless (equal (cadr case) "default") (cadr case))))
                 (should-not (member "--wrapper" args))
                 (org-agent-deck-test--launch-reply body args))))
      (org-babel-execute:agent-deck
       "Prompt" `((:preset . "work") (:directory . "/remote")
                  (:harness . ,(car case)) (:model . "native-model")
                  (:thinking . ,(cadr case)))))))

(ert-deftest org-agent-deck-babel-explicit-settings-without-preset ()
  (cl-letf (((symbol-function 'org-agent-deck--call)
             (lambda (body &rest args)
               (should (equal (cadr (member "--cmd" args)) "pi"))
               (should (equal (cadr (member "--group" args)) "custom/group"))
               (should-not (member "--wrapper" args))
               (org-agent-deck-test--launch-reply body args))))
    (org-babel-execute:agent-deck
     "Prompt" '((:directory . "/remote") (:group . "custom/group")))))

(ert-deftest org-agent-deck-babel-rejects-invalid-settings-before-launch ()
  (cl-letf (((symbol-function 'org-agent-deck--call)
             (lambda (&rest _) (ert-fail "Unexpected launch"))))
    (dolist (params '(((:preset . "unknown")) ((:directory . ""))
                      ((:directory . "--bad")) ((:directory . "relative/path"))
                      ((:group . 12)) ((:title . " ")) ((:title . "bad\0title"))
                      ((:harness . "pi; touch BAD")) ((:model . "$(touch BAD)"))
                      ((:thinking . "unlimited")) ((:dir . "/remote"))
                      ((:cache . "yes")) ((:session . "existing"))))
      (should-error
       (org-babel-execute:agent-deck
        "Prompt" (append params '((:preset . "work") (:directory . "/remote"))))
       :type 'user-error))
    (should-error (org-babel-execute:agent-deck "Prompt" '((:preset . "work")))
                  :type 'user-error)
    (should-error (org-babel-execute:agent-deck "Prompt" '((:directory . "/remote")))
                  :type 'user-error)
    (dolist (body '("" " \n " "Bad\0prompt"))
      (should-error
       (org-babel-execute:agent-deck body '((:preset . "work") (:directory . "/remote")))
       :type 'user-error))))

(ert-deftest org-agent-deck-babel-failures-never-retry-or-record-success ()
  (dolist (reply '("not JSON" "[]" "{\"success\":false,\"error\":\"unsupported model\"}"
                   "{\"success\":true}"
                   "{\"success\":true,\"id\":\"queued-id\",\"status\":\"queued\"}"
                   "{\"success\":true,\"id\":\"pending-id\",\"message_pending\":true}"
                   "{\"success\":true,\"id\":\"bad-prompt\",\"message\":\"different\"}"
                   process-failed))
    (with-temp-buffer
      (org-mode)
      (insert "#+begin_src agent-deck :preset work :directory /remote\nPrompt\n#+end_src\n")
      (goto-char (point-min))
      (let ((org-confirm-babel-evaluate nil) (calls 0))
        (cl-letf (((symbol-function 'org-agent-deck--call)
                   (lambda (&rest _)
                     (cl-incf calls)
                     (if (eq reply 'process-failed)
                         (user-error "Launch failed: unsupported model for tool")
                       reply))))
          (let ((err (should-error (org-babel-execute-src-block) :type 'user-error)))
            (should (string-match-p "retrying" (error-message-string err)))
            (when (eq reply 'process-failed)
              (should (string-match-p "unsupported model for tool"
                                      (error-message-string err))))))
        (should (= calls 1))
        (should-not (string-match-p (regexp-quote "#+RESULTS:") (buffer-string)))))))

(ert-deftest org-agent-deck-babel-respects-evaluation-controls ()
  (cl-letf (((symbol-function 'org-agent-deck--call)
             (lambda (&rest _) (ert-fail "Unexpected launch"))))
    (load "ob-agent-deck" nil t)
    (dolist (eval '("never" "query"))
      (with-temp-buffer
        (org-mode)
        (insert "#+begin_src agent-deck :preset work :directory /remote :eval " eval
                "\nPrompt\n#+end_src\n")
        (goto-char (point-min))
        (cl-letf (((symbol-function 'yes-or-no-p) (lambda (&rest _) nil)))
          (org-babel-execute-src-block))))
    (with-temp-buffer
      (org-mode)
      (insert "#+begin_src agent-deck :preset work :directory /remote\nPrompt\n#+end_src\n")
      (org-export-as 'md)
      (goto-char (point-min))
      (end-of-line)
      (insert " :eval yes :exports results")
      (let ((org-confirm-babel-evaluate nil))
        (should-error (org-export-as 'md) :type 'user-error)))))

(ert-deftest org-agent-deck-transport-preserves-argv-and-stdin ()
  "Exercise both real argv and SSH's shell-joined argv, without a network."
  (let* ((directory (make-temp-file "org-agent-deck-transport-" t))
         (ssh (expand-file-name "ssh" directory))
         (endpoint (expand-file-name "argv-echo" directory))
         (marker (expand-file-name "injected" directory))
         (payload (format "λ ' \" $HOME `uname`\n$(touch %s)\n" marker))
         (arguments (list "launch" "--title" payload "--group" "My Sessions"
                          "--wrapper" "{command} --model 'provider/id' --thinking max"
                          "~/remote dir/quotes'\"; $(false)")))
    (unwind-protect
        (progn
          (with-temp-file ssh
            (insert "#!/bin/sh\nshift\nexec /bin/sh -c \"$*\"\n"))
          (with-temp-file endpoint
            (insert "#!/bin/sh\nprintf '%s\\0' \"$@\"\ncat\n"))
          (set-file-modes ssh #o700)
          (set-file-modes endpoint #o700)
          (dolist (prefix (list (list endpoint) (list ssh "hera" endpoint)))
            (let ((org-agent-deck-command prefix))
              (should (equal (apply #'org-agent-deck--call payload arguments)
                             (concat (mapconcat #'identity arguments "\0")
                                     "\0" payload)))))
          (should-not (file-exists-p marker)))
      (delete-directory directory t))))

(provide 'org-agent-deck-test)

;;; org-agent-deck-test.el ends here
