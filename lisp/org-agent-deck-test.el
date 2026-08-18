;;; org-agent-deck-test.el --- Tests for org-agent-deck -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)
(require 'org-agent-deck)

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

(provide 'org-agent-deck-test)

;;; org-agent-deck-test.el ends here
