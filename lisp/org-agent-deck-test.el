;;; org-agent-deck-test.el --- Tests for org-agent-deck -*- lexical-binding: t; -*-

(require 'ert)
(require 'cl-lib)
(require 'org)
(require 'org-agent-deck)
(require 'ob-agent-deck)
(require 'wid-edit)

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
                 (lambda (_prompt &optional remote) (should-not remote) "session-1"))
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
                 (lambda (_prompt &optional remote) (should-not remote) "session-2"))
                ((symbol-function 'org-agent-deck--latest-output)
                 (lambda (session-id &optional remote)
                   (should (equal session-id "session-2"))
                   (should-not remote)
                   '("Remote session" . "# Result\n\n- one\n- two")))
                ((symbol-function 'org-agent-deck--markdown-to-org)
                 (lambda (markdown)
                   (should (equal markdown "# Result\n\n- one\n- two"))
                   "* Result\n\n- one\n- two")))
        (org-agent-deck-insert-latest-output))
      (should
       (equal (buffer-string)
              "* Parent\nBody.\n* NOTE Remote session\n** Result\n\n- one\n- two\n\n* Following\nKeep.\n")))))

(defun org-agent-deck-test--remote-cli (input &rest arguments)
  "Answer ARGUMENTS as an agent-deck with remotes vulcan and nyx would.
INPUT is ignored; a session vulcan-1 runs on vulcan."
  (ignore input)
  (pcase arguments
    ('("remote" "list" "--json")
     "[{\"name\":\"vulcan\",\"host\":\"johnw@vulcan\"},{\"name\":\"nyx\",\"host\":\"johnw@nyx\"}]")
    ('("remote" "exec" "vulcan" "list" "--json")
     "[{\"id\":\"vulcan-1\",\"title\":\"On Vulcan\",\"group\":\"my-sessions\",\"status\":\"idle\",\"archived\":false}]")
    ('("remote" "exec" "vulcan" "session" "send" "vulcan-1" "--message-file" "-") "")
    ('("remote" "exec" "vulcan" "session" "output" "vulcan-1" "--json")
     "{\"success\":true,\"session_title\":\"On Vulcan\",\"content\":\"Checked.\"}")
    (_ (ert-fail (format "Unexpected agent-deck call: %S" arguments)))))

(ert-deftest org-agent-deck-send-entry-prefix-reaches-a-remote-session ()
  "With a prefix argument, the remote is chosen first, then one of its
sessions, and the entry goes to that session through `remote exec'."
  (with-temp-buffer
    (org-mode)
    (insert "* Task\nBody.\n")
    (goto-char (point-min))
    (let (calls prompts)
      (cl-letf (((symbol-function 'org-agent-deck--call)
                 (lambda (input &rest arguments)
                   (push (cons input arguments) calls)
                   (apply #'org-agent-deck-test--remote-cli input arguments)))
                ((symbol-function 'completing-read)
                 (lambda (prompt collection &rest _)
                   (push (cons prompt collection) prompts)
                   (if (equal prompt "Remote: ") "vulcan" (caar collection)))))
        (let ((current-prefix-arg '(4)))
          (call-interactively #'org-agent-deck-send-entry)))
      (should (equal (mapcar #'cdr (reverse calls))
                     '(("remote" "list" "--json")
                       ("remote" "exec" "vulcan" "list" "--json")
                       ("remote" "exec" "vulcan" "session" "send" "vulcan-1"
                        "--message-file" "-"))))
      (should (string-match-p "^# Task$" (car (car calls))))
      (should (equal (mapcar #'car (reverse prompts))
                     '("Remote: " "Send entry to session: ")))
      (should (equal (cdr (car (last prompts))) '("vulcan" "nyx"))))))

(ert-deftest org-agent-deck-insert-latest-output-prefix-reads-a-remote-session ()
  "With a prefix argument, the reply is read from a session on the chosen remote."
  (with-temp-buffer
    (org-mode)
    (let ((org-todo-keywords '((sequence "TODO" "NOTE" "|" "DONE")))
          calls)
      (insert "* Parent\nBody.\n")
      (goto-char (point-min))
      (cl-letf (((symbol-function 'org-agent-deck--call)
                 (lambda (input &rest arguments)
                   (push arguments calls)
                   (apply #'org-agent-deck-test--remote-cli input arguments)))
                ((symbol-function 'completing-read)
                 (lambda (prompt collection &rest _)
                   (if (equal prompt "Remote: ") "vulcan" (caar collection))))
                ((symbol-function 'org-agent-deck--markdown-to-org) #'identity))
        (let ((current-prefix-arg '(4)))
          (call-interactively #'org-agent-deck-insert-latest-output)))
      (should (equal (reverse calls)
                     '(("remote" "list" "--json")
                       ("remote" "exec" "vulcan" "list" "--json")
                       ("remote" "exec" "vulcan" "session" "output" "vulcan-1" "--json"))))
      ;; As for a local session, a blank line follows the inserted NOTE.
      (should (equal (buffer-string)
                     "* Parent\nBody.\n* NOTE On Vulcan\nChecked.\n\n")))))

(ert-deftest org-agent-deck-read-remote-refuses-missing-or-malformed-remotes ()
  "Choosing a remote fails clearly when agent-deck lists none or answers oddly."
  (dolist (reply '("[]" "{}" "[{\"host\":\"johnw@vulcan\"}]" "[{\"name\":\"\"}]"))
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (_input &rest arguments)
                 (should (equal arguments '("remote" "list" "--json")))
                 reply))
              ((symbol-function 'completing-read)
               (lambda (&rest _) (ert-fail "Nothing should be offered"))))
      (should-error (org-agent-deck--read-remote "Remote: ") :type 'user-error))))

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
  "Return a successful CLI response for BODY, ARGUMENTS and ID.
Without BODY the launch sent no message, and agent-deck reports none."
  (let ((directory (car (last arguments)))
        (branch (cadr (member "--worktree" arguments))))
    (json-serialize
     `(:success t :session_id ,(or id "fresh-session")
       :title ,(cadr (member "--title" arguments))
       :group ,(cadr (member "--group" arguments))
       :path ,(if branch
                  (concat (file-name-as-directory directory) ".worktrees/" branch)
                directory)
       :worktree_branch ,(or branch :null)
       :tool ,(cadr (member "--cmd" arguments))
       :status "running"
       ,@(when body
           `(:message_pending :false
             :message ,(replace-regexp-in-string "[\r\n]+\\'" "" body)))))))

(defun org-agent-deck-test--script (directory name text)
  "Write the executable script NAME with TEXT in DIRECTORY; return its file."
  (let ((file (expand-file-name name directory)))
    (with-temp-file file (insert text))
    (set-file-modes file #o700)
    file))

(defun org-agent-deck-test--wait (predicate)
  "Accept process output until PREDICATE holds, for ten seconds at most.
Return PREDICATE's final value."
  (let ((deadline (+ (float-time) 10)))
    (while (and (not (funcall predicate)) (< (float-time) deadline))
      (accept-process-output nil 0.05))
    (funcall predicate)))

(defun org-agent-deck-test--read (file)
  "Return the contents of FILE."
  (with-temp-buffer
    (insert-file-contents file)
    (buffer-string)))

(defconst org-agent-deck-test--fake-cli
  "#!/bin/sh
# Log each call beside this script, then answer as agent-deck would.
log=$(dirname \"$0\")
n=$(ls \"$log\" | grep -c '\\.argv$')
printf '%s\\0' \"$@\" > \"$log/$n.argv\"
cat > \"$log/$n.stdin\"
case \" $* \" in
  *' launch '*)
    echo '{\"success\":true,\"id\":\"fresh-session\",\"session_id\":\"fresh-session\",\"title\":\"ob-agent-deck-mail\",\"group\":\"Positron\",\"path\":\"~/src/project/\",\"tool\":\"claude\",\"profile\":\"default\",\"status\":\"starting\"}' ;;
  *' session send '*)
    case $(cat \"$log/$n.stdin\") in
      /mailbox*)
        echo '{\"success\":true,\"session_id\":\"fresh-session\",\"session_title\":\"ob-agent-deck-mail\",\"message\":\"/mailbox ob-agent-deck-mail ++work !+review\",\"delivery\":\"submitted\",\"submitted\":true,\"confirmation\":\"confirmed\"}' ;;
      *)
        # Hold the prompt, as --defer-if-busy does, until the test releases it.
        i=0
        while [ -n \"$FAKE_PROMPT_HOLD\" ] && [ ! -e \"$log/release\" ] && [ $i -lt 200 ]; do
          sleep 0.05
          i=$((i + 1))
        done
        case \"$FAKE_PROMPT_FAILS\" in
          exit)
            echo 'defer-if-busy: target still busy (running) after 30m0s' >&2
            exit 1 ;;
          reply)
            echo '{\"success\":true,\"session_id\":\"fresh-session\",\"message\":\"Another prompt.\",\"delivery\":\"submitted\",\"submitted\":true,\"confirmation\":\"confirmed\"}'
            exit 0 ;;
          unknown)
            echo '{\"success\":true,\"session_id\":\"fresh-session\",\"session_title\":\"ob-agent-deck-mail\",\"message\":\"Fix the capture issue.\",\"delivery\":\"delivered\",\"submitted\":false,\"confirmation\":\"unknown\"}'
            exit 0 ;;
        esac
        echo '{\"success\":true,\"session_id\":\"fresh-session\",\"session_title\":\"ob-agent-deck-mail\",\"message\":\"Fix the capture issue.\",\"delivery\":\"submitted\",\"submitted\":true,\"confirmation\":\"confirmed\"}' ;;
    esac ;;
  *)
    echo \"unexpected call: $*\" >&2
    exit 2 ;;
esac
"
  "A fake agent-deck for mailbox launches; it logs its calls beside itself.")

(defun org-agent-deck-test--fake-calls (directory)
  "Return the calls the fake agent-deck logged in DIRECTORY, oldest first.
Each call is (ARGV . STDIN)."
  (cl-loop for n from 0
           for argv = (expand-file-name (format "%d.argv" n) directory)
           while (file-exists-p argv)
           collect (cons (split-string (org-agent-deck-test--read argv) "\0" t)
                         (org-agent-deck-test--read
                          (expand-file-name (format "%d.stdin" n) directory)))))

(defun org-agent-deck-test--mailbox-block (headers &optional held)
  "Run a work block with extra HEADERS through the fake agent-deck.
Wait until the background prompt send reports, then return a plist of
the logged :calls, the Org :buffer text, and the :messages and :warnings
shown to the user.  With HELD, the fake holds the prompt send until
after the block returns and HELD is called with the buffer text and the
messages shown so far."
  (let* ((directory (make-temp-file "org-agent-deck-mailbox-" t))
         (org-agent-deck-command
          (list (org-agent-deck-test--script
                 directory "agent-deck" org-agent-deck-test--fake-cli)))
         (process-environment (if held
                                  (cons "FAKE_PROMPT_HOLD=1" process-environment)
                                process-environment))
         (org-confirm-babel-evaluate nil)
         messages warnings)
    (unwind-protect
        (with-temp-buffer
          (insert "#+begin_src agent-deck :preset work :directory ~/src/project "
                  headers "\nFix the capture issue.\n#+end_src\n")
          (org-mode)
          (cl-letf (((symbol-function 'message)
                     (lambda (format &rest args)
                       (when format
                         (push (apply #'format-message format args) messages))))
                    ((symbol-function 'display-warning)
                     (lambda (&rest args) (push args warnings))))
            (goto-char (point-min))
            (org-ctrl-c-ctrl-c)
            (when held
              (funcall held (buffer-string) messages)
              (with-temp-file (expand-file-name "release" directory)))
            (org-agent-deck-test--wait
             (lambda ()
               (or warnings
                   (seq-some (lambda (text) (string-search "fresh-session" text))
                             messages)))))
          (list :calls (org-agent-deck-test--fake-calls directory)
                :buffer (buffer-string) :messages messages :warnings warnings))
      (delete-directory directory t))))

(ert-deftest org-agent-deck-babel-presets ()
  (dolist (case '(("work-codex" "Positron" "openai-codex/gpt-6-astra" "max")
                  ("local" "my-sessions" "omlx-hera/GLM-5.3-Flash-oQ4e-mtp" "max")
                  ("local" "my-sessions" "omlx-hera/GLM-5.3-Flash-oQ4e-mtp" nil
                   ((:thinking . "default")))))
    (let ((body "Review λ and فارسی.\nKeep \"quotes\", 'apostrophes', $HOME and `code`.\n")
          calls result)
      (cl-letf (((symbol-function 'org-agent-deck--call)
                 (lambda (input &rest args)
                   (push (cons input args) calls)
                   (org-agent-deck-test--launch-reply input args))))
        (setq result
              (org-babel-execute:agent-deck
               body (append (nth 4 case)
                            `((:preset . ,(nth 0 case))
                              (:directory . "~/remote only/project"))))))
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

(ert-deftest org-agent-deck-babel-inherits-overrides-with-exact-title ()
  (with-temp-buffer
    (insert "#+PROPERTY: header-args:agent-deck :preset work-codex :directory ~/remote-project :worktree yes\n"
            "* Project\n:PROPERTIES:\n"
            ":header-args:agent-deck+: :group my-sessions :model provider/inherited :thinking low\n"
            ":END:\n"
            "#+begin_src agent-deck :model provider/override :thinking high :title \"Design review\" :worktree no\n"
            "Review λ.\nKeep \"quotes\" and $HOME.\n#+end_src\n")
    (org-mode)
    (let ((org-confirm-babel-evaluate nil) calls)
      (cl-letf (((symbol-function 'org-agent-deck--call)
                 (lambda (body &rest args)
                   (push (cons body args) calls)
                   (org-agent-deck-test--launch-reply body args))))
        (goto-char (point-min))
        (search-forward "#+begin_src")
        (org-ctrl-c-ctrl-c))
      (should (= (length calls) 1))
      (should (equal (caar calls) "Review λ.\nKeep \"quotes\" and $HOME."))
      (let ((call (car calls)))
        (should (equal (car (last call)) "~/remote-project/"))
        (should (equal (cadr (member "--group" call)) "my-sessions"))
        (should (equal (cadr (member "--wrapper" call))
                       "{command} --model provider/override --thinking high"))
        (should (equal (cadr (member "--title" call)) "Design review"))
        (should-not (member "--worktree" call)))
      (should (string-match-p (regexp-quote "#+RESULTS:") (buffer-string)))
      (should (string-match-p ": Session: fresh-session" (buffer-string))))))

(ert-deftest org-agent-deck-babel-default-and-explicit-titles ()
  (dolist (case '(("/remote/project" nil "project")
                  ("~/remote/project/" nil "project")
                  ("/remote/project" "Review \"quotes\" λ" "Review \"quotes\" λ")
                  ("/" "Root" "Root")))
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (body &rest args)
                 (should (equal (cadr (member "--title" args)) (nth 2 case)))
                 (org-agent-deck-test--launch-reply body args))))
      (org-babel-execute:agent-deck
       "Prompt" (append (when (nth 1 case) `((:title . ,(nth 1 case))))
                        `((:preset . "work") (:directory . ,(car case))))))))

(ert-deftest org-agent-deck-babel-worktree-follows-title ()
  (dolist (setting '(nil "no" "yes"))
    (dolist (title '(nil "fix-capture"))
      (let ((expected (or title "project"))
            (worktree (equal setting "yes")))
        (cl-letf (((symbol-function 'org-agent-deck--call)
                   (lambda (body &rest args)
                     (should (equal (cadr (member "--title" args)) expected))
                     (should (equal (cadr (member "--worktree" args))
                                    (and worktree expected)))
                     (should (equal (and (member "--new-branch" args) t) worktree))
                     (should (equal (cadr (member "--location" args))
                                    (and worktree "subdirectory")))
                     (org-agent-deck-test--launch-reply body args))))
          (let ((result
                 (org-babel-execute:agent-deck
                  "Prompt" (append (when title `((:title . ,title)))
                                   (when setting `((:worktree . ,setting)))
                                   '((:preset . "work") (:directory . "~/src/project/"))))))
            (if worktree
                (progn
                  (should (string-match-p
                           (regexp-quote (concat "Directory: ~/src/project/.worktrees/" expected))
                           result))
                  (should (string-match-p (concat "\nBranch: " expected) result)))
              (should-not (string-match-p "\nBranch:" result)))))))))

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
                  (:thinking . ,(cadr case)) (:ultracode . "no"))))))

(ert-deftest org-agent-deck-babel-ultracode-per-harness ()
  "Claude's Ultracode is a settings overlay beside its effort; Codex's is the
ultra effort, which is max reasoning with delegation.  Presets may say t,
nil, yes or no, and headers override them."
  (let ((org-agent-deck-presets
         (append '(("ultra" . ((:group . "g") (:harness . "claude")
                               (:thinking . "max") (:ultracode . t)))
                   ("ultra-yes" . ((:group . "g") (:harness . "claude")
                                   (:thinking . "max") (:ultracode . "yes")))
                   ("off" . ((:group . "g") (:harness . "claude")
                             (:thinking . "max") (:ultracode . nil))))
                 org-agent-deck-presets))
        (overlay "--extra-arg=--settings={\"ultracode\":true}"))
    ;; (HEADERS EFFORT CLAUDE-OVERLAY ULTRACODE-REPORTED)
    (dolist (case `((((:harness . "claude") (:thinking . "max") (:ultracode . "yes"))
                     "max" t t)
                    (((:harness . "claude") (:ultracode . "yes")) nil t t)
                    ;; Claude runs Ultracode at any effort.
                    (((:harness . "claude") (:thinking . "high") (:ultracode . "yes"))
                     "high" t t)
                    (((:preset . "claude") (:ultracode . "yes")) "xhigh" t t)
                    (((:harness . "claude") (:thinking . "max") (:ultracode . "no"))
                     "max" nil nil)
                    (((:preset . "ultra")) "max" t t)
                    (((:preset . "ultra-yes")) "max" t t)
                    (((:ultracode . "no") (:preset . "ultra")) "max" nil nil)
                    (((:preset . "off")) "max" nil nil)
                    (((:ultracode . "yes") (:preset . "off")) "max" t t)
                    (((:preset . "work") (:ultracode . "yes") (:worktree . "yes")
                      (:title . "fix"))
                     "max" t t)
                    (((:harness . "codex") (:thinking . "max") (:ultracode . "yes"))
                     "ultra" nil t)
                    (((:harness . "codex") (:ultracode . "yes")) "ultra" nil t)
                    (((:harness . "codex") (:ultracode . "yes") (:remote . "vulcan"))
                     "ultra" nil t)
                    (((:harness . "codex") (:thinking . "default") (:ultracode . "yes"))
                     "ultra" nil t)
                    (((:harness . "codex") (:thinking . "ultra") (:ultracode . "yes"))
                     "ultra" nil t)
                    ;; The ultra effort is Codex's Ultracode, so it is reported.
                    (((:harness . "codex") (:thinking . "ultra")) "ultra" nil t)
                    (((:harness . "codex") (:thinking . "max") (:ultracode . "no"))
                     "max" nil nil)))
      (let (calls result)
        (cl-letf (((symbol-function 'org-agent-deck--call)
                   (lambda (input &rest args)
                     (push args calls)
                     (org-agent-deck-test--launch-reply input args))))
          (setq result
                (org-babel-execute:agent-deck
                 "Prompt" (append (car case)
                                  '((:group . "g") (:directory . "/remote"))))))
        (should (= (length calls) 1))
        (let ((args (car calls)))
          (should (equal (cadr (member "--effort" args)) (nth 1 case)))
          (should (equal (and (member overlay args) t) (nth 2 case)))
          (should-not (seq-some (lambda (arg) (string-prefix-p "--settings" arg)) args)))
        (should (string-match-p
                 (concat "^Requested thinking: "
                         (regexp-quote (or (nth 1 case) "(harness default)")) "$")
                 result))
        (should (equal (and (string-match-p "^Requested ultracode: yes$" result) t)
                       (nth 3 case)))))))

(ert-deftest org-agent-deck-presets-work-runs-claude-at-max ()
  "The work preset runs Claude at max effort; its Ultracode waits for the Nix
claude wrapper that admits it (nix-sko41).  Customize accepts the presets,
with t or nil allowed only for :ultracode."
  (let ((standard (eval (car (get 'org-agent-deck-presets 'standard-value)) t))
        (widget (widget-convert (get 'org-agent-deck-presets 'custom-type))))
    (should (equal (assoc "work" standard)
                   '("work" . ((:group . "Positron") (:harness . "claude")
                               (:model . "claude-opus-5-5") (:thinking . "max")
                               (:ultracode . nil)))))
    (should (widget-apply widget :match standard))
    (should (widget-apply widget :match '(("x" (:group . "g") (:ultracode)))))
    (dolist (bad '((("x" (:worktree . t))) (("x" (:harness . t)))
                   (("x" (:mailbox))) (("x" (:ultracode . 1)))))
      (should-not (widget-apply widget :match bad)))))

(ert-deftest org-agent-deck-babel-ultracode-errors-say-how-to-turn-it-off ()
  "Ultracode that the harness cannot run fails before launch, whether a
header or the work preset asks for it, and the error names :ultracode no.
A preset value other than yes, no, t or nil names the preset."
  (let ((org-agent-deck-presets
         (append '(("bad" . ((:group . "g") (:harness . "claude")
                             (:ultracode . "maybe")))
                   ("ultra" . ((:group . "g") (:harness . "claude")
                               (:thinking . "max") (:ultracode . t))))
                 org-agent-deck-presets))
        launched)
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (&rest _) (setq launched t) (ert-fail "Unexpected launch"))))
      (dolist (params `(((:harness . "pi")) ((:harness . "gemini"))
                        ,@(mapcar (lambda (thinking)
                                    `((:harness . "codex") (:thinking . ,thinking)))
                                  '("minimal" "low" "medium" "high" "xhigh"))))
        ;; Ultracode comes from a header, or from a preset that says t.
        (dolist (source '(((:ultracode . "yes") (:preset . "work"))
                          ((:preset . "ultra"))))
          (let ((err (should-error
                      (org-babel-execute:agent-deck
                       "Prompt" (append params source '((:directory . "/remote"))))
                      :type 'user-error)))
            (should (string-search ":ultracode no" (error-message-string err))))
          ;; On failure, ERT reports the first parameters that launched.
          (should-not (and launched (cons source params)))))
      (let ((err (should-error
                  (org-babel-execute:agent-deck
                   "Prompt" '((:preset . "bad") (:directory . "/remote")))
                  :type 'user-error)))
        (should (string-search "preset bad" (error-message-string err))))
      (should-not launched))))

(ert-deftest org-agent-deck-babel-ultracode-header-needs-yes-or-no ()
  "An :ultracode header written without yes or no fails before launch, as a
bare :worktree does, instead of reading as no under the work preset."
  (let (launched)
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (&rest _) (setq launched t) (ert-fail "Unexpected launch"))))
      (dolist (header '(":ultracode" ":ultracode t" ":ultracode 'nil"))
        (with-temp-buffer
          (insert "#+begin_src agent-deck :preset work :directory /remote "
                  header "\nPrompt\n#+end_src\n")
          (org-mode)
          (goto-char (point-min))
          (let ((org-confirm-babel-evaluate nil))
            (should-error (org-babel-execute-src-block) :type 'user-error)))
        (should-not (and launched header))))))

(ert-deftest org-agent-deck-babel-refused-ultracode-overlay-is-never-retried ()
  "A claude wrapper that refuses the Ultracode overlay ends the session at
once.  That launch fails without a retry, and only a Claude Ultracode
launch suggests :ultracode no."
  (dolist (case '((((:ultracode . "yes") (:preset . "work")) t)
                  (((:preset . "claude")) nil)))
    (let ((calls 0))
      (cl-letf (((symbol-function 'org-agent-deck--call)
                 (lambda (&rest _)
                   (cl-incf calls)
                   "{\"success\":true,\"session_id\":\"s1\",\"status\":\"error\",\"message_pending\":false,\"message\":\"Prompt\"}")))
        (let ((err (should-error
                    (org-babel-execute:agent-deck
                     "Prompt" (append (car case) '((:directory . "/remote"))))
                    :type 'user-error)))
          (should (string-search "(status error)" (error-message-string err)))
          (should (equal (and (string-search ":ultracode no" (error-message-string err))
                              t)
                         (cadr case)))))
      (should (= calls 1)))))

(ert-deftest org-agent-deck-babel-explicit-settings-without-preset ()
  (cl-letf (((symbol-function 'org-agent-deck--call)
             (lambda (body &rest args)
               (should (equal (cadr (member "--cmd" args)) "pi"))
               (should (equal (cadr (member "--group" args)) "custom/group"))
               (should-not (member "--wrapper" args))
               (org-agent-deck-test--launch-reply body args))))
    (org-babel-execute:agent-deck
     "Prompt" '((:directory . "/remote") (:group . "custom/group")))))

(ert-deftest org-agent-deck-babel-remote-launches-through-controller ()
  "A :remote block has the controller's agent-deck launch on that remote."
  (let ((org-agent-deck-presets
         (cons '("on-vulcan" . ((:group . "my-sessions") (:remote . "vulcan")))
               org-agent-deck-presets))
        (body "Review λ.\nKeep \"quotes\" and $HOME.\n"))
    (dolist (case '((((:remote . "vulcan") (:preset . "work"))
                     ("remote" "exec" "vulcan" "launch") "vulcan")
                    (((:preset . "on-vulcan"))
                     ("remote" "exec" "vulcan" "launch") "vulcan")
                    (((:preset . "work")) ("launch") nil)))
      (let (calls result)
        (cl-letf (((symbol-function 'org-agent-deck--call)
                   (lambda (input &rest args)
                     (push (cons input args) calls)
                     (org-agent-deck-test--launch-reply input args))))
          (setq result
                (org-babel-execute:agent-deck
                 body (append (car case) '((:directory . "~/src/project"))))))
        (should (= (length calls) 1))
        (pcase-let ((`(,input . ,args) (car calls)))
          (should (equal input body))
          (should (equal (seq-take args (length (nth 1 case))) (nth 1 case)))
          (should (equal (cadr (member "--message-file" args)) "-"))
          (should (equal (car (last args)) "~/src/project/")))
        (if (nth 2 case)
            (should (string-match-p (concat "^Remote: " (nth 2 case) "$") result))
          (should-not (string-match-p "^Remote:" result)))))))

(ert-deftest org-agent-deck-babel-mailbox-joins-before-prompt ()
  "With :mailbox, /mailbox runs as its own command and the prompt follows it.
The prompt send holds until the session is idle, so the join's turn ends
first; on a remote, every call goes through that remote."
  (dolist (remote '(nil "vulcan"))
    (let* ((run (org-agent-deck-test--mailbox-block
                 (concat (if remote (concat ":remote " remote " ") "")
                         ":ultracode yes :mailbox ob-agent-deck-mail ++work !+review")))
           (prefix (when remote (list "remote" "exec" remote)))
           (send (lambda (hold)
                   (append prefix
                           `("session" "send" "fresh-session" "--json"
                             "--no-tag" "--defer-if-busy" "--defer-timeout" ,hold
                             "--message-file" "-")))))
      (should (equal (plist-get run :calls)
                     `((,(append prefix
                                 '("launch" "--json" "--no-parent"
                                   "--no-assert-done" "--group" "Positron"
                                   "--cmd" "claude" "--title" "ob-agent-deck-mail"
                                   "--model" "claude-opus-5-5" "--effort" "max"
                                   "--extra-arg=--settings={\"ultracode\":true}"
                                   "~/src/project/"))
                        . "")
                       ;; Emacs waits for this send, so its hold is short.
                       (,(funcall send "10m")
                        . "/mailbox ob-agent-deck-mail ++work !+review")
                       ;; Babel passes the body without its final newline.
                       (,(funcall send "30m") . "Fix the capture issue."))))
      ;; Longer results become an example block instead of ": " lines.
      (should (string-match-p
               "^\\(: \\)?Mailbox: /mailbox ob-agent-deck-mail \\+\\+work !\\+review$"
               (plist-get run :buffer)))
      (should (string-match-p "^\\(: \\)?Prompt: " (plist-get run :buffer)))
      (should (string-match-p "^\\(: \\)?Requested ultracode: yes$"
                              (plist-get run :buffer)))
      (should-not (plist-get run :warnings))
      (should (seq-some (lambda (text) (string-search "fresh-session" text))
                        (plist-get run :messages))))))

(ert-deftest org-agent-deck-babel-mailbox-warns-when-prompt-undelivered ()
  "A background prompt send that fails, answers for another message, or
cannot confirm that the agent took the prompt raises one warning naming
the session and the reason."
  (dolist (case '(("exit" "target still busy") ("reply" "Another prompt")
                  ("unknown" "\"confirmation\":\"unknown\"")))
    (let* ((process-environment (cons (concat "FAKE_PROMPT_FAILS=" (car case))
                                      process-environment))
           (run (org-agent-deck-test--mailbox-block
                 ":mailbox ob-agent-deck-mail ++work !+review"))
           (warning (car (plist-get run :warnings))))
      (should (= (length (plist-get run :calls)) 3))
      (should (= (length (plist-get run :warnings)) 1))
      (should (eq (nth 0 warning) 'org-agent-deck))
      (should (eq (nth 2 warning) :error))
      (should (string-search "fresh-session" (nth 1 warning)))
      (should (string-search (cadr case) (nth 1 warning)))
      (should-not (seq-some (lambda (text) (string-search "fresh-session" text))
                            (plist-get run :messages))))))

(ert-deftest org-agent-deck-babel-mailbox-prompt-waits-in-background ()
  "The block returns while agent-deck still holds the prompt send.
Joining takes minutes, so Emacs must not wait for the prompt."
  (let (held-text held-messages)
    (let ((run (org-agent-deck-test--mailbox-block
                ":mailbox ob-agent-deck-mail ++work !+review"
                (lambda (text messages)
                  (setq held-text text
                        held-messages messages)))))
      (should (string-match-p "^\\(: \\)?Prompt: " held-text))
      (should-not (seq-some (lambda (text) (string-search "fresh-session" text))
                            held-messages))
      (should (seq-some (lambda (text) (string-search "fresh-session" text))
                        (plist-get run :messages))))))

(ert-deftest org-agent-deck-babel-mailbox-names-session-when-prompt-cannot-start ()
  "A prompt send that cannot even start still names the session /mailbox joined."
  (cl-letf (((symbol-function 'org-agent-deck--call)
             (lambda (input &rest args)
               (if (member "launch" args)
                   (org-agent-deck-test--launch-reply input args)
                 (json-serialize
                  `(:success t :session_id "fresh-session" :message ,input
                    :delivery "submitted" :submitted t :confirmation "confirmed")))))
            ((symbol-function 'org-agent-deck--start)
             (lambda (&rest _) (user-error "Cannot run ssh: No such file"))))
    (let ((err (should-error
                (org-babel-execute:agent-deck
                 "Prompt" '((:preset . "work") (:directory . "/remote")
                            (:mailbox . "remote")))
                :type 'user-error)))
      (should (string-search "fresh-session" (error-message-string err)))
      (should (string-search "Cannot run ssh" (error-message-string err))))))

(ert-deftest org-agent-deck-babel-mailbox-failure-withholds-prompt ()
  "Unless agent-deck saw the agent take up /mailbox, the prompt is never
sent, nothing records success, and the error names the new session.
An unconfirmed /mailbox might not mark the session busy, and the prompt
would then join its turn."
  (dolist (reply '(process-failed interrupted
                   "{\"success\":false,\"error\":\"menu_open\"}"
                   "{\"success\":true,\"message\":\"/mailbox someone-else\",\"delivery\":\"submitted\",\"submitted\":true,\"confirmation\":\"confirmed\"}"
                   "{\"success\":true,\"message\":\"/mailbox remote\",\"delivery\":\"delivered\",\"submitted\":false,\"confirmation\":\"unknown\"}"
                   "{\"success\":true,\"message\":\"/mailbox remote\",\"delivery\":\"queued\",\"submitted\":false,\"confirmation\":\"confirmed\"}"
                   "not JSON"))
    (with-temp-buffer
      (org-mode)
      (insert "#+begin_src agent-deck :preset work :directory /remote :mailbox remote\n"
              "Prompt\n#+end_src\n")
      (goto-char (point-min))
      (let ((org-confirm-babel-evaluate nil) sends started)
        (cl-letf (((symbol-function 'org-agent-deck--call)
                   (lambda (input &rest args)
                     (if (member "launch" args)
                         (org-agent-deck-test--launch-reply input args)
                       (push input sends)
                       (pcase reply
                         ('process-failed (user-error "Delivery failed: menu_open"))
                         ;; C-g while Emacs waits for the send.
                         ('interrupted (signal 'quit nil))
                         (_ reply)))))
                  ((symbol-function 'org-agent-deck--start)
                   (lambda (&rest _) (setq started t))))
          (let ((err (should-error (org-babel-execute-src-block) :type 'user-error)))
            (should (string-search "fresh-session" (error-message-string err)))))
        (should (equal sends '("/mailbox remote")))
        (should-not started)
        (should-not (string-search "#+RESULTS:" (buffer-string)))))))

(ert-deftest org-agent-deck-babel-mailbox-name-titles-the-session ()
  "Agent-mail binds a session by its title, so an untitled session takes the
mailbox name, and an explicit title may differ from it only in case."
  (dolist (case `((nil "fix-capture" "fix-capture")
                  ("Fix-Capture" "fix-capture" "Fix-Capture")
                  (nil "pi.2-review" "pi.2-review")
                  (nil ,(make-string 64 ?a) ,(make-string 64 ?a))))
    (let (titles)
      (cl-letf (((symbol-function 'org-agent-deck--call)
                 (lambda (input &rest args)
                   (if (member "launch" args)
                       (progn (push (cadr (member "--title" args)) titles)
                              (org-agent-deck-test--launch-reply input args))
                     (json-serialize
                      `(:success t :session_id "fresh-session" :message ,input
                        :delivery "submitted" :submitted t
                        :confirmation "confirmed")))))
                ((symbol-function 'org-agent-deck--start) #'ignore))
        (org-babel-execute:agent-deck
         "Prompt" `(,@(when (car case) `((:title . ,(car case))))
                    (:mailbox . ,(cadr case))
                    (:preset . "work") (:directory . "/remote/project"))))
      (should (equal titles (list (nth 2 case)))))))

(ert-deftest org-agent-deck-babel-mailbox-rejects-bad-names-before-launch ()
  "Names and topics that would stop /mailbox to ask John never launch."
  (let (launched)
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (&rest _) (setq launched t) (ert-fail "Unexpected launch"))))
      (dolist (params `(((:mailbox)) ((:mailbox . "")) ((:mailbox . " "))
                        ((:mailbox . 12))
                        ((:mailbox . "Upper")) ((:mailbox . "under_score"))
                        ((:mailbox . "two--dashes")) ((:mailbox . "trailing-"))
                        ((:mailbox . "-leading")) ((:mailbox . "bad\0name"))
                        ((:mailbox . "claude")) ((:mailbox . "john-review"))
                        ((:mailbox . ,(make-string 65 ?a)))
                        ((:mailbox . "review") (:title . "project"))
                        ((:mailbox . "review topic")) ((:mailbox . "review -topic"))
                        ((:mailbox . "review !topic")) ((:mailbox . "review +"))
                        ((:mailbox . "review +Topic")) ((:mailbox . "review +++topic"))
                        ((:mailbox . "review ++all"))))
        (should-error
         (org-babel-execute:agent-deck
          "Prompt" (append params '((:preset . "work") (:directory . "/remote"))))
         :type 'user-error)
        ;; On failure, ERT reports the first parameters that launched.
        (should-not (and launched params))))))

(ert-deftest org-agent-deck-babel-rejects-invalid-settings-before-launch ()
  ;; The launch wrapper converts every call failure into a `user-error',
  ;; so a launch attempt must be recorded rather than signaled.
  (let (launched)
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (&rest _) (setq launched t) (ert-fail "Unexpected launch"))))
      (dolist (params '(((:preset . "unknown")) ((:directory . ""))
                        ((:directory . "--bad")) ((:directory . "relative/path"))
                        ((:group . 12)) ((:title . " ")) ((:title . "bad\0title"))
                        ((:harness . "pi; touch BAD")) ((:model . "$(touch BAD)"))
                        ((:harness . "pi") (:thinking . "unlimited") (:ultracode . "no"))
                        ((:ultracode . "maybe")) ((:ultracode . 1))
                        ;; Headers say yes or no; only presets may say t or nil.
                        ((:ultracode)) ((:ultracode . t))
                        ((:harness . "pi") (:ultracode . "yes"))
                        ((:harness . "gemini") (:ultracode . "yes"))
                        ((:harness . "codex") (:thinking . "high") (:ultracode . "yes"))
                        ;; Codex's Ultracode needs max reasoning.
                        ((:harness . "codex") (:thinking . "xhigh") (:ultracode . "yes"))
                        ((:harness . "codex") (:thinking . "ultra") (:ultracode . "no"))
                        ((:dir . "/remote"))
                        ((:cache . "yes")) ((:session . "existing"))
                        ((:directory . "/")) ((:worktree . "maybe"))
                        ((:worktree . t)) ((:worktree . nil))
                        ((:worktree . "yes") (:title . "Design review"))
                        ((:worktree . "yes") (:title . "topic/name"))
                        ((:remote . "")) ((:remote . 12)) ((:remote . "--help"))
                        ((:remote . "johnw@vulcan")) ((:remote . "vulcan.lan"))
                        ((:remote . "vulcan; touch BAD"))))
        (should-error
         (org-babel-execute:agent-deck
          "Prompt" (append params '((:preset . "work") (:directory . "/remote"))))
         :type 'user-error)
        ;; On failure, ERT reports the first parameters that launched.
        (should-not (and launched params)))
      (should-error (org-babel-execute:agent-deck "Prompt" '((:preset . "work")))
                    :type 'user-error)
      (should-error (org-babel-execute:agent-deck "Prompt" '((:directory . "/remote")))
                    :type 'user-error)
      (dolist (body '("" " \n " "Bad\0prompt"))
        (should-error
         (org-babel-execute:agent-deck body '((:preset . "work") (:directory . "/remote")))
         :type 'user-error))
      (should-not launched))))

(ert-deftest org-agent-deck-babel-failures-never-retry-or-record-success ()
  (dolist (reply '("not JSON" "[]" "{\"success\":false,\"error\":\"unsupported model\"}"
                   "{\"success\":true}"
                   "{\"success\":true,\"id\":\"queued-id\",\"status\":\"queued\"}"
                   "{\"success\":true,\"id\":\"pending-id\",\"message_pending\":true}"
                   "{\"success\":true,\"id\":\"bad-prompt\",\"message\":\"different\"}"
                   ;; An older claude wrapper refuses the work preset's Ultracode
                   ;; overlay, and the session ends at once.
                   "{\"success\":true,\"id\":\"error-id\",\"status\":\"error\",\"message_pending\":false,\"message\":\"Prompt\"}"
                   "{\"success\":true,\"id\":\"stopped-id\",\"status\":\"stopped\",\"message_pending\":false,\"message\":\"Prompt\"}"
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
  ;; As above, a launch attempt is recorded because the launch wrapper
  ;; would turn the signaled failure into the expected `user-error'.
  (let (launched)
    (cl-letf (((symbol-function 'org-agent-deck--call)
               (lambda (&rest _) (setq launched t) (ert-fail "Unexpected launch"))))
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
          (should-error (org-export-as 'md) :type 'user-error))))
    (should-not launched)))

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

(ert-deftest org-agent-deck-start-preserves-argv-and-stdin-in-background ()
  "The background runner passes argv and stdin as `org-agent-deck--call' does.
It reports output or a diagnostic once, and leaves no process or buffer."
  (let* ((directory (make-temp-file "org-agent-deck-start-" t))
         (ssh (org-agent-deck-test--script
               directory "ssh" "#!/bin/sh\nshift\nexec /bin/sh -c \"$*\"\n"))
         (endpoint (org-agent-deck-test--script
                    directory "argv-echo" "#!/bin/sh\nprintf '%s\\0' \"$@\"\ncat\n"))
         (failing (org-agent-deck-test--script
                   directory "unavailable"
                   (concat "#!/bin/sh\ncat >/dev/null\necho 'partial output'\n"
                           "echo 'remote agent-deck is unavailable' >&2\nexit 3\n")))
         (marker (expand-file-name "injected" directory))
         (payload (format "λ ' \" $HOME `uname`\n$(touch %s)\n" marker))
         (arguments (list "session" "send" "id" "--json" "--message-file" "-"
                          "~/remote dir/quotes'\"; $(false)")))
    (unwind-protect
        (progn
          (dolist (prefix (list (list endpoint) (list ssh "hera" endpoint)))
            (let ((org-agent-deck-command prefix) reports)
              (apply #'org-agent-deck--start payload
                     (lambda (&rest report) (push report reports))
                     arguments)
              (should (org-agent-deck-test--wait (lambda () reports)))
              (should (equal reports
                             (list (list (concat (mapconcat #'identity arguments "\0")
                                                 "\0" payload)
                                         nil))))))
          (let ((org-agent-deck-command (list failing)) reports)
            (apply #'org-agent-deck--start payload
                   (lambda (&rest report) (push report reports))
                   arguments)
            (should (org-agent-deck-test--wait (lambda () reports)))
            (should (= (length reports) 1))
            (should-not (car (car reports)))
            (should (string-match-p "(exit 3): remote agent-deck is unavailable\n+partial output"
                                    (cadr (car reports)))))
          (should-not (file-exists-p marker))
          (should-not (seq-some (lambda (process)
                                  (string-prefix-p "org-agent-deck" (process-name process)))
                                (process-list)))
          (should-not (seq-some (lambda (buffer)
                                  (string-prefix-p " *org-agent-deck" (buffer-name buffer)))
                                (buffer-list))))
      (delete-directory directory t))))

(ert-deftest org-agent-deck-start-reports-when-its-buffer-is-killed ()
  "Killing the runner's hidden buffer ends the run, which still reports
one failure and leaves no process or buffer behind."
  (let* ((directory (make-temp-file "org-agent-deck-start-killed-" t))
         (org-agent-deck-command
          (list (org-agent-deck-test--script
                 directory "slow" "#!/bin/sh\ncat >/dev/null\nexec sleep 30\n")))
         reports)
    (unwind-protect
        (let ((process (org-agent-deck--start
                        "input" (lambda (&rest report) (push report reports))
                        "session" "send")))
          (let ((kill-buffer-query-functions nil))
            (kill-buffer (process-buffer process)))
          (should (org-agent-deck-test--wait (lambda () reports)))
          (should (= (length reports) 1))
          (should-not (car (car reports)))
          (should (string-search "failed" (cadr (car reports))))
          (should-not (seq-some (lambda (process)
                                  (string-prefix-p "org-agent-deck" (process-name process)))
                                (process-list)))
          (should-not (seq-some (lambda (buffer)
                                  (string-prefix-p " *org-agent-deck" (buffer-name buffer)))
                                (buffer-list))))
      (delete-directory directory t))))

(ert-deftest org-agent-deck-babel-edit-prompt-in-org-mode ()
  (save-window-excursion
    (with-temp-buffer
      (org-mode)
      (insert "#+begin_src agent-deck\n- Plan\n#+end_src\n")
      (goto-char (point-min))
      (forward-line 1)
      (unwind-protect
          (progn
            (org-edit-special)
            (should (eq major-mode 'org-mode))
            (should (org-src-edit-buffer-p))
            (goto-char (point-max))
            (insert "- Verify\n")
            (org-edit-src-exit))
        (when (org-src-edit-buffer-p) (org-edit-src-abort)))
      (should (string-match-p "- Verify" (buffer-string))))))

(provide 'org-agent-deck-test)

;;; org-agent-deck-test.el ends here
