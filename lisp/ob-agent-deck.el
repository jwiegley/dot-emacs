;;; ob-agent-deck.el --- Launch agent-deck sessions from Babel -*- lexical-binding: t; -*-

;; Copyright (C) 2026 John Wiegley
;; Author: John Wiegley <johnw@gnu.org>
;; Keywords: outlines tools

;;; Commentary:

;; The block body is the starting prompt.  Headers select a preset and a
;; directory on the agent-deck host, with optional per-block overrides.
;; :remote names a remote registered with that host's agent-deck, such as
;; vulcan; the host's agent-deck then launches the session there.
;; :mailbox NAME [TOPICS] runs /mailbox NAME [TOPICS] as the session's first
;; command; the prompt follows in the background once that turn ends.
;; :ultracode yes turns on standing dynamic-workflow orchestration: a
;; settings overlay for Claude, and Codex's ultra effort, which is max
;; reasoning with delegation.  Each successful execution launches a fresh,
;; standalone session.  See org-agent-deck-README.org for configuration,
;; examples, and limitations.

;;; Code:

(require 'ob)
(require 'org-src)
(require 'org-agent-deck)

(add-to-list 'org-src-lang-modes '("agent-deck" . org))

(defcustom org-agent-deck-presets
  '(("work" . ((:group . "Positron")
               (:harness . "claude")
               (:model . "claude-opus-5-5")
               (:thinking . "max")
               ;; t once the Nix claude wrapper admits Ultracode (nix-sko41).
               (:ultracode . nil)))
    ("work-codex" . ((:group . "Positron")
                     (:harness . "pi")
                     (:model . "openai-codex/gpt-6-astra")
                     (:thinking . "max")))
    ("claude" . ((:group . "my-sessions")
                 (:harness . "claude")
                 (:model . "claude-opus-5-5")
                 (:thinking . "xhigh")))
    ("local" . ((:group . "my-sessions")
                (:harness . "pi")
                (:model . "omlx-hera/GLM-5.3-Flash-oQ4e-mtp")
                (:thinking . "max"))))
  "Launch defaults selected by the agent-deck Babel :preset header.
Explicit and inherited headers take precedence over these defaults.
Values are strings, except that :ultracode may also be t or nil."
  :type '(alist :key-type string
                :value-type (alist :key-type symbol :value-type string
                                   :options ((:ultracode
                                              (choice (const :tag "On" t)
                                                      (const :tag "Off" nil)
                                                      (const "yes")
                                                      (const "no"))))))
  :group 'org-agent-deck)

(defvar org-babel-default-header-args:agent-deck
  '((:results . "verbatim replace")
    (:exports . "code")
    (:eval . "never-export")
    (:cache . "no"))
  "Default header arguments for agent-deck blocks.
Launching has side effects; results are not cached and export does not launch.")

(defun org-babel-agent-deck--mail-name-p (name)
  "Return non-nil if NAME follows agent-mail's naming standard.
Session and channel names use lower-case letters, digits, . and -,
start with a letter or digit, have no -- and no trailing -, are at
most 64 characters long, and avoid the names agent-mail reserves."
  (let ((case-fold-search nil))
    (and (<= (length name) 64)
         (string-match-p "\\`[a-z0-9]\\(?:[a-z0-9.-]*[a-z0-9.]\\)?\\'" name)
         (not (string-search "--" name))
         (not (string-prefix-p "john-" name))
         (not (member name '("all" "everyone" "john" "johnw" "jwiegley" "user"
                             "human" "operator" "owner" "admin" "root" "system"
                             "claude" "anthropic" "codex" "agent-deck"
                             "agent-mail"))))))

(defun org-babel-agent-deck--options (params)
  "Merge and validate launch settings in Babel PARAMS."
  (let* ((preset (cdr (assq :preset params)))
         (defaults (and (stringp preset)
                        (assoc preset org-agent-deck-presets)))
         (options (append params (cdr defaults))))
    (when (and preset (not defaults))
      (user-error "Unknown agent-deck :preset %S (available: %s)"
                  preset (mapconcat #'car org-agent-deck-presets ", ")))
    (dolist (key '(:directory :group :harness :mailbox :model :remote :thinking
                              :title))
      (let ((value (cdr (assq key options))))
        (when (and value
                   (or (not (stringp value))
                       (string-empty-p (string-trim value))
                       (string-match-p "\0" value)))
          (user-error "agent-deck %s must be a non-empty string without NUL" key))))
    (when (and (assq :worktree options)
               (not (member (cdr (assq :worktree options)) '("yes" "no"))))
      (user-error "agent-deck :worktree must be yes or no"))
    ;; Headers say yes or no, as :worktree does; a header written without a
    ;; value arrives as nil.  Presets may also say t or nil.
    (when (and (assq :ultracode params)
               (not (member (cdr (assq :ultracode params)) '("yes" "no"))))
      (user-error "agent-deck :ultracode must be yes or no"))
    (when (and (assq :ultracode (cdr defaults))
               (not (member (cdr (assq :ultracode (cdr defaults)))
                            '("yes" "no" t nil))))
      (user-error "agent-deck preset %s: :ultracode must be yes, no, t or nil"
                  preset))
    (dolist (key '(:directory :group))
      (unless (cdr (assq key options))
        (user-error "agent-deck requires %s (directly or via a preset)" key)))
    ;; Use :directory, not Babel's :dir, which changes Emacs's working directory.
    (when (assq :dir params)
      (user-error "Use :directory for the agent-deck host, not Babel :dir"))
    (when (equal (cdr (assq :cache params)) "yes")
      (user-error "agent-deck launches cannot use :cache yes"))
    (unless (member (cdr (assq :session params)) '(nil "none"))
      (user-error "agent-deck blocks always launch fresh sessions; omit :session"))
    (let ((directory (cdr (assq :directory options))))
      (unless (or (string-prefix-p "/" directory)
                  (string-prefix-p "~/" directory))
        (user-error "agent-deck :directory must be absolute or begin with ~/ on the target host")))
    (let ((harness (or (cdr (assq :harness options)) "pi"))
          (model (cdr (assq :model options)))
          (remote (cdr (assq :remote options)))
          (thinking (cdr (assq :thinking options))))
      (unless (string-match-p "\\`[[:alnum:]_-]+\\'" harness)
        (user-error "agent-deck :harness must be a tool name, not a command"))
      (when (and remote
                 (not (string-match-p "\\`[[:alnum:]][[:alnum:]_-]*\\'" remote)))
        (user-error "agent-deck :remote must be an agent-deck remote name, not a host or command"))
      (when (and model
                 (not (string-match-p "\\`[[:alnum:]/._:+@-]+\\'" model)))
        (user-error "agent-deck :model must be a model ID, not shell syntax or a pattern"))
      (when (and (equal harness "pi") thinking
                 (not (member thinking
                              '("default" "off" "minimal" "low" "medium"
                                "high" "xhigh" "max"))))
        (user-error "Invalid Pi :thinking %S" thinking))
      (let ((ultracode (assq :ultracode options)))
        (if (member (cdr ultracode) '("yes" t))
            (pcase harness
              ("claude" nil)
              ;; Codex's Ultracode is its ultra effort, which reasons at max.
              ("codex"
               (unless (member thinking '(nil "default" "max" "ultra"))
                 (user-error "Codex Ultracode is its ultra effort, max reasoning with delegation; use :thinking max, omit :thinking, or add :ultracode no")))
              (_ (user-error "agent-deck :ultracode needs :harness claude or codex; add :ultracode no")))
          ;; The ultra effort cannot run without Codex's Ultracode.
          (when (and ultracode (equal harness "codex") (equal thinking "ultra"))
            (user-error "Codex's ultra effort is its Ultracode; drop :ultracode no or choose another :thinking")))))
    (when (and (assq :mailbox options) (not (cdr (assq :mailbox options))))
      (user-error "agent-deck :mailbox needs a name, optionally followed by topics"))
    ;; /mailbox stops to ask John about a name or topic it cannot use, and
    ;; the prompt would then arrive as his answer.  Refuse those here.
    (when-let* ((mailbox (cdr (assq :mailbox options))))
      (let ((words (split-string mailbox)))
        (unless (org-babel-agent-deck--mail-name-p (car words))
          (user-error "agent-deck :mailbox name %S breaks agent-mail's naming standard"
                      (car words)))
        (dolist (topic (cdr words))
          (unless (and (string-match "\\`!?\\+\\+?" topic)
                       (org-babel-agent-deck--mail-name-p
                        (substring topic (match-end 0))))
            (user-error "agent-deck :mailbox topic %S must be +NAME, ++NAME, !+NAME or !++NAME"
                        topic)))))
    options))

(defun org-babel-agent-deck--send-arguments (remote id hold)
  "Return arguments that send standard input to session ID on REMOTE.
REMOTE is nil for the controlling host.  The send holds while the
session is busy, for at most HOLD (a duration such as \"10m\"), so it
never joins a turn that is still running."
  (org-agent-deck--remote-arguments
   remote (list "session" "send" id "--json" "--no-tag" "--defer-if-busy"
                "--defer-timeout" hold "--message-file" "-")))

(defun org-babel-agent-deck--sent-p (reply message &optional submitted)
  "Return non-nil if agent-deck's parsed send REPLY confirms MESSAGE.
Agent-deck must confirm the delivery; with SUBMITTED, it must have seen
the agent take MESSAGE up, rather than queue it behind a running turn.
Agent-deck removes trailing line endings before delivery."
  (and (hash-table-p reply)
       (eq (gethash "success" reply) t)
       (equal (gethash "message" reply)
              (replace-regexp-in-string "[\r\n]+\\'" "" message))
       (if submitted
           (eq (gethash "submitted" reply) t)
         (equal (gethash "confirmation" reply) "confirmed"))))

(defun org-babel-agent-deck--send-later (remote id title body)
  "Send prompt BODY to session ID, titled TITLE, on REMOTE.
Return at once.  Agent-deck delivers BODY when the current turn ends;
report the outcome then, and never retry."
  (apply #'org-agent-deck--start body
         (lambda (output failure)
           (if (org-babel-agent-deck--sent-p
                (and output (ignore-errors (json-parse-string output)))
                body)
               (message "Agent-deck sent the prompt to %s (%s) after /mailbox"
                        title id)
             ;; A lost SSH connection can leave the remote send running, so
             ;; an unconfirmed prompt may still arrive.
             (display-warning
              'org-agent-deck
              (format "Agent-deck could not confirm the prompt for %s (%s) after /mailbox: %s\nCheck the session before sending the prompt yourself; nothing was retried."
                      title id (or failure (string-trim output)))
              :error)))
         (org-babel-agent-deck--send-arguments remote id "30m")))

;;;###autoload
(defun org-babel-execute:agent-deck (body params)
  "Launch a fresh agent-deck session with prompt BODY and Babel PARAMS.
With :remote, the controlling agent-deck launches on that remote.
Wait only for launch and initial prompt delivery, not task completion.
With :mailbox, wait for delivery of /mailbox instead, and send BODY in
the background once that turn ends.
Return launch details for Org results.  Never retry a failed launch."
  (when org-babel-exp-reference-buffer
    (user-error "agent-deck blocks cannot launch during export"))
  (when (or (string-empty-p (string-trim body)) (string-match-p "\0" body))
    (user-error "agent-deck requires a non-empty prompt without NUL"))
  (let* ((options (org-babel-agent-deck--options params))
         (directory (cdr (assq :directory options)))
         (group (cdr (assq :group options)))
         (harness (or (cdr (assq :harness options)) "pi"))
         (model (cdr (assq :model options)))
         (remote (cdr (assq :remote options)))
         (thinking (cdr (assq :thinking options)))
         (ultracode (member (cdr (assq :ultracode options)) '("yes" t)))
         (mailbox (when-let* ((value (cdr (assq :mailbox options))))
                    (split-string value)))
         (command (and mailbox (string-join (cons "/mailbox" mailbox) " ")))
         (title (or (cdr (assq :title options))
                    ;; Agent-mail binds a session under its title.
                    (car mailbox)
                    (file-name-nondirectory (directory-file-name directory))))
         (worktree (equal (cdr (assq :worktree options)) "yes"))
         (arguments (org-agent-deck--remote-arguments
                     remote
                     (append
                      (list "launch" "--json" "--no-parent" "--no-assert-done")
                      ;; Launch skips the guard that keeps a slash command
                      ;; from arriving as text, so /mailbox is sent later.
                      (unless command (list "--message-file" "-"))
                      (list "--group" group "--cmd" harness "--title" title)))))
    (when (string-empty-p (string-trim title))
      (user-error "Cannot derive a title from :directory; specify :title"))
    (when (and worktree (string-match-p "[/[:space:]]" title))
      (user-error "A worktree :title must be a Git branch name without spaces or /"))
    (when (and mailbox (not (equal (car mailbox) (downcase title))))
      (user-error "agent-deck :mailbox name %s must be the session title in lower case, %s"
                  (car mailbox) (downcase title)))
    (when (equal thinking "default") (setq thinking nil))
    (if (equal harness "pi")
        ;; Agent-deck's --model/--effort do not support Pi.  A native wrapper
        ;; retains its Pi identity and per-instance session directory.
        (when (or model thinking)
          (setq arguments
                (append arguments
                        (list "--wrapper"
                              (concat "{command} "
                                      (mapconcat
                                       #'shell-quote-argument
                                       (append (when model (list "--model" model))
                                               (when thinking
                                                 (list "--thinking" thinking)))
                                       " "))))))
      ;; Codex's Ultracode is its ultra effort, max reasoning with delegation.
      (when (equal harness "codex")
        (cond (ultracode (setq thinking "ultra"))
              ((equal thinking "ultra") (setq ultracode t))))
      ;; Let agent-deck validate supported native harness/model/effort flags.
      (setq arguments
            (append arguments (when model (list "--model" model))
                    (when thinking (list "--effort" thinking))
                    ;; Claude's Ultracode is a session setting.  Only a Nix
                    ;; claude wrapper that admits this one --settings overlay
                    ;; lets it through; an older one ends the session at once.
                    ;; Agent-deck keeps the argument across session restarts.
                    (when (and ultracode (equal harness "claude"))
                      (list "--extra-arg=--settings={\"ultracode\":true}")))))
    (when worktree
      (setq arguments
            (append arguments (list "--worktree" title "--new-branch"
                                    "--location" "subdirectory"))))
    (let* ((reply
            (condition-case err
                (org-agent-deck--json
                 (apply #'org-agent-deck--call (unless command body)
                        ;; Agent-deck trims surrounding quotes from its path
                        ;; argument.  A trailing slash protects quoted names.
                        (append arguments (list (file-name-as-directory directory))))
                 "Agent-deck launch")
              (error
               (user-error "%s\nA session or worktree may already exist; check agent-deck before retrying"
                           (error-message-string err)))))
           (id (and (hash-table-p reply)
                    (or (gethash "session_id" reply) (gethash "id" reply)))))
      (unless (and (hash-table-p reply) (eq (gethash "success" reply) t)
                   (stringp id) (not (string-empty-p id)))
        (user-error "Unconfirmed agent-deck launch: %S; check agent-deck before retrying"
                    reply))
      (when (or (member (gethash "status" reply) '("queued" "error" "stopped"))
                (unless command
                  (or (eq (gethash "message_pending" reply) t)
                      (not (equal (gethash "message" reply)
                                  (replace-regexp-in-string "[\r\n]+\\'" "" body))))))
        (user-error "Session %s was created, but prompt delivery is unconfirmed (status %s); inspect it before retrying%s"
                    id (gethash "status" reply)
                    (if (and ultracode (equal harness "claude")
                             (equal (gethash "status" reply) "error"))
                        "\nA claude wrapper that refuses the Ultracode --settings overlay ends the session at once; if so, retry with :ultracode no"
                      "")))
      (when command
        (let ((sent
               (condition-case err
                   (org-agent-deck--json
                    (apply #'org-agent-deck--call command
                           ;; Emacs waits for this send, so its hold is short.
                           (org-babel-agent-deck--send-arguments remote id "10m"))
                    "Agent-deck /mailbox send")
                 ((error quit)
                  (user-error "Session %s was created, but sending %s stopped: %s\nInspect it before retrying"
                              id command (error-message-string err))))))
          ;; The prompt waits only while the session reads busy, so the agent
          ;; must already have taken /mailbox up.
          (unless (org-babel-agent-deck--sent-p sent command t)
            (user-error "Session %s was created, but agent-deck did not see it take up %s: %S; inspect it before retrying"
                        id command sent)))
        (condition-case err
            (org-babel-agent-deck--send-later remote id title body)
          (error
           (user-error "Session %s took up %s, but its prompt was not sent: %s\nSend the prompt yourself"
                       id command (error-message-string err)))))
      (format "Session: %s%s\nTitle: %s\nGroup: %s\nDirectory: %s\nHarness: %s\nRequested model: %s\nRequested thinking: %s%s%s%s%s"
              id (if remote (concat "\nRemote: " remote) "")
              (or (gethash "title" reply) title)
              (or (gethash "group" reply) group)
              (or (gethash "path" reply) directory)
              (or (gethash "tool" reply) harness)
              (or model "(harness default)") (or thinking "(harness default)")
              (if ultracode "\nRequested ultracode: yes" "")
              (if worktree
                  (format "\nBranch: %s" (or (gethash "worktree_branch" reply) title))
                "")
              (if command
                  (format "\nMailbox: %s\nPrompt: pending until /mailbox finishes"
                          command)
                "")
              (if-let* ((warning (gethash "warning" reply)))
                  (concat "\nWarning: " warning)
                "")))))

(provide 'ob-agent-deck)
;;; ob-agent-deck.el ends here
