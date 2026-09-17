;;; ob-agent-deck.el --- Launch agent-deck sessions from Babel -*- lexical-binding: t; -*-

;; Copyright (C) 2026 John Wiegley
;; Author: John Wiegley <johnw@gnu.org>
;; Keywords: outlines tools

;;; Commentary:

;; The block body is the starting prompt.  Headers select a preset and a
;; directory on the agent-deck host, with optional per-block overrides.
;; Each successful execution launches a fresh, standalone session.  See
;; org-agent-deck-README.org for configuration, examples, and limitations.

;;; Code:

(require 'ob)
(require 'org-agent-deck)

(defcustom org-agent-deck-presets
  '(("work" . ((:group . "Positron")
               (:harness . "pi")
               (:model . "openai-codex/gpt-6-astra")
               (:thinking . "max")))
    ("personal" . ((:group . "my-sessions")
                   (:harness . "pi")
                   (:model . "omlx-hera/GLM-5.3-Flash-oQ4e"))))
  "Launch defaults selected by the agent-deck Babel :preset header.
Explicit and inherited headers take precedence over these defaults."
  :type '(alist :key-type string
                :value-type (alist :key-type symbol :value-type string))
  :group 'org-agent-deck)

(defvar org-babel-default-header-args:agent-deck
  '((:results . "verbatim replace") (:exports . "code")
    (:eval . "never-export") (:cache . "no"))
  "Default header arguments for agent-deck blocks.
Launching has side effects; results are not cached and export does not launch.")

(defun org-babel-agent-deck--options (params)
  "Merge and validate launch settings in Babel PARAMS."
  (let* ((preset (cdr (assq :preset params)))
         (defaults (and (stringp preset)
                        (assoc preset org-agent-deck-presets)))
         (options (append params (cdr defaults))))
    (when (and preset (not defaults))
      (user-error "Unknown agent-deck :preset %S (available: %s)"
                  preset (mapconcat #'car org-agent-deck-presets ", ")))
    (dolist (key '(:directory :group :harness :model :thinking :title))
      (let ((value (cdr (assq key options))))
        (when (and value
                   (or (not (stringp value))
                       (string-empty-p (string-trim value))
                       (string-match-p "\0" value)))
          (user-error "agent-deck %s must be a non-empty string without NUL" key))))
    (when (and (assq :worktree options)
               (not (member (cdr (assq :worktree options)) '("yes" "no"))))
      (user-error "agent-deck :worktree must be yes or no"))
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
          (thinking (cdr (assq :thinking options))))
      (unless (string-match-p "\\`[[:alnum:]_-]+\\'" harness)
        (user-error "agent-deck :harness must be a tool name, not a command"))
      (when (and model
                 (not (string-match-p "\\`[[:alnum:]/._:+@-]+\\'" model)))
        (user-error "agent-deck :model must be a model ID, not shell syntax or a pattern"))
      (when (and (equal harness "pi") thinking
                 (not (member thinking
                              '("default" "off" "minimal" "low" "medium"
                                "high" "xhigh" "max"))))
        (user-error "Invalid Pi :thinking %S" thinking)))
    options))

;;;###autoload
(defun org-babel-execute:agent-deck (body params)
  "Launch a fresh agent-deck session with prompt BODY and Babel PARAMS.
Wait only for launch and initial prompt delivery, not task completion.
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
         (thinking (cdr (assq :thinking options)))
         (title (or (cdr (assq :title options))
                    (file-name-nondirectory (directory-file-name directory))))
         (worktree (equal (cdr (assq :worktree options)) "yes"))
         (arguments (list "launch" "--json" "--no-parent" "--no-assert-done"
                          "--message-file" "-" "--group" group "--cmd" harness
                          "--title" title)))
    (when (string-empty-p (string-trim title))
      (user-error "Cannot derive a title from :directory; specify :title"))
    (when (and worktree (string-match-p "[/[:space:]]" title))
      (user-error "A worktree :title must be a Git branch name without spaces or /"))
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
      ;; Let agent-deck validate supported native harness/model/effort flags.
      (setq arguments
            (append arguments (when model (list "--model" model))
                    (when thinking (list "--effort" thinking)))))
    (when worktree
      (setq arguments
            (append arguments (list "--worktree" title "--new-branch"
                                    "--location" "subdirectory"))))
    (let* ((reply
            (condition-case err
                (org-agent-deck--json
                 (apply #'org-agent-deck--call body
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
                (eq (gethash "message_pending" reply) t)
                (not (equal (gethash "message" reply)
                            (replace-regexp-in-string "[\r\n]+\\'" "" body))))
        (user-error "Session %s was created, but prompt delivery is unconfirmed (status %s); inspect it before retrying"
                    id (gethash "status" reply)))
      (format "Session: %s\nTitle: %s\nGroup: %s\nDirectory: %s\nHarness: %s\nRequested model: %s\nRequested thinking: %s%s%s"
              id (or (gethash "title" reply) title)
              (or (gethash "group" reply) group)
              (or (gethash "path" reply) directory)
              (or (gethash "tool" reply) harness)
              (or model "(harness default)") (or thinking "(harness default)")
              (if worktree
                  (format "\nBranch: %s" (or (gethash "worktree_branch" reply) title))
                "")
              (if-let* ((warning (gethash "warning" reply)))
                  (concat "\nWarning: " warning)
                "")))))

(provide 'ob-agent-deck)
;;; ob-agent-deck.el ends here
