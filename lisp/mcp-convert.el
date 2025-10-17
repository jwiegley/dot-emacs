;;; mcp-convert.el --- Convert MCP JSON config to Emacs Lisp -*- lexical-binding: t; -*-

;; Copyright (C) 2025 Free Software Foundation, Inc.

;; Author: Claude Code
;; Version: 1.0.0
;; Package-Requires: ((emacs "27.1"))
;; Keywords: tools, mcp, conversion
;; URL: https://github.com/example/mcp-convert

;;; Commentary:

;; This package provides utilities for converting MCP (Model Context Protocol)
;; server configurations from JSON format to Emacs Lisp format with automatic
;; secret detection and replacement using lookup-password.
;;
;; Main command: M-x mcp-convert-json-to-elisp
;;
;; Features:
;; - Parse JSON from clipboard
;; - Transform to idiomatic Emacs Lisp format
;; - Detect and protect secrets (API keys, tokens, passwords, URIs)
;; - Special handling for uvx commands
;; - Customizable user and service host mappings
;;
;; Usage:
;;   1. Copy MCP JSON config to clipboard
;;   2. M-x mcp-convert-json-to-elisp
;;   3. Result inserted at point

;;; Code:

(require 'json)
(require 'url-parse)
(require 'cl-lib)

;;; Customization

(defgroup mcp-convert nil
  "Convert MCP server configurations from JSON to Emacs Lisp."
  :group 'tools
  :prefix "mcp-convert-")

(defcustom mcp-convert-default-user "johnw"
  "Default username for `lookup-password' calls."
  :type 'string
  :group 'mcp-convert)

(defcustom mcp-convert-service-host-alist
  '(("perplexity" . "api.perplexity.ai")
    ("openai" . "api.openai.com")
    ("anthropic" . "api.anthropic.com")
    ("github" . "api.github.com")
    ("gitlab" . "gitlab.com")
    ("postgres" . "localhost")
    ("mysql" . "localhost")
    ("redis" . "localhost"))
  "Alist mapping server names to API host addresses.
Used to generate appropriate `lookup-password' host parameters."
  :type '(alist :key-type string :value-type string)
  :group 'mcp-convert)

;;; Internal Variables

(defvar mcp-convert--secret-patterns
  '(("API_KEY" . api-key)
    ("TOKEN" . token)
    ("SECRET" . secret)
    ("PASSWORD" . password)
    ("PASS" . password)
    ("KEY" . api-key))
  "Patterns for detecting secret environment variable names.")

;;; Helper Functions

(defun mcp-convert--get-clipboard-content ()
  "Get content from clipboard (kill-ring or GUI clipboard).
Returns the most recent kill or clipboard content as a string."
  (or (and kill-ring (current-kill 0 t))
      (gui-get-selection 'CLIPBOARD)
      (error "Clipboard is empty")))

(defun mcp-convert--detect-secret-type (var-name value)
  "Detect if VAR-NAME/VALUE pair is a secret and return its type.
Returns one of: api-key, token, secret, password, uri, or nil."
  (let ((name-upper (upcase var-name)))
    (cond
     ;; Check URI patterns first
     ((and (or (string-match-p "URI\\|URL\\|DSN\\|CONNECTION" name-upper)
               (string-match-p "^[a-z]+://" value))
           (string-match-p ":[^:/@]+@" value))
      'uri)
     ;; Check variable name patterns
     ((cl-some (lambda (pattern)
                 (when (string-match-p (car pattern) name-upper)
                   (cdr pattern)))
               mcp-convert--secret-patterns))
     ;; Check value patterns (looks like secrets)
     ((or (string-match-p "^sk-[a-zA-Z0-9_-]{20,}$" value)  ; API key
          (string-match-p "^[a-f0-9]{32,}$" value)          ; Hex token
          (string-match-p "^[A-Za-z0-9_-]{40,}$" value)     ; Long token
          (string-match-p "^ghp_[a-zA-Z0-9]{36}$" value)    ; GitHub token
          (string-match-p "^glpat-[a-zA-Z0-9_-]{20}$" value)) ; GitLab token
      'token)
     (t nil))))

(defun mcp-convert--parse-uri (uri)
  "Parse URI string and return components.
Returns plist with :scheme :user :password :host :port :path."
  (let* ((parsed (url-generic-parse-url uri))
         (host (url-host parsed))
         (port (url-port parsed))
         (user (url-user parsed))
         (password (url-password parsed))
         (scheme (url-type parsed))
         (path (url-filename parsed)))
    (list :scheme scheme
          :user user
          :password password
          :host host
          :port (if (numberp port) port
                  (pcase scheme
                    ("http" 80)
                    ("https" 443)
                    ("postgresql" 5432)
                    ("mysql" 3306)
                    ("redis" 6379)
                    (_ 80)))
          :path path)))

(defun mcp-convert--derive-service-host (srvr-name var-name)
  "Derive API service host from SRVR-NAME and VAR-NAME.
Checks customization alist first, then uses defaults."
  (or (cdr (assoc srvr-name mcp-convert-service-host-alist))
      (cond
       ((string-match-p "perplexity" srvr-name) "api.perplexity.ai")
       ((string-match-p "openai" srvr-name) "api.openai.com")
       ((string-match-p "anthropic" srvr-name) "api.anthropic.com")
       ((string-match-p "github" srvr-name) "api.github.com")
       ((string-match-p "gitlab" srvr-name) "gitlab.com")
       ;; Extract domain from variable name if possible
       ((string-match "\\([a-z0-9-]+\\)[-_]\\(?:api\\|key\\|token\\)"
                      (downcase var-name))
        (format "api.%s.com" (match-string 1 (downcase var-name))))
       ;; Generic fallback
       (t (format "api.%s.com" srvr-name)))))

(defun mcp-convert--generate-lookup-password (srvr-name var-name value secret-type)
  "Generate `lookup-password' form for secret.
SRVR-NAME is the MCP server name.
VAR-NAME is the environment variable name.
VALUE is the original secret value (used for URI parsing).
SECRET-TYPE is the detected secret type symbol."
  (pcase secret-type
    ('uri
     (let* ((components (mcp-convert--parse-uri value))
            (host (plist-get components :host))
            (user (or (plist-get components :user) mcp-convert-default-user))
            (port (plist-get components :port))
            (scheme (plist-get components :scheme))
            (path (plist-get components :path))
            ;; (base-uri (format "%s://%s" scheme
            ;;                   (if (string-prefix-p "/" path)
            ;;                       path
            ;;                     (concat "/" path))))
            )
       ;; Return format string with embedded lookup-password
       `(format ,(format "%s://%s:%%s@%s:%d%s"
                         scheme
                         user
                         host
                         port
                         (replace-regexp-in-string "^/+" "" path))
                (lookup-password ,host ,user ,port))))

    ('api-key
     (let ((host (mcp-convert--derive-service-host srvr-name var-name)))
       `(lookup-password ,host ,mcp-convert-default-user 80)))

    ('token
     (let ((host (mcp-convert--derive-service-host srvr-name var-name)))
       `(lookup-password ,host ,mcp-convert-default-user 80)))

    ('secret
     `(lookup-password ,(format "%s.mcp" srvr-name)
                       ,mcp-convert-default-user
                       80))

    ('password
     `(lookup-password ,(format "%s.mcp" srvr-name)
                       ,mcp-convert-default-user
                       80))

    (_ value)))

(defun mcp-convert--process-env-value (srvr-name var-name value)
  "Process environment variable value, detecting and protecting secrets.

Examines the given value to determine if it contains sensitive information
based on the variable name and value patterns. If a secret is detected,
generates a safe `lookup-password'  form; otherwise returns the original
                                       ; value.

SRVR-NAME: The MCP server identifier for credential lookup.
VAR-NAME: The environment variable name to inspect for secret patterns.
VALUE: The environment variable value to process.

Returns either the original value string or a `lookup-password' form for
safe secret handling."
  (let ((secret-type (mcp-convert--detect-secret-type var-name value)))
    (if secret-type
        (mcp-convert--generate-lookup-password srvr-name var-name value secret-type)
      value)))

(defun mcp-convert--process-args (args command)
  "Process args array, applying special handling for uvx.
ARGS is a JSON array, COMMAND is the command string.
Returns Emacs Lisp list representation."
  (let ((args-list (append args nil)))  ; Convert vector to list
    (if (and (string= command "uvx")
             (= (length args-list) 1)
             (not (member (car args-list) '("--isolated" "--from"))))
        ;; Expand single package name for uvx
        (let ((package (car args-list)))
          (list "--isolated" "--from" package package "--"))
      ;; Return as-is
      args-list)))

(defun mcp-convert--parse-url-query-params (url)
  "Parse query parameters from URL and return as alist.
Each element is (param-name . param-value)."
  (when-let* ((parsed (url-generic-parse-url url))
              (query (url-filename parsed)))
    (when (string-match "\\?" query)
      (let ((params-string (substring query (1+ (match-beginning 0))))
            (params nil))
        (dolist (pair (split-string params-string "&"))
          (when (string-match "\\([^=]+\\)=\\(.+\\)" pair)
            (push (cons (match-string 1 pair) (match-string 2 pair)) params)))
        (nreverse params)))))

(defun mcp-convert--find-api-key-param (params)
  "Find API key parameter in PARAMS alist.
Returns cons cell (param-name . param-value) or nil."
  (cl-some (lambda (param-name)
             (assoc param-name params))
           '("apiKey" "api_key" "key" "token" "access_token")))

(defun mcp-convert--remove-query-param (url param-name)
  "Remove PARAM-NAME from URL query string."
  (let* ((parsed (url-generic-parse-url url))
         (path (url-filename parsed))
         (base-path (if (string-match "\\?" path)
                        (substring path 0 (match-beginning 0))
                      path))
         (params (mcp-convert--parse-url-query-params url))
         (filtered (cl-remove-if (lambda (p) (string= (car p) param-name)) params))
         (scheme (url-type parsed))
         (host (url-host parsed))
         (port (url-port parsed))
         (port-str (cond
                    ((null port) "")
                    ((and (string= scheme "https") (= port 443)) "")
                    ((and (string= scheme "http") (= port 80)) "")
                    (t (format ":%d" port)))))
    (if filtered
        (format "%s://%s%s%s?%s"
                scheme host port-str base-path
                (mapconcat (lambda (p) (format "%s=%s" (car p) (cdr p)))
                           filtered "&"))
      (format "%s://%s%s%s" scheme host port-str base-path))))

(defun mcp-convert--process-url (srvr-name url)
  "Process URL, detecting and protecting API keys in query parameters.
Returns either the original URL string or a format expression with lookup-password."
  (let* ((params (mcp-convert--parse-url-query-params url))
         (secret-param (mcp-convert--find-api-key-param params)))
    (if secret-param
        (let* ((param-name (car secret-param))
               (base-url (mcp-convert--remove-query-param url param-name))
               (parsed (url-generic-parse-url url))
               (host (url-host parsed)))
          ;; Return format expression with lookup-password
          `(format ,(concat base-url (if (string-match "\\?" base-url) "&" "?")
                           param-name "=%s")
                   (lookup-password ,host ,mcp-convert-default-user 80)))
      ;; No secret found, return as-is
      url)))

(defun mcp-convert--json-to-server-config (srvr-name config)
  "Convert single server CONFIG to Emacs Lisp format.
SRVR-NAME is the server identifier string.
CONFIG is a hash table from parsed JSON."
  (let* ((server-type (gethash "type" config))
         (url (gethash "url" config))
         (command (gethash "command" config))
         (args (gethash "args" config))
         (env (gethash "env" config))
         (result nil))

    ;; Handle HTTP-type servers with URL
    (cond
     ;; HTTP server with URL (note: we don't emit :type field per user request)
     ((and (string= server-type "http") url)
      (let ((processed-url (mcp-convert--process-url srvr-name url)))
        (setq result (list (intern ":url") processed-url))))

     ;; Command-based server
     (command
      (setq result (list (intern ":command") command))

      ;; Add args if present
      (when args
        (let ((processed-args (mcp-convert--process-args args command)))
          (setq result (append result
                               (list (intern ":args")
                                     processed-args)))))))

    ;; Add env if present (applies to both HTTP and command-based)
    (when env
      (let ((env-list nil))
        (maphash
         (lambda (key value)
           (let ((processed-value
                  (mcp-convert--process-env-value srvr-name key value)))
             (push (intern (concat ":" key)) env-list)
             (push processed-value env-list)))
         env)
        (when env-list
          (setq result (append result
                               (list (intern ":env")
                                     (nreverse env-list)))))))

    ;; Return (srvr-name config...)
    (list srvr-name result)))

(defun mcp-convert--parse-json-config (json-string)
  "Parse JSON-STRING and extract mcpServers configuration.
Returns hash table of server configurations or signals error."
  (condition-case err
      (json-parse-string json-string)
    (json-parse-error
     (error "Invalid JSON: %s" (error-message-string err)))
    (error
     (error "Failed to parse JSON: %s" (error-message-string err)))))

(defun mcp-convert--format-output (servers-list)
  "Format SERVERS-LIST as pretty-printed Emacs Lisp code.
SERVERS-LIST is a list of server configurations."
  (with-temp-buffer
    (insert "(mcp-hub-servers\n `(")

    (let ((first t))
      (dolist (server servers-list)
        (unless first
          (insert "\n    "))
        (setq first nil)

        ;; Format each server entry
        (insert "\n    (")
        (prin1 (car server) (current-buffer))  ; Server name
        (insert "\n     ")

        ;; Format properties
        (let ((props (cadr server))
              (prop-first t))
          (while props
            (let ((key (pop props))
                  (value (pop props)))
              (unless prop-first
                (insert "\n     "))
              (setq prop-first nil)

              (prin1 key (current-buffer))
              (insert " ")

              ;; Special formatting for different value types
              (cond
               ;; Lists (args)
               ((and (listp value) (not (eq (car-safe value) 'lookup-password))
                     (not (eq (car-safe value) 'format)))
                (insert "(")
                (let ((first-item t))
                  (dolist (item value)
                    (unless first-item (insert " "))
                    (setq first-item nil)
                    (prin1 item (current-buffer))))
                (insert ")"))

               ;; Env plist
               ((eq key :env)
                (insert "(")
                (let ((env-props value)
                      (env-first t))
                  (while env-props
                    (let ((env-key (pop env-props))
                          (env-value (pop env-props)))
                      (unless env-first
                        (insert "\n           "))
                      (setq env-first nil)

                      (prin1 env-key (current-buffer))
                      (insert " ")

                      ;; Unquote for backquote template
                      (cond
                       ((and (listp env-value)
                             (memq (car env-value) '(lookup-password format)))
                        (insert ",")
                        (prin1 env-value (current-buffer)))
                       (t
                        (prin1 env-value (current-buffer)))))))
                (insert ")"))

               ;; Other values - check if they need unquoting
               (t
                (cond
                 ;; Format/lookup-password expressions need unquoting in backquote
                 ((and (listp value)
                       (memq (car value) '(lookup-password format)))
                  (insert ",")
                  (prin1 value (current-buffer)))
                 ;; Regular values
                 (t
                  (prin1 value (current-buffer))))))))

        (insert ")")))

    (insert ")))")
    (buffer-string)))

;;; Main Command

;;;###autoload
(defun mcp-convert-json-to-elisp ()
  "Convert MCP server config from JSON to Emacs Lisp format.

Reads JSON configuration from the clipboard, transforms it to
idiomatic Emacs Lisp format with automatic secret protection,
and inserts the result at point.

The conversion performs these transformations:
1. Parses JSON object
2. Drops `type' field from server configs
3. Converts args arrays to Emacs Lisp lists
4. Special handling for uvx commands (expands single package name)
5. Detects secrets in env vars (API keys, tokens, passwords, URIs)
6. Replaces secrets with `lookup-password' calls
7. Pretty-prints output with proper indentation

Example input (JSON):
  {
    \"perplexity\": {
      \"type\": \"stdio\",
      \"command\": \"uvx\",
      \"args\": [\"mcp-perplexity\"],
      \"env\": {
        \"PERPLEXITY_API_KEY\": \"pplx-abc123...\"
      }
    }
  }

Example output (Emacs Lisp):
  (mcp-hub-servers
   `((\"perplexity\"
      :command \"uvx\"
      :args (\"--isolated\" \"mcp-perplexity\" \"--\")
      :env (:PERPLEXITY_API_KEY ,(lookup-password \"pplx\" \"johnw\" 80)))))

Customize `mcp-convert-default-user' and `mcp-convert-service-host-alist'
to control generated lookup-password parameters."
  (interactive)
  (condition-case err
      (let* ((json-string (mcp-convert--get-clipboard-content))
             (servers-hash (mcp-convert--parse-json-config json-string))
             (servers-list nil))

        ;; Convert each server configuration
        (maphash
         (lambda (name config)
           (push (mcp-convert--json-to-server-config name config)
                 servers-list))
         servers-hash)

        ;; Sort by server name for consistent output
        (setq servers-list (sort servers-list
                                 (lambda (a b)
                                   (string< (car a) (car b)))))

        ;; Format and insert output
        (let ((output (mcp-convert--format-output servers-list)))
          (insert output)
          (message "Converted %d MCP server%s from JSON to Emacs Lisp"
                   (length servers-list)
                   (if (= (length servers-list) 1) "" "s"))))

    (error
     (message "Conversion failed: %s" (error-message-string err))
     nil)))

;;; Additional Utilities

;;;###autoload
(defun mcp-convert-detect-secrets-in-region (start end)
  "Detect potential secrets in region from START to END.
Displays detected secrets and their types in a separate buffer."
  (interactive "r")
  (let ((text (buffer-substring-no-properties start end))
        (secrets nil))
    (with-temp-buffer
      (insert text)
      (goto-char (point-min))

      ;; Simple heuristic: find KEY=value patterns
      (while (re-search-forward "^\\s-*\"?\\([A-Z_]+\\)\"?\\s-*[=:]\\s-*\"\\([^\"]+\\)\"" nil t)
        (let* ((var-name (match-string 1))
               (value (match-string 2))
               (secret-type (mcp-convert--detect-secret-type var-name value)))
          (when secret-type
            (push (list var-name value secret-type) secrets)))))

    (if secrets
        (with-output-to-temp-buffer "*MCP Detected Secrets*"
          (princ "Detected secrets in region:\n\n")
          (dolist (secret (nreverse secrets))
            (princ (format "%-30s  Type: %-12s  Value: %s\n"
                          (car secret)
                          (caddr secret)
                          (cadr secret)))))
      (message "No secrets detected in region"))))

(provide 'mcp-convert)

;;; mcp-convert.el ends here
