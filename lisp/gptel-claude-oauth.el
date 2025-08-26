;;; gptel-claude-oauth.el --- OAuth backend for Claude in gptel -*- lexical-binding: t; -*-

;; Author: Clean implementation for Claude OAuth
;; Package-Requires: ((emacs "27.1") (gptel))

;;; Commentary:
;; Minimal OAuth implementation for Claude/Anthropic API access.
;; Uses device flow authentication with PKCE.
;; Automatically injects required system prompt for OAuth tokens.

;; (setq gptel-model 'claude-opus-4-1-20250805
;;       gptel-backend (gptel-make-claude-oauth "Claude-OAuth" :stream t))

;;; Code:

(require 'gptel)
(require 'gptel-anthropic)
(require 'json)
(require 'url)
(require 'browse-url)

(defgroup gptel-claude-oauth nil
  "OAuth authentication for Claude in gptel."
  :group 'gptel)

;;; Configuration

(defcustom gptel-claude-oauth-cache-dir
  (expand-file-name ".cache/claude-oauth/" user-emacs-directory)
  "Directory for OAuth token cache."
  :type 'string
  :group 'gptel-claude-oauth)

(defconst gptel-claude-oauth--client-id "9d1c250a-e61b-44d9-88ed-5944d1962f5e"
  "OAuth client ID from OpenCode.")

(defconst gptel-claude-oauth--auth-url "https://claude.ai/oauth/authorize"
  "OAuth authorization endpoint.")

(defconst gptel-claude-oauth--token-url "https://console.anthropic.com/v1/oauth/token"
  "OAuth token endpoint.")

(defconst gptel-claude-oauth--redirect-uri "https://console.anthropic.com/oauth/code/callback"
  "OAuth redirect URI.")

(defconst gptel-claude-oauth--required-system-prompt
  "You are Claude Code, Anthropic's official CLI for Claude."
  "Required system prompt for OAuth token validation.")

;;; Token Storage

(defvar gptel-claude-oauth--token-cache nil
  "In-memory token cache: (access-token refresh-token expiry).")

(defun gptel-claude-oauth--ensure-cache-dir ()
  "Ensure cache directory exists with proper permissions."
  (unless (file-directory-p gptel-claude-oauth-cache-dir)
    (make-directory gptel-claude-oauth-cache-dir t)
    (set-file-modes gptel-claude-oauth-cache-dir #o700)))

(defun gptel-claude-oauth--save-tokens (access-token refresh-token expiry)
  "Save tokens to secure cache."
  (gptel-claude-oauth--ensure-cache-dir)
  (let ((token-file (expand-file-name "tokens.el" gptel-claude-oauth-cache-dir)))
    (with-temp-buffer
      (insert (format "(%S %S %S)"
                      access-token
                      refresh-token
                      (and expiry (float-time expiry))))
      (write-region (point-min) (point-max) token-file nil 'silent))
    (set-file-modes token-file #o600)
    (setq gptel-claude-oauth--token-cache
          (list access-token refresh-token expiry))))

(defun gptel-claude-oauth--load-tokens ()
  "Load tokens from cache."
  (let ((token-file (expand-file-name "tokens.el" gptel-claude-oauth-cache-dir)))
    (when (file-exists-p token-file)
      (with-temp-buffer
        (insert-file-contents token-file)
        (let ((data (read (current-buffer))))
          (when (and (listp data) (= (length data) 3))
            (setq gptel-claude-oauth--token-cache
                  (list (nth 0 data)
                        (nth 1 data)
                        (and (nth 2 data)
                             (seconds-to-time (nth 2 data)))))))))))

(defun gptel-claude-oauth--token-valid-p ()
  "Check if current token is valid."
  (when gptel-claude-oauth--token-cache
    (let ((expiry (nth 2 gptel-claude-oauth--token-cache)))
      (or (null expiry)  ; No expiry means valid
          (time-less-p (current-time) expiry)))))

;;; PKCE Implementation

(defun gptel-claude-oauth--base64url-encode (str)
  "Base64url encode STR."
  (let ((b64 (base64-encode-string str t)))
    (setq b64 (replace-regexp-in-string "+" "-" b64))
    (setq b64 (replace-regexp-in-string "/" "_" b64))
    (replace-regexp-in-string "=+$" "" b64)))

(defun gptel-claude-oauth--generate-verifier ()
  "Generate PKCE code verifier."
  (let ((chars "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-._~"))
    (apply #'string
           (cl-loop repeat 128
                    collect (aref chars (random (length chars)))))))

(defun gptel-claude-oauth--generate-challenge (verifier)
  "Generate PKCE code challenge from VERIFIER."
  (gptel-claude-oauth--base64url-encode
   (secure-hash 'sha256 verifier nil nil t)))

;;; OAuth Flow

(defun gptel-claude-oauth--exchange-code (code verifier)
  "Exchange authorization CODE for tokens using VERIFIER."
  ;; Parse the code - it might contain state after #
  (let* ((parts (split-string code "#"))
         (auth-code (car parts))
         (state (cadr parts))
         (url-request-method "POST")
         (url-request-extra-headers '(("Content-Type" . "application/json")))
         (url-request-data
          (json-encode
           `(("code" . ,auth-code)
             ,@(when state `(("state" . ,state)))
             ("grant_type" . "authorization_code")
             ("client_id" . ,gptel-claude-oauth--client-id)
             ("redirect_uri" . ,gptel-claude-oauth--redirect-uri)
             ("code_verifier" . ,verifier)))))
    (condition-case err
        (with-current-buffer
            (url-retrieve-synchronously gptel-claude-oauth--token-url)
          (goto-char (point-min))
          (when (re-search-forward "^$" nil t)
            (json-read)))
      (error
       (message "Error exchanging code: %s" err)
       nil))))

(defun gptel-claude-oauth--refresh-token ()
  "Refresh access token using refresh token."
  (when-let ((refresh-token (nth 1 gptel-claude-oauth--token-cache)))
    (let* ((url-request-method "POST")
           (url-request-extra-headers '(("Content-Type" . "application/json")))
           (url-request-data
            (json-encode
             `(("grant_type" . "refresh_token")
               ("refresh_token" . ,refresh-token)
               ("client_id" . ,gptel-claude-oauth--client-id)))))
      (condition-case nil
          (with-current-buffer
              (url-retrieve-synchronously gptel-claude-oauth--token-url)
            (goto-char (point-min))
            (when (re-search-forward "^$" nil t)
              (let ((response (json-read)))
                (when-let ((access-token (cdr (assoc 'access_token response))))
                  (let ((new-refresh (or (cdr (assoc 'refresh_token response))
                                         refresh-token))
                        (expires-in (or (cdr (assoc 'expires_in response)) 3600)))
                    (gptel-claude-oauth--save-tokens
                     access-token
                     new-refresh
                     (time-add (current-time) (seconds-to-time expires-in)))
                    t)))))
        (error nil)))))

;;; Public Interface

(defun gptel-claude-oauth-status ()
  "Check OAuth authentication status."
  (interactive)
  (unless gptel-claude-oauth--token-cache
    (gptel-claude-oauth--load-tokens))
  (let ((status (cond
                 ((gptel-claude-oauth--token-valid-p)
                  (format "Authenticated (expires %s)"
                          (format-time-string "%Y-%m-%d %H:%M:%S"
                                              (nth 2 gptel-claude-oauth--token-cache))))
                 ((nth 1 gptel-claude-oauth--token-cache)
                  "Token expired, refresh token available")
                 (t "Not authenticated"))))
    (message "Claude OAuth: %s" status)))

(defun gptel-claude-oauth-login ()
  "Authenticate with Claude using OAuth device flow."
  (interactive)
  (let* ((verifier (gptel-claude-oauth--generate-verifier))
         (challenge (gptel-claude-oauth--generate-challenge verifier))
         (auth-url (format "%s?code=true&client_id=%s&response_type=code&redirect_uri=%s&scope=%s&code_challenge=%s&code_challenge_method=S256&state=%s"
                           gptel-claude-oauth--auth-url
                           gptel-claude-oauth--client-id
                           (url-hexify-string gptel-claude-oauth--redirect-uri)
                           (url-hexify-string "org:create_api_key user:profile user:inference")
                           challenge
                           verifier)))
    (browse-url auth-url)
    (message "Opening browser for authentication...")
    (let ((code (read-string "Paste the authorization code from browser: ")))
      (when (string-empty-p code)
        (user-error "No authorization code provided"))
      (if-let ((response (gptel-claude-oauth--exchange-code code verifier))
               (access-token (cdr (assoc 'access_token response))))
          (progn
            (gptel-claude-oauth--save-tokens
             access-token
             (cdr (assoc 'refresh_token response))
             (time-add (current-time)
                       (seconds-to-time (or (cdr (assoc 'expires_in response)) 3600))))
            (message "Successfully authenticated with Claude!"))
        (user-error "Failed to authenticate")))))

(defun gptel-claude-oauth-logout ()
  "Clear OAuth tokens."
  (interactive)
  (setq gptel-claude-oauth--token-cache nil)
  (let ((token-file (expand-file-name "tokens.el" gptel-claude-oauth-cache-dir)))
    (when (file-exists-p token-file)
      (delete-file token-file)))
  (message "Logged out from Claude OAuth"))

(defun gptel-claude-oauth--get-token ()
  "Get valid OAuth token, refreshing if necessary."
  (unless gptel-claude-oauth--token-cache
    (gptel-claude-oauth--load-tokens))
  (unless (gptel-claude-oauth--token-valid-p)
    (unless (gptel-claude-oauth--refresh-token)
      (gptel-claude-oauth-login)))
  (car gptel-claude-oauth--token-cache))

;;; Backend Creation

;;;###autoload
(cl-defun gptel-make-claude-oauth
    (name &key stream key
          (models '((claude-opus-4-1-20250805
                     :description "Claude Opus 4.1 - Most capable"
                     :capabilities (tool json reasoning)
                     :context-window 200000
                     :max-tokens 64000)
                    (claude-opus-4-20250514
                     :description "Claude Opus 4"
                     :capabilities (tool json reasoning)
                     :context-window 200000
                     :max-tokens 64000)
                    (claude-sonnet-4-20250514
                     :description "Claude Sonnet 4"
                     :capabilities (tool json)
                     :context-window 200000
                     :max-tokens 32000)
                    (claude-3-5-sonnet-20241022
                     :description "Claude Sonnet 3.5 v2"
                     :capabilities (tool json)
                     :context-window 200000
                     :max-tokens 8192)
                    (claude-3-5-haiku-20241022
                     :description "Claude Haiku 3.5 - Fast"
                     :capabilities (tool json)
                     :context-window 200000
                     :max-tokens 8192))))
  "Create Claude backend with OAuth authentication.

NAME is the backend name.
STREAM enables streaming responses.
MODELS is the list of available models."
  (declare (indent 1))
  (let ((backend
         (gptel--make-anthropic
          :name name
          :host "api.anthropic.com"
          :header (lambda ()
                    `(("authorization" . ,(format "Bearer %s" (gptel-claude-oauth--get-token)))
                      ("anthropic-version" . "2023-06-01")
                      ("anthropic-beta" . "oauth-2025-04-20,claude-code-20250219,interleaved-thinking-2025-05-14,fine-grained-tool-streaming-2025-05-14")))
          :models (gptel--process-models models)
          :protocol "https"
          :endpoint "/v1/messages"
          :stream stream
          :request-params `(:system ,gptel-claude-oauth--required-system-prompt)
          :url "https://api.anthropic.com/v1/messages")))
    (prog1 backend
      (setf (alist-get name gptel--known-backends nil nil #'equal) backend))))

(provide 'gptel-claude-oauth)
;;; gptel-claude-oauth.el ends here
