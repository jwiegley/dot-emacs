;;; hf.el --- LLM model management  -*- lexical-binding: t; -*-

;;; Commentary:

;; Model management utility for GGUF, MLX, LMStudio, and Ollama models.
;; Handles downloading, importing, configuration, and serving of AI models.

;;; Code:

(require 'cl-lib)
(require 'json)
(require 'url)
(require 'files)
(require 'subr-x)

(defgroup hf nil
  "Model management configuration."
  :group 'tools)

(defcustom hf-protocol "http"
  "Protocol for model server."
  :type 'string
  :group 'hf)

(defcustom hf-server "192.168.50.5"
  "Server address."
  :type 'string
  :group 'hf)

(defcustom hf-port 8080
  "Server port."
  :type 'integer
  :group 'hf)

(defcustom hf-prefix ""
  "API prefix."
  :type 'string
  :group 'hf)

(defcustom hf-api-key "sk-1234"
  "API key."
  :type 'string
  :group 'hf)

(defcustom hf-threads 24
  "Number of threads."
  :type 'integer
  :group 'hf)

(defcustom hf-hostname "hera"
  "Name of model host."
  :type 'string
  :group 'hf)

;; Define paths
(defvar hf-home (expand-file-name "~"))
(defvar hf-xdg-local (expand-file-name ".local/share" hf-home))
(defvar hf-gguf-models (expand-file-name "Models" hf-home))
(defvar hf-mlx-models (expand-file-name ".cache/huggingface/hub" hf-home))
(defvar hf-lmstudio-models (expand-file-name "lmstudio/models" hf-xdg-local))
(defvar hf-ollama-models (expand-file-name "ollama/models" hf-xdg-local))

(cl-defstruct model-config
  name draft context temp minp topp aliases args)

(defun hf-lookup-csv (csv-file search-key &optional key-column)
  "Look up SEARCH-KEY in CSV-FILE at KEY-COLUMN (default 0)."
  (setq key-column (or key-column 0))
  (when (file-exists-p csv-file)
    (with-temp-buffer
      (insert-file-contents csv-file)
      (goto-char (point-min))
      (catch 'found
        (while (not (eobp))
          (let* ((line (buffer-substring-no-properties
                        (line-beginning-position)
                        (line-end-position)))
                 (row (split-string line "," t)))
            (when (and (> (length row) key-column)
                       (string= (nth key-column row) search-key))
              (throw 'found
                     (make-model-config
                      :name (or (nth 0 row) "")
                      :draft (or (nth 1 row) "")
                      :context (or (nth 2 row) "")
                      :temp (or (nth 3 row) "")
                      :minp (or (nth 4 row) "")
                      :topp (or (nth 5 row) "")
                      :aliases (or (nth 6 row) "")
                      :args (or (nth 7 row) ""))))
            (forward-line 1)))))))

(defsubst hf-api-base ()
  "Get API base URL."
  (format "%s://%s:%d%s"
          hf-protocol
          hf-server
          hf-port
          hf-prefix))

(defconst hf-gguf-min-file-size (* 100 1024 1024))

(defun hf-get-gguf (model)
  "Find the best GGUF file for MODEL."
  (car
   (delete-dups
    (cl-loop
     for gguf in (sort (directory-files-recursively model "\\.gguf$")
                       #'string<)
     nconc (cl-loop
            for (_name pattern) in '(("fp" "fp\\(16\\|32\\)[_-]")
                                     ("f"  "[Ff]\\(16\\|32\\)")
                                     ("q"  "[Qq][234568]_\\(.*XL\\)?"))
            when (string-match-p pattern gguf)
            when (> (file-attribute-size (file-attributes gguf))
                    hf-gguf-min-file-size)
            collect gguf)))))

;; (inspect (hf-get-gguf "/Users/johnw/Models/TheBloke_WizardCoder-Python-34B-V1.0-GGUF"))

(defun hf-get-ctx-size (model)
  "Get context size of MODEL."
  (let ((gguf (hf-get-gguf model)))
    (when gguf
      (with-temp-buffer
        (when (zerop (call-process "gguf-tools" nil t nil "show" gguf))
          (goto-char (point-min))
          (when (search-forward ".context_length" nil t)
            (when (re-search-forward "\\[uint32\\] \\([0-9]+\\)" nil t)
              (string-to-number (match-string 1)))))))))

;; (inspect (hf-get-ctx-size "/Users/johnw/Models/unsloth_gemma-3-27b-it-GGUF"))

(defun hf-run-process (program &rest args)
  "Run PROGRAM with ARGS and return output."
  (with-temp-buffer
    (when (zerop (apply #'call-process program nil t nil args))
      (buffer-string))))

(defun hf-http-get (endpoint)
  "GET request to ENDPOINT."
  (let ((url-request-method "GET")
        (url-request-extra-headers
         `(("Authorization" . ,(format "Bearer %s" hf-api-key))
           ("Content-Type" . "application/json"))))
    (with-current-buffer
        (url-retrieve-synchronously
         (concat (hf-api-base) endpoint) t)
      (goto-char (point-min))
      (re-search-forward "^$")
      (json-read))))

(defun hf-get-models ()
  "Get list of available models from server."
  (condition-case err
      (let* ((response (hf-http-get "/v1/models"))
             (data (alist-get 'data response))
             (models (make-hash-table :test 'equal)))
        (seq-doseq (item data)
          (let ((id (alist-get 'id item)))
            (puthash id (list "M") models)))
        models)
    (error
     (message "Error fetching models: %s" err)
     (make-hash-table :test 'equal))))

;; (inspect (hf-get-models))

(defun hf-download (entries)
  "Download models from HuggingFace ENTRIES."
  (interactive "sModel entries (space-separated): ")
  (dolist (entry (split-string entries))
    (let* ((parts (split-string entry "/"))
           (model (string-join (cl-subseq parts 0 (min 2 (length parts))) "/"))
           (name (replace-regexp-in-string "/" "_" model)))
      (make-directory name t)
      (shell-command (format "git clone hf.co:%s %s" model name)))))

(defun hf-checkout (models)
  "Checkout MODELS using Git LFS."
  (interactive "sModel files (space-separated): ")
  (dolist (model (split-string models))
    (when (file-regular-p model)
      (let ((dir (file-name-directory model))
            (base (file-name-nondirectory model)))
        (shell-command (format "cd %s && git lfs fetch --include %s" dir base))
        (shell-command (format "cd %s && git lfs checkout %s" dir base))
        (shell-command (format "cd %s && git lfs dedup" dir))))))

(defun hf-import-lmstudio (models)
  "Import MODELS to LMStudio."
  (interactive "sModel files (space-separated): ")
  (dolist (model (split-string models))
    (when (file-regular-p model)
      (let* ((file-path (expand-file-name model))
             (base (replace-regexp-in-string
                    (concat (regexp-quote hf-gguf-models) "/")
                    "" file-path))
             (name (replace-regexp-in-string "_" "/" base))
             (target (expand-file-name name hf-lmstudio-models)))
        (make-directory (file-name-directory target) t)
        (when (file-exists-p target)
          (delete-file target))
        (add-name-to-file file-path target)))))

(defun hf-import-ollama (models)
  "Import MODELS to Ollama."
  (interactive "sModel files (space-separated): ")
  (dolist (model (split-string models))
    (when (file-regular-p model)
      (let* ((file-path (expand-file-name model))
             (base-name (file-name-nondirectory model))
             (modelfile-name (replace-regexp-in-string "\\.gguf$" ".modelfile" base-name))
             (model-name (replace-regexp-in-string "\\.gguf$" "" base-name)))
        (with-temp-file modelfile-name
          (insert (format "FROM %s\n" file-path)))
        (shell-command (format "ollama create %s -f %s" model-name modelfile-name))
        (delete-file modelfile-name)))))

(defun hf-show (model)
  "Show MODEL details."
  (interactive "sModel directory: ")
  (let ((gguf (hf-get-gguf model)))
    (when gguf
      (shell-command (format "gguf-tools show %s" gguf)))))

(defun hf-generate-gptel-config (&optional hostname)
  "Generate GPTel Emacs configuration for HOSTNAME or `hf-hostname'."
  (interactive)
  (let* ((models (sort (hash-table-keys (hf-get-models))
                       #'string<))
         (model-list
          (mapconcat
           (lambda (m)
             (format
              (concat "                "
                      "(%s/%s"
                      " :description \"\""
                      " :capabilities (media tool json url)"
                      " :mime-types (\"image/jpeg\" \"image/png\" \"image/gif\" \"image/webp\"))")
              (or hostname hf-hostname) m))
           models
           "\n")))
    (with-current-buffer (get-buffer-create "*GPTel Config*")
      (erase-buffer)
      (insert (format "    (gptel-make-openai \"llama-swap\"
      :host \"%s:%d\"
      :protocol \"%s\"
      ;; :stream t
      :models '(
%s
                ))"
                      hf-server
                      hf-port
                      hf-protocol
                      model-list))
      (display-buffer (current-buffer)))))

(defun hf-generate-build-yaml ()
  "Build llama-swap.yaml configuration."
  (interactive)
  (let ((gguf-models
         (sort (cl-remove-if-not
                (lambda (x) (file-directory-p x))
                (directory-files hf-gguf-models t "^[^.]"))
               #'string<)))
    (with-current-buffer (get-buffer-create "*llama-swap.yaml*")
      (insert "healthCheckTimeout: 7200\n")
      (insert "startPort: 9200\n\n")
      (insert "models:")
      (dolist (gguf-model gguf-models)
        (let ((gguf (hf-get-gguf gguf-model)))
          (if gguf
              (let* (
                     (model
                      (thread-last
                        gguf-model
                        file-name-nondirectory
                        (replace-regexp-in-string "-gguf" "")
                        (replace-regexp-in-string "-GGUF" "")
                        (replace-regexp-in-string ".*_" ""))))
                (insert (format "
  \"%s\":
    proxy: \"http://127.0.0.1:${PORT}\"
    cmd: >
      /etc/profiles/per-user/johnw/bin/llama-server
        --jinja
        --no-webui
        --offline
        --port ${PORT}
        --model %s%s
    checkEndpoint: /health
" model gguf "")))
            (error "No GGUF file in %s" gguf-model))))
      (current-buffer))))

;;; (display-buffer (hf-generate-build-yaml))

(defun hf-build-yaml ()
  "Build llama-swap.yaml configuration."
  (interactive)
  (let ((yaml-path (expand-file-name "llama-swap.yaml" hf-gguf-models))
        )
    (with-temp-file yaml-path
      (insert "healthCheckTimeout: 7200\n")
      (insert "startPort: 9200\n\n")
      (insert "models:\n")
      (dolist (model gguf-models)
        (let ((gguf (hf-get-gguf model)))
          (insert "
  \"Qwen3-14B\":
    proxy: \"http://127.0.0.1:${PORT}\"
    cmd: >
      /etc/profiles/per-user/johnw/bin/llama-server
        --jinja
        --no-webui
        --offline
        --port ${PORT}
        --model %s%s
    checkEndpoint: /health
" gguf gguf "")))
      (message "Generated %s" yaml-path))
    (shell-command "killall llama-swap 2>/dev/null")))

(defun hf-run-llama-swap ()
  "Start llama-swap with generated config."
  (interactive)
  (let ((config-path (expand-file-name "llama-swap.yaml" hf-gguf-models)))
    (shell-command (format "llama-swap --config %s" config-path))))

(defun hf-status ()
  "Get llama-swap status."
  (interactive)
  (let ((response (hf-http-get "/running")))
    (with-current-buffer (get-buffer-create "*Model Status*")
      (erase-buffer)
      (insert (json-encode response))
      (json-pretty-print-buffer)
      (display-buffer (current-buffer)))))

(defun hf-unload ()
  "Unload current model."
  (interactive)
  (hf-http-get "/unload")
  (message "Model unloaded"))

(defun hf-git-pull-all ()
  "Pull updates for all model directories."
  (interactive)
  (dolist (dir (directory-files hf-gguf-models t "^[^.]"))
    (when (and (file-directory-p dir)
               (file-exists-p (expand-file-name ".git" dir)))
      (message "Pulling %s..." (file-name-nondirectory dir))
      (shell-command (format "cd %s && git pull" dir)))))

(defun hf-list-all-models ()
  "List all models from MLX and GGUF directories."
  (interactive)
  (let ((models '()))
    (dolist (base-dir (list hf-mlx-models hf-gguf-models))
      (when (file-exists-p base-dir)
        (dolist (item (directory-files base-dir t "^[^.]"))
          (when (and (file-directory-p item)
                     (not (string= (file-name-nondirectory item) ".locks")))
            (let ((name (file-name-nondirectory item)))
              (when (string-prefix-p "models--" name)
                (setq name (substring name 8)))
              (setq name (replace-regexp-in-string "--" "_" name))
              (push name models))))))
    (with-current-buffer (get-buffer-create "*All Models*")
      (erase-buffer)
      (dolist (model (sort models #'string<))
        (insert model "\n"))
      (display-buffer (current-buffer)))))

(provide 'hf)

;;; hf.el ends here
