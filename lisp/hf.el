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

(defconst model-formats '(GGUF safetensors))

(defconst model-engines '(llama-cpp koboldcpp mlx-lm))

(cl-defstruct hf-config
  "Configuration data for a model, and its family of instances."
  model-name
  context-length
  temperature
  min-p
  top-p
  aliases)

(cl-defstruct hf-instance
  "Configuration data for a model, and its family of instances."
  model-config                          ; reference to model config
  hostname                              ; where does the model run?
  file-format                           ; GGUF, safetensors
  model-path                            ; path to model directory
  file-path                             ; (optional) path to model file
  draft-model                           ; (optional) path to draft model file
  engine                                ; llama.cpp, koboldcpp, etc.
  arguments)

(defvar hf-model-configs
  (list (make-hf-config
         :model-name 'gpt-oss-120b
         :context-length 131072
         :temperature 1.0)
        (make-hf-config
         :model-name 'gpt-oss-20b
         :context-length 131072
         :temperature 1.0)))

(defvar hf-model-configs-hash
  (let ((h (make-hash-table)))
    (cl-loop for config in hf-model-configs
             for name = (let ((name (hf-config-model-name config)))
                          (if (symbolp name) name (intern name)))
             do (puthash name config h)
             finally (return h))))

(defvar hf-model-instances
  (list (make-hf-instance
         :model-config 'gpt-oss-20b
         :hostname "hera"
         :file-format 'GGUF
         :model-path "~/Models/unsloth_gpt-oss-20b-GGUF"
         :engine 'llama-cpp)
        (make-hf-instance
         :model-config 'gpt-oss-120b
         :hostname "hera"
         :file-format 'GGUF
         :model-path "~/Models/unsloth_gpt-oss-120b-GGUF"
         :draft-model 'gpt-oss-20b--llama-cpp--hera
         :engine 'llama-cpp)))

(defvar hf-model-instances-hash
  (let ((h (make-hash-table)))
    (cl-loop for instance in hf-model-instances
             for name =
             (intern
              (format "%s--%s--%s"
                      (symbol-name (hf-instance-model-config instance))
                      (symbol-name (hf-instance-engine instance))
                      (hf-instance-hostname instance)))
             do (puthash name instance h)
             finally (return h))))

;; (defun hf-lookup-csv (csv-file search-key &optional key-column)
;;   "Look up SEARCH-KEY in CSV-FILE at KEY-COLUMN (default 0)."
;;   (setq key-column (or key-column 0))
;;   (when (file-exists-p csv-file)
;;     (with-temp-buffer
;;       (insert-file-contents csv-file)
;;       (goto-char (point-min))
;;       (catch 'found
;;         (while (not (eobp))
;;           (let* ((line (buffer-substring-no-properties
;;                         (line-beginning-position)
;;                         (line-end-position)))
;;                  (row (split-string line "," t)))
;;             (when (and (> (length row) key-column)
;;                        (string= (nth key-column row) search-key))
;;               (throw 'found
;;                      (make-model-config
;;                       :model-name (or (nth 0 row) "")
;;                       :draft-model (or (nth 1 row) "")
;;                       :context-length (or (nth 2 row) "")
;;                       :temperature (or (nth 3 row) "")
;;                       :min-p (or (nth 4 row) "")
;;                       :top-p (or (nth 5 row) "")
;;                       :aliases (or (nth 6 row) "")
;;                       :arguments (or (nth 7 row) ""))))
;;             (forward-line 1)))))))

(defsubst hf-api-base ()
  "Get API base URL."
  (format "%s://%s:%d%s"
          hf-protocol
          hf-server
          hf-port
          hf-prefix))

(defun hf-full-model-name (directory)
  "Based on a model DIRECTORY, return the canonical full model name."
  (let ((name (file-name-nondirectory directory)))
    (when (string-prefix-p "models--" name)
      (setq name (substring name 8)))
    (setq name (replace-regexp-in-string "--" "_" name))
    name))

;;; (hf-full-model-name "/Users/johnw/Models/TheBloke_WizardCoder-Python-7B-V1.0-GGUF")
;;; (hf-full-model-name "/Users/johnw/Models/TheBloke_WizardCoder-Python-7B-V1.0-GGUF/Users/johnw/.cache/huggingface/hub/models--mlx-community--whisper-large-v3-mlx")

(defun hf-short-model-name (model-name)
  "Given a full MODEL-NAME, return its short model name."
  (thread-last
    model-name
    file-name-nondirectory
    (replace-regexp-in-string "-gguf" "")
    (replace-regexp-in-string "-GGUF" "")
    (replace-regexp-in-string ".*_" "")))

;;; (hf-short-model-name "TheBloke_WizardCoder-Python-7B-V1.0-GGUF")

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
              (let ((model (hf-short-model-name gguf-model)))
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

(cl-defun hf-run-mlx (model &key (port 8081))
  "Start mlx-lm with a specific MODEL on the given PORT."
  (interactive
   (list (read-string "Model: ")
         :port (read-number "Port: " 8081)))
  (let ((proc (start-process
               "mlx-lm"
               "*mlx-lm*"
               "mlx-lm"
               "--model" model
               "--port" (format "%d" port))))
    (set-process-query-on-exit-flag proc nil)
    (message "Started mlx-lm with model %s on port %d" model port)))

(cl-defun hf-run-llama-cpp (model &key (port 8081))
  "Start llama.cpp with a specific MODEL on the given PORT."
  (interactive
   (list (read-string "Model: ")
         :port (read-number "Port: " 8081)))
  (let ((proc (start-process
               "llama-cpp"
               "*llama-cpp*"
               "llama-server"
               "--jinja"
               "--no-webui"
               "--offline"
               "--port" (format "%d" port)
               "--model" model
               "--threads" (format "%d" hf-threads))))
    (set-process-query-on-exit-flag proc nil)
    (message "Started llama.cpp with model %s on port %d using %d threads"
             model port hf-threads)))

(defun hf-run-llama-swap ()
  "Start llama-swap with generated config."
  (interactive)
  (let ((config-path (expand-file-name "llama-swap.yaml" hf-gguf-models)))
    (shell-command (format "llama-swap --config %s" config-path))))

(defun hf-status ()
  "Get llama-swap status."
  (interactive)
  (with-current-buffer (get-buffer-create "*Model Status*")
    (erase-buffer)
    (insert (json-encode (hf-http-get "/running")))
    (json-pretty-print-buffer)
    (json-mode)
    (display-buffer (current-buffer))))

(defun hf-unload ()
  "Unload current model."
  (interactive)
  (hf-http-get "/unload")
  (message "Current model unloaded"))

(defun hf-git-pull-all ()
  "Run git-pull in all model directories."
  (interactive)
  (async-shell-command
   (mapconcat
    (lambda (dir)
      (format "echo \">>> %s\" && cd \"%s\" && git pull" dir))
    (cl-loop for dir in (directory-files hf-gguf-models t "^[^.]")
             when (file-directory-p dir)
             when (file-exists-p (expand-file-name ".git" dir))
             collect dir)
    " ; ")))

(defun hf-installed-models ()
  "List all models from MLX and GGUF directories."
  (interactive)
  (let ((models
         (cl-loop
          for base-dir in (list hf-mlx-models hf-gguf-models)
          when (file-exists-p base-dir)
          nconc (cl-loop
                 for item in (directory-files base-dir t "^[^.]")
                 when (file-directory-p item)
                 unless (string= (file-name-nondirectory item) ".locks")
                 collect (hf-full-model-name item)))))
    (with-current-buffer (get-buffer-create "*All Models*")
      (erase-buffer)
      (dolist (model (sort models #'string<))
        (insert model "\n"))
      (display-buffer (current-buffer)))))

(defun hf-generate-instances-from-models-dir ()
  "Generate model instance declarations from ~/Models subdirectories."
  (interactive)
  (with-current-buffer (get-buffer-create "*HF Instances*")
    (erase-buffer)
    (insert ";; Generated model instances from ~/Models\n")
    (dolist (dir (cl-remove-if-not #'file-directory-p
                                   (directory-files "~/Models" t "^[^.]")))
      (let* ((full-model (hf-full-model-name dir))
             (model-name (hf-short-model-name full-model)))
        (insert "(make-hf-instance\n"
                "  :model-config '" model-name "\n"
                "  :hostname \"" hf-hostname "\"\n"
                "  :file-format 'GGUF\n"
                "  :model-path \"" dir "\"\n"
                "  :engine 'llama-cpp)\n\n")))
    (display-buffer (current-buffer))))

(provide 'hf)

;;; hf.el ends here
