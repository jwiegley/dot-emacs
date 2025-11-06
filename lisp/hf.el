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

(defcustom hf-server "hera.lan"
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

(defcustom hf-default-hostname "hera"
  "Name of model host."
  :type 'string
  :group 'hf)

(defcustom hf-default-instance-name 'hera/gpt-oss-120b
  "Name of default instance."
  :type 'symbol
  :group 'hf)

(defcustom hf-valid-hostnames '("hera" "clio" ;; "vulcan"
                                )
  "Name of hosts that can run models."
  :type '(repeat string)
  :group 'hf)

(defcustom hf-llama-server-executable "llama-server"
  "Path to the llama-server executable."
  :type 'file
  :group 'hf)

(defcustom hf-mlx-lm-executable "mlx-lm"
  "Path to the mlx-lm executable."
  :type 'file
  :group 'hf)

(defcustom hf-llama-swap-prolog "
healthCheckTimeout: 7200
startPort: 9200
"
  "Prolog for beginning of llama-swap.yaml file."
  :type 'string
  :group 'hf)

(defcustom hf-llama-swap-epilog "
groups:
  large_models:
    swap: true
    exclusive: false
    members:
      - DeepSeek-R1-Distill-Qwen-32B
      - DeepSeek-V3.1-Terminus
      - Kimi-K2-Instruct
      - Llama-4-Maverick-17B-128E-Instruct
      - Llama-4-Scout-17B-16E-Instruct
      - MiniMax-M2
      - Phi-4-reasoning-plus
      - Qwen3-235B-A22B-Instruct-2507
      - Qwen3-235B-A22B-Thinking-2507
      - Qwen3-30B-A3B-Instruct-2507
      - Qwen3-30B-A3B-Thinking-2507
      - Qwen3-32B
      - Qwen3-Coder-30B-A3B-Instruct
      - Qwen3-Coder-480B-A35B-Instruct
      - gpt-oss-120b
      - r1-1776-distill-llama-70b

  small_models:
    swap: true
    exclusive: false
    members:
      - DeepSeek-R1-0528-Qwen3-8B
      - Qwen3-0.6B
      - Qwen3-1.7B
      - Qwen3-14B
      - Qwen3-4B
      - Qwen3-8B
      - gemma-3-12b-it
      - gemma-3-1b-it
      - gemma-3-27b-it
      - gemma-3-4b-it
      - gemma-3n-E4B-it
      - gpt-oss-20b

  embeddings:
    swap: true
    exclusive: false
    members:
      - NV-Embed-v2
      - Qwen3-Embedding-8B
      - all-MiniLM-L6-v2
      - bge-base-en-v1.5
      - bge-large-en-v1.5
      - bge-m3
      - nomic-embed-text-v2-moe

  rerankings:
    swap: true
    exclusive: false
    members:
      - Qwen.Qwen3-Reranker-8B
      - bge-reranker-v2-m3

  stt:
    swap: true
    exclusive: false
    members:
      - whisper-large-v3-mlx
"
  "Epilog for beginning of llama-swap.yaml file."
  :type 'string
  :group 'hf)

(defcustom hf-litellm-path "/ssh:vulcan|sudo:root@vulcan:/etc/litellm/config.yaml"
  "Pathname to LiteLLM's config.yaml file."
  :type 'file
  :group 'hf)

(defcustom hf-litellm-prolog ""
  "Prolog for beginning of LiteLLM's config.yaml file."
  :type 'string
  :group 'hf)

(defcustom hf-litellm-credentials-function
  (lambda ()
    (format "
credential_list:
  - credential_name: hera_llama_swap_credential
    credential_values:
      api_base: http://hera.lan:8080/v1
      api_key: \"fake\"
    credential_info:
      description: \"API Key for llama-swap on Hera\"

  - credential_name: vulcan_llama_swap_credential
    credential_values:
      api_base: http://127.0.0.1:8080/v1
      api_key: \"fake\"
    credential_info:
      description: \"API Key for llama-swap on Vulcan\"

  - credential_name: clio_llama_swap_credential
    credential_values:
      api_base: http://clio.lan:8080/v1
      api_key: \"fake\"
    credential_info:
      description: \"API Key for llama-swap on Clio\"

  - credential_name: openai_credential
    credential_values:
      api_key: \"%s\"
    credential_info:
      description: \"API Key for OpenAI\"

  - credential_name: anthropic_credential
    credential_values:
      api_key: \"%s\"
    credential_info:
      description: \"API Key for Anthropic\"

  - credential_name: perplexity_credential
    credential_values:
      api_key: \"%s\"
    credential_info:
      description: \"API Key for Perplexity\"

  - credential_name: groq_credential
    credential_values:
      api_key: \"%s\"
    credential_info:
      description: \"API Key for Groq\"

  - credential_name: openrouter_credential
    credential_values:
      api_key: \"%s\"
    credential_info:
      description: \"API Key for OpenRouter\"
"
            (lookup-password "api.openai.com" "johnw" 443)
            (lookup-password "api.anthropic.com" "johnw" 443)
            (lookup-password "api.perplexity.ai" "johnw" 443)
            (lookup-password "api.groq.com" "johnw" 443)
            (lookup-password "openrouter.ai" "johnw" 443)
            ))
  "Function for generating credentials for LiteLLM's config.yaml file."
  :type 'function
  :group 'hf)

(defcustom hf-litellm-epilog "
litellm_settings:
  request_timeout: 7200
  ssl_verify: false
  # set_verbose: True
  cache: True
  cache_params:
    type: redis
    host: \"10.0.2.2\"
    port: 8085
    supported_call_types: [\"acompletion\", \"atext_completion\", \"aembedding\", \"atranscription\"]

router_settings:
  routing_strategy: \"least-busy\"
  num_retries: 3
  request_timeout: 7200
  max_parallel_requests: 100
  # provider_budget_config:
  #   perplexity:
  #     budget_limit: 5
  #     time_period: 1mo

general_settings:
  store_model_in_db: true
  store_prompts_in_spend_logs: true
  maximum_spend_logs_retention_period: \"90d\"
  maximum_spend_logs_retention_interval: \"7d\"
"
  "Epilog for beginning of LiteLLM's config.yaml file."
  :type 'string
  :group 'hf)

(defsubst hf-api-base ()
  "Get API base URL."
  (format "%s://%s:%d%s" hf-protocol hf-server hf-port hf-prefix))

;; Define paths
(defvar hf-home (expand-file-name "~"))
(defvar hf-xdg-local (expand-file-name ".local/share" hf-home))
(defvar hf-gguf-models (expand-file-name "Models" hf-home))
(defvar hf-mlx-models (expand-file-name ".cache/huggingface/hub" hf-home))
(defvar hf-lmstudio-models (expand-file-name "lmstudio/models" hf-xdg-local))
(defvar hf-ollama-models (expand-file-name "ollama/models" hf-xdg-local))

(defconst hf-all-model-characteristics
  '(high medium low remote local thinking instruct coding rewrite))

(defconst hf-all-model-capabilities
  '(media tool json url))

(defconst hf-all-model-mime-types
  '("image/jpeg" "image/png" "image/gif" "image/webp"))

(defconst hf-all-model-kinds
  '(text-generation embedding reranker))

(defconst hf-all-model-providers
  '(local openai anthropic perplexity groq openrouter))

(defconst hf-all-model-engines
  '(llama-cpp koboldcpp mlx-lm))

(cl-defstruct hf-model
  "Configuration data for a model, and its family of instances."
  name                                  ; name of the model
  description                           ; description of the model
  characteristics
  (capabilities
   hf-all-model-capabilities)           ; capabilities of the model
  (mime-types
   hf-all-model-mime-types)             ; MIME types that can be sent
  context-length                        ; model context length
  max-input-tokens                      ; number of tokens to accept
  max-output-tokens                     ; number of tokens to predict
  temperature                           ; model temperature
  min-p                                 ; minimum p
  top-p                                 ; top p
  top-k                                 ; top k
  (kind 'text-generation)               ; nil, or symbol from model-kinds
  (supports-system-message t)           ; t if model supports system messages
  (supports-function-calling nil)       ; t if model supports function calling
  (supports-reasoning nil)              ; t if model supports reasoning
  aliases                               ; model alias names
  instances)                            ; model instances

(cl-defstruct hf-instance
  "Configuration data for a model, and its family of instances."
  name                                  ; alternate name to use with provider
  model-name                            ; alternate model-name to use
  context-length                        ; context length to use for instance
  max-input-tokens                      ; number of tokens to accept
  max-output-tokens                     ; number of tokens to predict
  cache-control                         ; supports auto-caching?
  (provider 'local)                     ; where does the model run?
  (engine 'llama-cpp)                   ; if local: llama.cpp, koboldcpp, etc.
  (hostnames
   (list hf-default-hostname))          ; if local: hostname where engine runs
  model-path                            ; if local: path to model directory
  file-path                             ; if local: (optional) path to model file
  draft-model                           ; if local: (optional) path to draft model
  arguments)                            ; if local: arguments to engine

(defcustom hf-models-list
  (list

   (make-hf-model
    :name 'r1-1776-distill-llama-70b
    :context-length 131072
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/bartowski_perplexity-ai_r1-1776-distill-llama-70b-GGUF")))

   (make-hf-model
    :name 'DeepSeek-R1-Distill-Qwen-32B
    :context-length 131072
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/lmstudio-community_DeepSeek-R1-Distill-Qwen-32B-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'DeepSeek-R1-0528
    :context-length 163840
    :temperature 0.6
    :min-p 0.01
    :top-p 0.95
    :top-k 20
    :supports-reasoning t
    :instances
    (list
     ;; (make-hf-instance
     ;;  :context-length 16384
     ;;  :model-path "~/Models/unsloth_DeepSeek-R1-0528-GGUF"
     ;;  :arguments '("--cache-type-k" "q4_1"
     ;;               "--seed" "3407"))

     (make-hf-instance
      :name 'deepseek/deepseek-r1-0528:free
      :provider 'openrouter)))

   (make-hf-model
    :name 'DeepSeek-R1-0528-Qwen3-8B
    :context-length 131072
    :temperature 0.6
    :min-p 0.01
    :top-p 0.95
    :top-k 20
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_DeepSeek-R1-0528-Qwen3-8B-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'DeepSeek-V3.1-Terminus
    :context-length 131072
    :instances
    (list
     (make-hf-instance
      :context-length 16384
      :model-path "~/Models/unsloth_DeepSeek-V3.1-Terminus-GGUF"
      :arguments '("--cache-type-k" "q4_1"
                   ;; "--flash-attn" "on"
                   ;; "--cache-type-v" "q4_1"
                   "--seed" "3407"))))

   (make-hf-model
    :name 'DeepSeek-V3-0324-UD
    :context-length 163840
    :instances
    (list
     ;; (make-hf-instance
     ;;  :context-length 12000
     ;;  :model-path "~/Models/unsloth_DeepSeek-V3-0324-GGUF-UD")
     ))

   (make-hf-model
    :name 'Kimi-K2-Instruct
    :context-length 131072
    :temperature 0.6
    :min-p 0.01
    :top-p 0.8
    :top-k 20
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :context-length 32768
      :max-output-tokens 32768
      :model-path "~/Models/unsloth_Kimi-K2-Instruct-GGUF"
      :arguments '("--cache-type-k" "q4_1"
                   "--seed" "3407"))))

   (make-hf-model
    :name 'Llama-4-Scout-17B-16E-Instruct
    :context-length 10485760
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :context-length 1048576
      :model-path "~/Models/unsloth_Llama-4-Scout-17B-16E-Instruct-GGUF")

     (make-hf-instance
      :name 'meta-llama/llama-4-scout-17b-16e-instruct
      :provider 'groq)))

   ;; (make-hf-model
   ;;  :name 'Llama-4-Maverick-17B-128E-Instruct
   ;;  :context-length 1048576
   ;;  :supports-function-calling t
   ;;  :instances
   ;;  (list
   ;;   (make-hf-instance
   ;;    :context-length 65536
   ;;    :model-path "~/Models/unsloth_Llama-4-Maverick-17B-128E-Instruct-GGUF")

   ;;   (make-hf-instance
   ;;    :name 'meta-llama/llama-4-maverick-17b-128e-instruct
   ;;    :provider 'groq)

   ;;   (make-hf-instance
   ;;    :name 'meta-llama/llama-4-maverick:free
   ;;    :provider 'openrouter)))

   (make-hf-model
    :name 'MiniMax-M2
    :context-length 262144
    :temperature 1.0
    :top-p 0.95
    :top-k 40
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_MiniMax-M2-GGUF"
      :hostnames '("hera"))))

   (make-hf-model
    :name 'Phi-4-reasoning-plus
    :context-length 32768
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Phi-4-reasoning-plus-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'Qwen3-0.6B
    :context-length 40960
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Qwen3-0.6B-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'Qwen3-1.7B
    :context-length 40960
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Qwen3-1.7B-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'Qwen3-4B
    :context-length 40960
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Qwen3-4B-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'Qwen3-8B
    :context-length 40960
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Qwen3-8B-GGUF"
      :hostnames '("hera" "clio")) ))

   (make-hf-model
    :name 'Qwen3-14B
    :context-length 40960
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Qwen3-14B-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'Qwen3-32B
    :context-length 40960
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Qwen3-32B-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'Qwen3-30B-A3B-Instruct-2507
    :context-length 262144
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Qwen3-30B-A3B-Instruct-2507-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'Qwen3-30B-A3B-Thinking-2507
    :context-length 262144
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_Qwen3-30B-A3B-Thinking-2507-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'Qwen3-235B-A22B-Instruct-2507
    :characteristics '(high local instruct)
    :context-length 262144
    :temperature 0.7
    :min-p 0.01
    :top-p 0.8
    :top-k 20
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :max-output-tokens 81920
      :model-path "~/Models/unsloth_Qwen3-235B-A22B-Instruct-2507-GGUF"
      :arguments '("--repeat-penalty" "1.05"
                   "--cache-type-k" "q8_0"
                   "--top-k" "20"
                   "--flash-attn" "on"
                   "--cache-type-v" "q8_0"))))

   (make-hf-model
    :name 'Qwen3-235B-A22B-Thinking-2507
    :characteristics '(high local thinking)
    :context-length 262144
    :temperature 0.6
    :min-p 0.01
    :top-p 0.95
    :top-k 20
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :max-output-tokens 32768
      :model-path "~/Models/unsloth_Qwen3-235B-A22B-Thinking-2507-GGUF"
      :arguments '("--repeat-penalty" "1.05"
                   "--cache-type-k" "q8_0"
                   "--top-k" "20"
                   "--flash-attn" "on"
                   "--cache-type-v" "q8_0"))))

   (make-hf-model
    :name 'Qwen3-Coder-30B-A3B-Instruct
    :context-length 262144
    :temperature 0.7
    :min-p 0.01
    :top-p 0.8
    :top-k 20
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :max-output-tokens 65536
      :model-path "~/Models/unsloth_Qwen3-Coder-30B-A3B-Instruct-GGUF"
      :hostnames '("hera" "clio")
      :cache-control t
      :arguments '("--repeat-penalty" "1.05"
                   "--cache-type-k" "q8_0"
                   "--top-k" "20"
                   "--flash-attn" "on"
                   "--cache-type-v" "q8_0"
                   "--batch-size" "8192"
                   "--ubatch-size" "8192"
                   "--rope-scaling" "yarn"
                   "--rope-scale" "4"
                   "--yarn-orig-ctx" "262144"))))

   (make-hf-model
    :name 'Qwen3-Coder-480B-A35B-Instruct
    :context-length 262144
    :temperature 0.7
    :min-p 0.01
    :top-p 0.8
    :top-k 20
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :max-output-tokens 65536
      :model-path "~/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF"
      :file-path "~/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF/UD-Q4_K_XL/Qwen3-Coder-480B-A35B-Instruct-UD-Q4_K_XL-00001-of-00006.gguf"
      :cache-control t
      :arguments '("--repeat-penalty" "1.05"
                   "--cache-type-k" "q4_1"
                   "--top-k" "20"
                   "--flash-attn" "on"
                   "--cache-type-v" "q4_1"
                   "--rope-scaling" "yarn"
                   "--rope-scale" "4"
                   "--yarn-orig-ctx" "262144"
                   "--chat-template-file" "/Users/johnw/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF/chat_template.jinja"))))

   (make-hf-model
    :name 'gemma-3-1b-it
    :context-length 32768
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_gemma-3-1b-it-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'gemma-3-4b-it
    :context-length 131072
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_gemma-3-4b-it-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'gemma-3-12b-it
    :context-length 131072
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_gemma-3-12b-it-GGUF"
      :draft-model "~/Models/unsloth_gemma-3-1b-it-GGUF/gemma-3-1b-it-UD-Q8_K_XL.gguf"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'gemma-3-27b-it
    :context-length 131072
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_gemma-3-27b-it-GGUF"
      :draft-model "~/Models/unsloth_gemma-3-4b-it-GGUF/gemma-3-4b-it-UD-Q8_K_XL.gguf"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'gemma-3n-E4B-it
    :context-length 32768
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_gemma-3n-E4B-it-GGUF"
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'gpt-oss-20b
    :context-length 131072
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_gpt-oss-20b-GGUF"
      :hostnames '("hera" "clio")
      :cache-control t)))

   (make-hf-model
    :name 'gpt-oss-120b
    :context-length 131072
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/unsloth_gpt-oss-120b-GGUF"
      :draft-model "~/Models/unsloth_gpt-oss-20b-GGUF/gpt-oss-20b-F16.gguf"
      :cache-control t)))

   (make-hf-model
    :name 'Qwen.Qwen3-Reranker-8B
    :kind 'reranker
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/DevQuasar_Qwen.Qwen3-Reranker-8B-GGUF"
      :hostnames '("hera" "clio")
      :arguments '("--reranking"))))

   (make-hf-model
    :name 'Qwen3-Embedding-8B
    :context-length 32767
    :kind 'embedding
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/Qwen_Qwen3-Embedding-8B-GGUF"
      :hostnames '("hera" "clio")
      :arguments '("--embedding"
                   "--pooling" "last"
                   "--ubatch-size" "8192"
                   "--batch-size" "2048"))))

   (make-hf-model
    :name 'bge-m3
    :context-length 8192
    :kind 'embedding
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/gpustack_bge-m3-GGUF"
      :hostnames '("hera" "clio")
      :arguments '("--embedding"
                   "--pooling" "mean"
                   "--ubatch-size" "8192"
                   "--batch-size" "4096"))))

   (make-hf-model
    :name 'bge-reranker-v2-m3
    :kind 'reranker
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/gpustack_bge-reranker-v2-m3-GGUF"
      :hostnames '("hera" "clio")
      :arguments '("--reranking"
                   "--ubatch-size" "8192"
                   "--batch-size" "4096"))))

   (make-hf-model
    :name 'nomic-embed-text-v2-moe
    :context-length 512
    :kind 'embedding
    :instances
    (list
     (make-hf-instance
      :model-path "~/Models/nomic-ai_nomic-embed-text-v2-moe-GGUF"
      :hostnames '("hera" "clio")
      :arguments '("--embedding"
                   "--ubatch-size" "8192"))))

   (make-hf-model
    :name 'bge-base-en-v1.5
    :kind 'embedding
    :instances
    (list
     (make-hf-instance
      :name 'BAAI/bge-base-en-v1.5
      :engine 'mlx-lm)))

   (make-hf-model
    :name 'bge-large-en-v1.5
    :kind 'embedding
    :instances
    (list
     (make-hf-instance
      :name 'BAAI/bge-large-en-v1.5
      :engine 'mlx-lm
      :hostnames '("hera" "clio"))))

   (make-hf-model
    :name 'whisper-large-v3-mlx
    :instances
    (list
     (make-hf-instance
      :name 'mlx-community/whisper-large-v3-mlx
      :engine 'mlx-lm)))

   (make-hf-model
    :name 'NV-Embed-v2
    :kind 'embedding
    :instances
    (list
     (make-hf-instance
      :name 'nvidia/NV-Embed-v2
      :engine 'mlx-lm)))

   (make-hf-model
    :name 'all-MiniLM-L6-v2
    :kind 'embedding
    :instances
    (list
     (make-hf-instance
      :name 'sentence-transformers/all-MiniLM-L6-v2
      :engine 'mlx-lm)))

   (make-hf-model
    :name 'gpt-4.1
    :description "Flagship GPT model for complex tasks"
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'gpt-4.1-mini
    :description "Balanced for intelligence, speed, and cost"
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'gpt-4.1-nano
    :description "Fastest, most cost-effective GPT-4.1 model"
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'gpt-4o
    :description "Fast, intelligent, flexible GPT model"
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'gpt-4o-mini
    :description "Fast, affordable small model for focused tasks"
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'o1
    :description "Our most powerful reasoning model"
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'o1-pro
    :description "Our most powerful reasoning model"
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'o3
    :description "Our most powerful reasoning model"
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'o3-deep-research
    :description "Our most powerful reasoning model"
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'o3-mini
    :description "A small model alternative to o3"
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'o3-pro
    :description "Version of o3 with more compute for better responses"
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'o4-mini
    :description "Faster, more affordable reasoning model"
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'o4-mini-deep-research
    :description "Faster, more affordable reasoning model"
    :supports-function-calling t
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'openai)))

   (make-hf-model
    :name 'claude-haiku
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :name 'claude-haiku-4-5-20251001
      :provider 'anthropic)

     (make-hf-instance
      :model-name 'claude-haiku-cached
      :name 'claude-haiku-4-5-20251001
      :provider 'anthropic
      :cache-control t)))

   (make-hf-model
    :name 'claude-sonnet
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :name 'claude-sonnet-4-5-20250929
      :provider 'anthropic)

     (make-hf-instance
      :model-name 'claude-sonnet-cached
      :name 'claude-sonnet-4-5-20250929
      :provider 'anthropic
      :cache-control t)))

   (make-hf-model
    :name 'claude-opus
    :supports-function-calling t
    :instances
    (list
     (make-hf-instance
      :name 'claude-opus-4-1-20250805
      :provider 'anthropic)

     (make-hf-instance
      :model-name 'claude-opus-cached
      :name 'claude-opus-4-1-20250805
      :provider 'anthropic
      :cache-control t)))

   (make-hf-model
    :name 'r1-1776
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'perplexity)))

   (make-hf-model
    :name 'sonar-deep-research
    :instances
    (list
     (make-hf-instance
      :provider 'perplexity)))

   (make-hf-model
    :name 'sonar-pro
    :instances
    (list
     (make-hf-instance
      :provider 'perplexity)))

   (make-hf-model
    :name 'sonar-reasoning-pro
    :supports-reasoning t
    :instances
    (list
     (make-hf-instance
      :provider 'perplexity)))

   (make-hf-model
    :name 'compound-beta
    :instances
    (list
     (make-hf-instance
      :provider 'groq)))

   (make-hf-model
    :name 'deepseek-r1-distill-llama-70b
    :instances
    (list
     (make-hf-instance
      :provider 'groq)))

   (make-hf-model
    :name 'llama-3.3-70b-versatile
    :instances
    (list
     (make-hf-instance
      :provider 'groq)))

   (make-hf-model
    :name 'Llama-Guard-4-12B
    :instances
    (list
     (make-hf-instance
      :name 'meta-llama/Llama-Guard-4-12B
      :provider 'groq)))
   )
  "List of configured models."
  :type '(repeat sexp)
  :group 'hf)

(defun hf-models-from-characteristics (&rest characteristics)
  "Return all models that provides the full list of CHARACTERISTICS."
  (cl-loop for model in hf-models-list
           when (and-let* ((all-chars (hf-model-characteristics model)))
                  (cl-subsetp characteristics all-chars))
           return (hf-model-name model)))

;; (hf-models-from-characteristics 'high 'local 'thinking)

(defun hf-make-models-hash ()
  "Build a hashtable from NAME to MODEL for `hf-models-list'."
  (let ((h (make-hash-table)))
    (cl-loop for model in hf-models-list
             for name = (hf-model-name model)
             do (puthash name model h)
             finally (return h))))

(defun hf-get-model (model-name &optional models-hash)
  "Using MODELS-HASH, find the model with the given MODEL-NAME."
  (let ((models-hash (or models-hash (hf-make-models-hash))))
    (gethash model-name models-hash)))

(defun hf-instances-list ()
  "Return list of all current instances."
  (cl-loop for model in hf-models-list
           nconc (cl-loop for instance in (hf-model-instances model)
                          collect (cons model instance))))

(defun hf-full-model-name (directory)
  "Based on a model DIRECTORY, return the canonical full model name."
  (let ((name (file-name-nondirectory directory)))
    (when (string-prefix-p "models--" name)
      (setq name (substring name 8)))
    (replace-regexp-in-string "--" "/" name)))

(defun hf-short-model-name (model-name)
  "Given a full MODEL-NAME, return its short model name."
  (thread-last
    model-name
    file-name-nondirectory
    (replace-regexp-in-string "-gguf" "")
    (replace-regexp-in-string "-GGUF" "")
    (replace-regexp-in-string ".*_" "")))

(defconst hf-gguf-min-file-size (* 100 1024 1024))

(defun hf-get-gguf-path (model)
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

(defun hf-get-context-length (model)
  "Get maximum context length of MODEL."
  (when-let* ((gguf (expand-file-name (hf-get-gguf-path model))))
    (with-temp-buffer
      (when (zerop (call-process "gguf-tools" nil t nil "show" gguf))
        (goto-char (point-min))
        (when (search-forward ".context_length" nil t)
          (when (re-search-forward "\\[uint32\\] \\([0-9]+\\)" nil t)
            (string-to-number (match-string 1))))))))

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
        (shell-command (format "ollama create %s -f %s"
                               model-name modelfile-name))
        (delete-file modelfile-name)))))

(defun hf-show (model)
  "Show MODEL details."
  (interactive "sModel directory: ")
  (let ((gguf (hf-get-gguf-path model)))
    (when gguf
      (shell-command (format "gguf-tools show %s" gguf)))))

(defun hf-get-instance-model-name (model instance)
  "Return the model name for the given MODEL and INSTANCE."
  (or (hf-instance-model-name instance)
      (hf-model-name model)))

(defun hf-get-instance-name (model instance)
  "Return the model name for the given MODEL and INSTANCE."
  (or (hf-instance-name instance)
      (hf-model-name model)))

(defun hf-get-instance-context-length (model instance)
  "Find maximum context-length for the given MODEL and INSTANCE."
  (or (hf-instance-context-length instance)
      (hf-model-context-length model)))

(defun hf-get-instance-max-input-tokens (model instance)
  "Find maximum output tokens for the given MODEL and INSTANCE."
  (or (hf-instance-max-input-tokens instance)
      (hf-model-max-input-tokens model)))

(defun hf-get-instance-max-output-tokens (model instance)
  "Find maximum output tokens for the given MODEL and INSTANCE."
  (or (hf-instance-max-output-tokens instance)
      (hf-model-max-output-tokens model)))

(defsubst hf-remote-hostname-p (hostname)
  "Return non-nil if HOSTNAME is both non-nil and a remote host.
Remote is defined by any hostname that does not match `hf-default-hostname'."
  (and hostname
       (not (string= hostname hf-default-hostname))))

(defsubst hf-remote-path (path hostname)
  "Given a possibly remote HOSTNAME, return the correct PATH to reference it."
  (if (hf-remote-hostname-p hostname)
      (concat "/ssh:" hostname ":" path)
    path))

(defun hf-get-instance-gguf-path (instance &optional hostname)
  "Return file path for the GGUF file related to INSTANCE.
Optionally read the path on the given HOSTNAME."
  (or (hf-instance-file-path instance)
      (when-let* ((path (hf-instance-model-path instance)))
        (hf-get-gguf-path (hf-remote-path path hostname)))))

(defun hf-strip-tramp-prefix (path)
  "Remove TRAMP protocol/host info from PATH, leaving only the remote part."
  (if (file-remote-p path)
      (file-remote-p path 'localname)
    path))

(defun hf-insert-instance-llama-swap (model instance &optional hostname)
  "Instance the llama-swap.yaml config for MODEL and INSTANCE.
Optionally generate for the given HOSTNAME."
  (let* ((max-output-tokens (hf-get-instance-max-output-tokens model instance))
         (context-length (hf-get-instance-context-length model instance))
         (temperature (hf-model-temperature model))
         (min-p (hf-model-min-p model))
         (top-p (hf-model-top-p model))
         (top-k (hf-model-top-k model))
         (args
          (mapconcat
           #'identity
           (append
            (hf-instance-arguments instance)
            (and temperature
                 (list "--temp" (number-to-string temperature)))
            (and min-p
                 (list "--min-p" (number-to-string min-p)))
            (and top-p
                 (list "--top-p" (number-to-string top-p)))
            (and top-k
                 (list "--top-k" (number-to-string top-k)))
            (and-let* ((draft-model (hf-instance-draft-model instance))
                       (expanded (expand-file-name draft-model)))
              (and (file-exists-p expanded)
                   (cl-case (hf-instance-engine instance)
                     (llama-cpp (list "--model-draft" expanded))
                     (mlx-lm (list "--draft-model" expanded)))))
            (and context-length
                 (cl-case (hf-instance-engine instance)
                   ;; mlx-lm does not specify the context size, but grows the
                   ;; context dynamically based on usage.
                   (llama-cpp (list "--ctx-size"
                                    (number-to-string context-length)))))
            (and max-output-tokens
                 (list (cl-case (hf-instance-engine instance)
                         (llama-cpp "--predict")
                         (mlx-lm "--max-tokens"))
                       (number-to-string max-output-tokens))))
           " "))
         (leader (format "
  \"%s\":
    proxy: \"http://127.0.0.1:${PORT}\"
    cmd: >" (hf-model-name model)))
         (footer "
    checkEndpoint: /health
"))
    (cl-case (hf-instance-engine instance)
      (llama-cpp
       (when-let* ((path (hf-get-instance-gguf-path instance hostname))
                   (exe (let ((default-directory (hf-remote-path "~/" hostname)))
                          (executable-find hf-llama-server-executable
                                           (hf-remote-hostname-p hostname)))))
         (insert
          leader
          (format "
      %s
        --host 127.0.0.1 --port ${PORT}
        --jinja
        --model %s %s"
                  exe (hf-strip-tramp-prefix (expand-file-name path)) args)
          footer)))
      (mlx-lm
       (when-let* ((exe (let ((default-directory (hf-remote-path "~/" hostname)))
                          (executable-find hf-mlx-lm-executable
                                           (hf-remote-hostname-p hostname)))))
         (insert
          leader
          (format "
      %s
        --host 127.0.0.1 --port ${PORT}
        --model %s %s"
                  exe (hf-get-instance-model-name model instance) args)
          footer))))))

(defun hf-generate-llama-swap-yaml (hostname)
  "Build llama-swap.yaml configuration for HOSTNAME."
  (with-current-buffer (get-buffer-create "*llama-swap.yaml*")
    (erase-buffer)
    (insert hf-llama-swap-prolog)
    (insert "\nmodels:")
    (dolist (mi (hf-instances-list))
      (cl-destructuring-bind (model . instance) mi
        (when (and (eq 'local (hf-instance-provider instance))
                   (member hostname (hf-instance-hostnames instance)))
          (hf-insert-instance-llama-swap model instance hostname))))
    (insert hf-llama-swap-epilog)
    (yaml-mode)
    (current-buffer)))

;; (display-buffer (hf-generate-llama-swap-yaml "hera"))

(defun hf-build-llama-swap-yaml (&optional hostname)
  "Build llama-swap.yaml configuration, optionally for HOSTNAME."
  (let ((yaml-path (if (string= hostname "vulcan")
                       (expand-file-name "llama-swap.yaml" "/home/johnw/Models")
                     (expand-file-name "llama-swap.yaml" hf-gguf-models))))
    (with-temp-buffer
      (insert (with-current-buffer
                  (hf-generate-llama-swap-yaml (or hostname hf-default-hostname))
                (buffer-string)))
      (write-file (hf-remote-path yaml-path hostname)))
    (if (and hostname
             (not (string= hostname hf-default-hostname)))
        (shell-command
         (format "ssh %s killall llama-swap 2>/dev/null" hostname))
      (shell-command "killall llama-swap 2>/dev/null"))))

(defun hf-insert-instance-litellm (model instance)
  "Instance the LiteLLM config for MODEL and INSTANCE."
  (let* ((hostnames (hf-instance-hostnames instance))
         (provider (hf-instance-provider instance))
         (cache-control (hf-instance-cache-control instance))
         (model-name (hf-get-instance-model-name model instance))
         (name (hf-get-instance-name model instance))
         (kind (hf-model-kind model))
         (description (hf-model-description model))
         (max-input-tokens (hf-get-instance-max-input-tokens model instance))
         (max-output-tokens (hf-get-instance-max-output-tokens model instance))
         (supports-system-message (hf-model-supports-system-message model))
         (supports-function-calling (hf-model-supports-function-calling model))
         (supports-reasoning (hf-model-supports-reasoning model)))
    (dolist (host (if (eq 'local provider)
                      hostnames
                    (list provider)))
      (insert (format "
  - model_name: %s/%s
    litellm_params:
      model: %s/%s
      litellm_credential_name: %s_credential
      supports_system_message: %s
    model_info:
      mode: %S
      description: %S%s%s
      supports_function_calling: %s
      supports_reasoning: %s
"
                      host model-name
                      (if (eq 'local provider)
                          "openai"
                        provider)
                      name
                      (if (eq 'local provider)
                          (concat host "_llama_swap")
                        provider)
                      (concat
                       (if supports-system-message "true" "false")
                       (when cache-control
                         "
      cache_control_injection_points:
        - location: message
          role: system"))
                      (if (or (null kind) (eq kind 'text-generation))
                          "chat"
                        kind)
                      (or description "")
                      (if max-input-tokens
                          (format "\n      max_input_tokens: %s" max-input-tokens)
                        "")
                      (if max-output-tokens
                          (format "\n      max_output_tokens: %s" max-output-tokens)
                        "")
                      (if supports-function-calling "true" "false")
                      (if supports-reasoning "true" "false"))))))

(defun hf-generate-litellm-yaml ()
  "Build llama-swap.yaml configuration for HOSTNAME."
  (with-current-buffer (get-buffer-create "*litellm-config.yaml*")
    (erase-buffer)
    (insert hf-litellm-prolog)
    (insert "model_list:")
    (dolist (mi (hf-instances-list))
      (cl-destructuring-bind (model . instance) mi
        (hf-insert-instance-litellm model instance)
        ;; (unless (string= model (downcase model))
        ;;   (hf-insert-instance-litellm (downcase model) instance))
        ))
    (insert (funcall hf-litellm-credentials-function))
    (insert hf-litellm-epilog)
    (yaml-mode)
    (current-buffer)))

;; (display-buffer (hf-generate-litellm-yaml))

(defun hf-build-litellm-yaml ()
  "Build LiteLLM config.yaml configuration."
  (with-temp-buffer
    (insert (with-current-buffer (hf-generate-litellm-yaml)
              (buffer-string)))
    (write-file hf-litellm-path))
  (shell-command "ssh vulcan sudo systemctl restart litellm.service"))

(defun hf-reset ()
  "Reset all of the configuration files related to LLMs."
  (interactive)
  ;; First check that everything is sane
  (unless (= 0 (hf-check-instances))
    (error "Failed to check installed and defined instances"))
  ;; Update llama-swap configurations on all machines that run models
  (hf-build-llama-swap-yaml)
  (hf-build-llama-swap-yaml "clio")
  ;; (hf-build-llama-swap-yaml "vulcan")
  ;; Update LiteLLM to refer to all local and remote models
  (hf-build-litellm-yaml)
  ;; Update GPTel with instance list, to remain in sync with LiteLLM
  (setq gptel-model hf-default-instance-name
        gptel-backend (gptel-backends-make-litellm)))

(defun hf-get-instance-gptel-backend (model instance &optional hostname)
  "Instance the llama-swap.yaml config for MODEL and INSTANCE.
If HOSTNAME is non-nil, only generate definitions for that host."
  (let* ((model-name (hf-get-instance-model-name model instance)))
    (unless (memq (hf-model-kind model) '(embedding reranker))
      (cl-loop for server in (let ((provider (hf-instance-provider instance)))
                               (if (or (null provider)
                                       (eq 'local provider))
                                   (hf-instance-hostnames instance)
                                 (list provider)))
               when (or (null hostname) (string= server hostname))
               collect (list (if hostname
                                 model-name
                               (intern (format "%s/%s" server model-name)))
                             :description (or (hf-model-description model) "")
                             :capabilities (hf-model-capabilities model)
                             :mime-types (hf-model-mime-types model))))))

(defun hf-gptel-backends (&optional hostname)
  "Return the GPTel backends for all defined instances.
If HOSTNAME is non-nil, only generate definitions for that host."
  (cl-loop for (model . instance) in (hf-instances-list)
           for backends =
           (hf-get-instance-gptel-backend model instance hostname)
           when backends
           nconc backends))

;; (inspect (hf-gptel-backends))

(defun hf-lookup-instance (model)
  "Return the instance whole model matches the symbol MODEL."
  (cl-loop for (m . instance) in (hf-instances-list)
           when (eq model m)
           return instance))

(defun hf-check-instances ()
  "Check all model and instances definitions."
  (interactive)
  (let ((models-hash (hf-make-models-hash))
        (warnings 0))
    (dolist (host hf-valid-hostnames)
      (dolist (installed (hf-installed-models host))
        (unless (hf-get-model installed models-hash)
          (warn "Missing model for host %s: %s" host installed)
          (cl-incf warnings))
        (unless
            (catch 'found
              (dolist (mi (hf-instances-list))
                (cl-destructuring-bind (model . instance) mi
                  (when (and (member host (hf-instance-hostnames instance))
                             (eq installed (hf-model-name model)))
                    (throw 'found instance)))))
          (warn "Missing instance for host %s: %s" host installed)
          (cl-incf warnings))))
    (dolist (model hf-models-list)
      (let ((capabilities (hf-model-capabilities model))
            (mime-types (hf-model-mime-types model))
            (kind (hf-model-kind model)))
        (dolist (cap capabilities)
          (unless (member cap hf-all-model-capabilities)
            (warn "Unknown capability: %S" cap)
            (cl-incf warnings)))
        (dolist (mime mime-types)
          (unless (member mime hf-all-model-mime-types)
            (warn "Unknown mime-type: %S" mime)
            (cl-incf warnings)))
        (unless (member kind hf-all-model-kinds)
          (warn "Unknown kind: %S" kind)
          (cl-incf warnings))))
    (dolist (mi (hf-instances-list))
      (cl-destructuring-bind (_model . instance) mi
        (let ((model-path (hf-instance-model-path instance))
              (file-path (hf-instance-file-path instance))
              (hostnames (hf-instance-hostnames instance))
              (provider (hf-instance-provider instance))
              (engine (hf-instance-engine instance))
              (draft-model (hf-instance-draft-model instance)))
          (unless (or (null model-path)
                      (file-directory-p model-path))
            (warn "Unknown model-path: %s" model-path)
            (cl-incf warnings))
          (unless (or (null file-path)
                      (file-regular-p file-path))
            (warn "Unknown file-path: %s" file-path)
            (cl-incf warnings))
          (dolist (host hostnames)
            (unless (member host hf-valid-hostnames)
              (warn "Unknown hostname: %s" host)
              (cl-incf warnings)))
          (unless (member provider hf-all-model-providers)
            (warn "Unknown provider: %s" provider)
            (cl-incf warnings))
          (unless (member engine hf-all-model-engines)
            (warn "Unknown engine: %s" engine)
            (cl-incf warnings))
          (unless (or (null draft-model)
                      (file-regular-p draft-model))
            (warn "Unknown draft-model: %S" draft-model)
            (cl-incf warnings)))))
    warnings))

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
      (format "echo \">>> %s\" && cd \"%s\" && git pull" dir dir))
    (cl-loop for dir in (directory-files hf-gguf-models t "^[^.]")
             when (file-directory-p dir)
             when (file-exists-p (expand-file-name ".git" dir))
             collect dir)
    " ; ")))

(defun hf-installed-models (&optional hostname)
  "List all models from MLX and GGUF directories, optionally for HOSTNAME."
  (interactive)
  (cl-loop
   for base-dir in (list (hf-remote-path hf-mlx-models hostname)
                         (hf-remote-path hf-gguf-models hostname))
   when (file-exists-p base-dir)
   nconc (cl-loop
          for item in (directory-files base-dir t "^[^.]")
          when (file-directory-p item)
          unless (string= (file-name-nondirectory item) ".locks")
          collect (intern (hf-short-model-name (hf-full-model-name item))))))

;; (hf-installed-models "vulcan")

(cl-defun hf-generate-instance-declarations
    (&key (hostname hf-default-hostname))
  "Generate model declarations from DIRECTORY's subdirectories.
These declarations are for HOSTNAME."
  (interactive)
  (let ((dirs (cl-remove-if-not #'file-directory-p
                                (directory-files "~/Models" t "^[^.]"))))
    (with-current-buffer (get-buffer-create "*HF Instances*")
      (erase-buffer)
      (insert ";; Generated model configs from ~/Models\n")
      (dolist (dir dirs)
        (let* ((full-model (hf-full-model-name dir))
               (model-name (hf-short-model-name full-model))
               (context-length (hf-get-context-length dir)))
          (insert "(make-hf-model\n"
                  "  :name '" model-name "\n"
                  "  :context-length " (if (null context-length)
                                           "nil"
                                         (number-to-string context-length))
                  "\n"
                  "  :temperature 1.0\n"
                  "  :min-p 0.05\n"
                  "  :top-p 0.8\n"
                  "  :top-k 20\n"
                  "  :kind nil\n"
                  "  :aliases '())\n\n")))
      (insert "\n;; Generated model instances from ~/Models\n")
      (dolist (dir dirs)
        (let* ((full-model (hf-full-model-name dir))
               (model-name (hf-short-model-name full-model)))
          (insert "(make-hf-instance\n"
                  "  :model '" model-name "\n"
                  "  :hostnames '(\"" hostname "\")\n"
                  "  :file-format 'GGUF\n"
                  "  :model-path \"" dir "\"\n"
                  "  :engine 'llama-cpp\n"
                  "  :arguments '())\n\n")))
      (display-buffer (current-buffer)))))

(provide 'hf)

;;; hf.el ends here
