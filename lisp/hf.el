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

(defcustom hf-default-model
  (if (string-match-p "clio" (system-name))
      'Qwen3-Coder-30B-A3B-Instruct
    'Qwen3-Coder-480B-A35B-Instruct)
  "Name of default model."
  :type 'symbol
  :group 'hf)

(defcustom hf-default-hostname "hera"
  "Name of model host."
  :type 'string
  :group 'hf)

(defcustom hf-default-instance
  (if (string-match-p "clio" (system-name))
      hf-default-model
    (intern (format "%s/%s" hf-default-hostname hf-default-model)))
  "Name of default instance."
  :type 'symbol
  :group 'hf)

(defcustom hf-valid-hostnames '("hera" "clio" "athena")
  "Name of hosts that can run models."
  :type '(repeat string)
  :group 'hf)

(defcustom hf-llama-swap-prolog "
healthCheckTimeout: 7200
startPort: 9200
"
  "Name of model host."
  :type 'string
  :group 'hf)

(defcustom hf-llama-swap-epilog "
groups:
  always_running:
    swap: false
    exclusive: false
    persistent: true
    members:
      - Qwen3-235B-A22B

  small:
    swap: true
    exclusive: false
    members:
      - DeepSeek-R1-0528-Qwen3-8B
      - Qwen3-30B-A3B

  embeddings:
    swap: true
    exclusive: false
    members:
      - bge-m3
      - Qwen3-Embedding-8B
      - nomic-embed-text-v2-moe
      - sentence-transformers/all-MiniLM-L6-v2
"
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

(defconst hf-all-model-capabilities '(media tool json url))

(defconst hf-all-model-mime-types '("image/jpeg"
                                    "image/png"
                                    "image/gif"
                                    "image/webp"))

(defconst hf-all-model-kinds '(text-generation embedding reranker))

(defconst hf-all-model-providers '(local openai anthropic perplexity groq
                                         openrouter))

(defconst hf-all-model-engines '(llama-cpp koboldcpp mlx-lm))

(cl-defstruct hf-model
  "Configuration data for a model, and its family of instances."
  name                                  ; name of the model
  description                           ; description of the model
  (capabilities
   '(media tool json url))              ; capabilities of the model
  (mime-types
   '("image/jpeg"
     "image/png"
     "image/gif"
     "image/webp"))                     ; MIME types that can be sent
  context-length                        ; model context length
  (max-tokens 32767)                    ; number of tokens to predict
  (temperature 1.0)                     ; model temperature
  (min-p 0.05)                          ; minimum p
  (top-p 0.8)                           ; top p
  (top-k 20)                            ; top k
  (kind 'text-generation)               ; nil, or symbol from model-kinds
  (reasoning nil)                       ; t if model supports reasoning
  aliases                               ; model alias names
  inactive)                             ; t if model is not being used

(cl-defstruct hf-instance
  "Configuration data for a model, and its family of instances."
  model                                 ; reference to model config
  name                                  ; alternate name to use with provider
  context-length                        ; context length to use for instance
  max-tokens                            ; number of tokens to predict
  (provider 'local)                     ; where does the model run?
  (engine 'llama-cpp)                   ; if local: llama.cpp, koboldcpp, etc.
  (hostnames
   (list hf-default-hostname))          ; if local: hostname where engine runs
  model-path                            ; if local: path to model directory
  file-path                             ; if local: (optional) path to model file
  draft-model                           ; if local: (optional) path to draft model
  arguments)                            ; if local: arguments to engine

(defvar hf-models-list
  (list

   (make-hf-model :name 'Qwen.Qwen3-Reranker-8B
                  :context-length 40960
                  :kind 'reranker)

   (make-hf-model :name 'Qwen3-Embedding-8B
                  :context-length 40960
                  :kind 'embedding)

   (make-hf-model :name 'WizardCoder-Python-34B-V1.0
                  :context-length 16384)

   (make-hf-model :name 'WizardCoder-Python-7B-V1.0
                  :context-length 16384)

   (make-hf-model :name 'Mistral-Nemo-Instruct-2407
                  :context-length 1024000)

   (make-hf-model :name 'Llama-3.3-Nemotron-Super-49B-v1
                  :context-length 131072)

   (make-hf-model :name 'r1-1776-distill-llama-70b
                  :context-length 131072)

   (make-hf-model :name 'bge-m3
                  :context-length 8192
                  :kind 'embedding)

   (make-hf-model :name 'DeepSeek-R1-Distill-Qwen-32B
                  :context-length 131072
                  :reasoning t)

   (make-hf-model :name 'DeepSeek-R1-0528
                  :context-length 163840
                  :temperature 0.6
                  :min-p 0.01
                  :top-p 0.95
                  :top-k 20
                  :reasoning t)

   (make-hf-model :name 'DeepSeek-R1-0528-Qwen3-8B
                  :context-length 131072
                  :temperature 0.6
                  :min-p 0.01
                  :top-p 0.95
                  :top-k 20
                  :reasoning t)

   (make-hf-model :name 'DeepSeek-V3-0324-UD
                  :context-length 163840)

   (make-hf-model :name 'Devstral-Small-2505
                  :context-length 131072)

   (make-hf-model :name 'Kimi-K2-Instruct
                  :context-length 131072
                  :temperature 0.6
                  :min-p 0.01
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Llama-4-Maverick-17B-128E-Instruct
                  :context-length 1048576)

   (make-hf-model :name 'Llama-4-Scout-17B-16E-Instruct
                  :context-length 10485760)

   (make-hf-model :name 'Magistral-Small-2506
                  :context-length 40960)

   (make-hf-model :name 'Mistral-Small-3.2-24B-Instruct-2506
                  :context-length 131072)

   (make-hf-model :name 'nomic-embed-text-v2-moe
                  :context-length 512
                  :kind 'embedding)

   (make-hf-model :name 'Phi-4-reasoning-plus
                  :context-length 32768
                  :reasoning t)

   (make-hf-model :name 'Qwen3-0.6B
                  :context-length 40960
                  :reasoning t)

   (make-hf-model :name 'Qwen3-1.7B
                  :context-length 40960
                  :reasoning t)

   (make-hf-model :name 'Qwen3-4B
                  :context-length 40960
                  :reasoning t)

   (make-hf-model :name 'Qwen3-8B
                  :context-length 40960
                  :reasoning t)

   (make-hf-model :name 'Qwen3-14B
                  :context-length 40960
                  :reasoning t)

   (make-hf-model :name 'Qwen3-32B
                  :context-length 40960
                  :reasoning t)

   (make-hf-model :name 'Qwen3-30B-A3B-Thinking-2507
                  :context-length 262144
                  :reasoning t)

   (make-hf-model :name 'Qwen3-235B-A22B-Instruct-2507
                  :context-length 262144
                  :temperature 0.7
                  :min-p 0.01
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-235B-A22B-Thinking-2507
                  :context-length 262144
                  :temperature 0.6
                  :min-p 0.01
                  :top-p 0.95
                  :top-k 20
                  :reasoning t)

   (make-hf-model :name 'Qwen3-Coder-30B-A3B-Instruct
                  :context-length 262144
                  :temperature 0.7
                  :min-p 0.01
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-Coder-480B-A35B-Instruct
                  :context-length 262144
                  :temperature 0.7
                  :min-p 0.01
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'gemma-3-1b-it
                  :context-length 32768)

   (make-hf-model :name 'gemma-3-4b-it
                  :context-length 131072)

   (make-hf-model :name 'gemma-3-12b-it
                  :context-length 131072)

   (make-hf-model :name 'gemma-3-27b-it
                  :context-length 131072)

   (make-hf-model :name 'gemma-3n-E4B-it
                  :context-length 32768)

   (make-hf-model :name 'gpt-oss-20b
                  :context-length 131072
                  :reasoning t)

   (make-hf-model :name 'gpt-oss-120b
                  :context-length 131072
                  :reasoning t)

   (make-hf-model :name 'bge-base-en-v1.5
                  :kind 'embedding)

   (make-hf-model :name 'bge-large-en-v1.5
                  :kind 'embedding)

   (make-hf-model :name 'whisper-large-v3-mlx)

   (make-hf-model :name 'NV-Embed-v2
                  :kind 'embedding)

   (make-hf-model :name 'all-MiniLM-L6-v2
                  :kind 'embedding)

   (make-hf-model :name 'gpt-4.1
                  :description "Flagship GPT model for complex tasks")

   (make-hf-model :name 'gpt-4.1-mini
                  :description "Balanced for intelligence, speed, and cost")

   (make-hf-model :name 'gpt-4.1-nano
                  :description "Fastest, most cost-effective GPT-4.1 model")

   (make-hf-model :name 'gpt-4o
                  :description "Fast, intelligent, flexible GPT model")

   (make-hf-model :name 'gpt-4o-mini
                  :description "Fast, affordable small model for focused tasks")

   (make-hf-model :name 'o1
                  :description "Our most powerful reasoning model"
                  :reasoning t)

   (make-hf-model :name 'o1-pro
                  :description "Our most powerful reasoning model"
                  :reasoning t)

   (make-hf-model :name 'o3
                  :description "Our most powerful reasoning model"
                  :reasoning t)

   (make-hf-model :name 'o3-deep-research
                  :description "Our most powerful reasoning model"
                  :reasoning t)

   (make-hf-model :name 'o3-mini
                  :description "A small model alternative to o3"
                  :reasoning t)

   (make-hf-model :name 'o3-pro
                  :description "Version of o3 with more compute for better responses"
                  :reasoning t)

   (make-hf-model :name 'o4-mini
                  :description "Faster, more affordable reasoning model"
                  :reasoning t)

   (make-hf-model :name 'o4-mini-deep-research
                  :description "Faster, more affordable reasoning model"
                  :reasoning t)

   (make-hf-model :name 'claude-haiku
                  :description "")

   (make-hf-model :name 'claude-opus
                  :description "")

   (make-hf-model :name 'claude-sonnet
                  :description "")

   (make-hf-model :name 'r1-1776
                  :description ""
                  :reasoning t)

   (make-hf-model :name 'sonar-deep-research
                  :description "")

   (make-hf-model :name 'sonar-pro
                  :description "")

   (make-hf-model :name 'sonar-reasoning-pro
                  :description ""
                  :reasoning t)

   (make-hf-model :name 'compound-beta
                  :description "")

   (make-hf-model :name 'deepseek-r1-distill-llama-70b
                  :description "")

   (make-hf-model :name 'llama-3.3-70b-versatile
                  :description "")

   (make-hf-model :name 'Llama-Guard-4-12B
                  :description "")

   ))

(defun hf-make-models-hash ()
  "Build a hashtable from NAME to MODEL for `hf-models-list'."
  (let ((h (make-hash-table)))
    (cl-loop for model in hf-models-list
             for name = (let ((name (hf-model-name model)))
                          (if (symbolp name) name (intern name)))
             unless (hf-model-inactive model)
             do (puthash name model h)
             finally (return h))))

(defvar hf-instances-list
  (list

   (make-hf-instance
    :model 'Qwen.Qwen3-Reranker-8B
    :model-path "~/Models/DevQuasar_Qwen.Qwen3-Reranker-8B-GGUF")

   (make-hf-instance
    :model 'Qwen3-Embedding-8B
    :model-path "~/Models/Qwen_Qwen3-Embedding-8B-GGUF"
    :arguments '("--embedding"
                 "--pooling" "last"
                 "--ubatch-size" "8192"
                 "--batch-size" "2048"))

   (make-hf-instance
    :model 'WizardCoder-Python-34B-V1.0
    :model-path "~/Models/TheBloke_WizardCoder-Python-34B-V1.0-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'WizardCoder-Python-7B-V1.0
    :model-path "~/Models/TheBloke_WizardCoder-Python-7B-V1.0-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Mistral-Nemo-Instruct-2407
    :model-path "~/Models/bartowski_Mistral-Nemo-Instruct-2407-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Llama-3.3-Nemotron-Super-49B-v1
    :model-path "~/Models/bartowski_nvidia_Llama-3.3-Nemotron-Super-49B-v1-GGUF")

   (make-hf-instance
    :model 'r1-1776-distill-llama-70b
    :model-path "~/Models/bartowski_perplexity-ai_r1-1776-distill-llama-70b-GGUF")

   (make-hf-instance
    :model 'bge-m3
    :model-path "~/Models/gpustack_bge-m3-GGUF"
    :arguments '("--embedding"
                 "--pooling" "mean"
                 "--ubatch-size" "8192"
                 "--batch-size" "4096"))

   (make-hf-instance
    :model 'DeepSeek-R1-Distill-Qwen-32B
    :model-path "~/Models/lmstudio-community_DeepSeek-R1-Distill-Qwen-32B-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'nomic-embed-text-v2-moe
    :model-path "~/Models/nomic-ai_nomic-embed-text-v2-moe-GGUF"
    :arguments '("--embedding"
                 "--ubatch-size" "8192"))

   (make-hf-instance
    :model 'DeepSeek-R1-0528
    :context-length 16384
    :model-path "~/Models/unsloth_DeepSeek-R1-0528-GGUF"
    :arguments '("--cache-type-k" "q4_1"
                 "--seed" "3407"))

   (make-hf-instance
    :model 'DeepSeek-R1-0528-Qwen3-8B
    :model-path "~/Models/unsloth_DeepSeek-R1-0528-Qwen3-8B-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'DeepSeek-V3-0324-UD
    :context-length 12000
    :model-path "~/Models/unsloth_DeepSeek-V3-0324-GGUF-UD")

   (make-hf-instance
    :model 'Devstral-Small-2505
    :model-path "~/Models/unsloth_Devstral-Small-2505-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Kimi-K2-Instruct
    :context-length 32768
    :max-tokens 32768
    :model-path "~/Models/unsloth_Kimi-K2-Instruct-GGUF"
    :arguments '("--cache-type-k" "q4_1"
                 "--seed" "3407"))

   (make-hf-instance
    :model 'Llama-4-Maverick-17B-128E-Instruct
    :context-length 65536
    :model-path "~/Models/unsloth_Llama-4-Maverick-17B-128E-Instruct-GGUF")

   (make-hf-instance
    :model 'Llama-4-Scout-17B-16E-Instruct
    :context-length 1048576
    :model-path "~/Models/unsloth_Llama-4-Scout-17B-16E-Instruct-GGUF")

   (make-hf-instance
    :model 'Magistral-Small-2506
    :model-path "~/Models/unsloth_Magistral-Small-2506-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Mistral-Small-3.2-24B-Instruct-2506
    :model-path "~/Models/unsloth_Mistral-Small-3.2-24B-Instruct-2506-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Phi-4-reasoning-plus
    :model-path "~/Models/unsloth_Phi-4-reasoning-plus-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Qwen3-0.6B
    :model-path "~/Models/unsloth_Qwen3-0.6B-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Qwen3-1.7B
    :model-path "~/Models/unsloth_Qwen3-1.7B-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Qwen3-4B
    :model-path "~/Models/unsloth_Qwen3-4B-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Qwen3-8B
    :model-path "~/Models/unsloth_Qwen3-8B-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Qwen3-14B
    :model-path "~/Models/unsloth_Qwen3-14B-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'Qwen3-32B
    :model-path "~/Models/unsloth_Qwen3-32B-GGUF"
    :hostnames '("hera" "athena" "clio"))

   (make-hf-instance
    :model 'Qwen3-30B-A3B-Thinking-2507
    :model-path "~/Models/unsloth_Qwen3-30B-A3B-Thinking-2507-GGUF"
    :hostnames '("hera" "athena" "clio"))

   (make-hf-instance
    :model 'Qwen3-235B-A22B-Instruct-2507
    :max-tokens 81920
    :model-path "~/Models/unsloth_Qwen3-235B-A22B-Instruct-2507-GGUF"
    :arguments '("--repeat-penalty" "1.05"
                 "--cache-type-k" "q8_0"
                 "--top-k" "20"
                 "--flash-attn"
                 "--cache-type-v" "q8_0"))

   (make-hf-instance
    :model 'Qwen3-235B-A22B-Thinking-2507
    :max-tokens 32768
    :model-path "~/Models/unsloth_Qwen3-235B-A22B-Thinking-2507-GGUF"
    :arguments '("--repeat-penalty" "1.05"
                 "--cache-type-k" "q8_0"
                 "--top-k" "20"
                 "--flash-attn"
                 "--cache-type-v" "q8_0"))

   (make-hf-instance
    :model 'Qwen3-Coder-30B-A3B-Instruct
    :max-tokens 65536
    :model-path "~/Models/unsloth_Qwen3-Coder-30B-A3B-Instruct-GGUF"
    :hostnames '("hera" "athena" "clio")
    :arguments '("--repeat-penalty" "1.05"
                 "--cache-type-k" "q8_0"
                 "--top-k" "20"
                 "--flash-attn"
                 "--cache-type-v" "q8_0"
                 "--rope-scaling" "yarn"
                 "--rope-scale" "4"
                 "--yarn-orig-ctx" "262144"))

   (make-hf-instance
    :model 'Qwen3-Coder-480B-A35B-Instruct
    :max-tokens 65536
    :model-path "~/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF"
    :file-path "~/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF/UD-Q4_K_XL/Qwen3-Coder-480B-A35B-Instruct-UD-Q4_K_XL-00001-of-00006.gguf"
    :arguments '("--repeat-penalty" "1.05"
                 "--cache-type-k" "q4_1"
                 "--top-k" "20"
                 "--flash-attn"
                 "--cache-type-v" "q4_1"
                 "--rope-scaling" "yarn"
                 "--rope-scale" "4"
                 "--yarn-orig-ctx" "262144"
                 "--chat-template-file" "/Users/johnw/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF/chat_template.jinja"))

   (make-hf-instance
    :model 'gemma-3-1b-it
    :model-path "~/Models/unsloth_gemma-3-1b-it-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'gemma-3-4b-it
    :model-path "~/Models/unsloth_gemma-3-4b-it-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'gemma-3-12b-it
    :model-path "~/Models/unsloth_gemma-3-12b-it-GGUF"
    :draft-model 'gemma-3-1b-it
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'gemma-3-27b-it
    :model-path "~/Models/unsloth_gemma-3-27b-it-GGUF"
    :draft-model 'gemma-3-4b-it
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'gemma-3n-E4B-it
    :model-path "~/Models/unsloth_gemma-3n-E4B-it-GGUF"
    :hostnames '("hera" "clio"))

   (make-hf-instance
    :model 'gpt-oss-20b
    :model-path "~/Models/unsloth_gpt-oss-20b-GGUF"
    :hostnames '("hera" "athena" "clio"))

   (make-hf-instance
    :model 'gpt-oss-120b
    :model-path "~/Models/unsloth_gpt-oss-120b-GGUF")

   (make-hf-instance
    :model 'bge-base-en-v1.5
    :name 'BAAI/bge-base-en-v1.5
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'bge-large-en-v1.5
    :name 'BAAI/bge-large-en-v1.5
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'whisper-large-v3-mlx
    :name 'mlx-community/whisper-large-v3-mlx
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'NV-Embed-v2
    :name 'nvidia/NV-Embed-v2
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'all-MiniLM-L6-v2
    :name 'sentence-transformers/all-MiniLM-L6-v2
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'gpt-4.1
    :provider 'openai)

   (make-hf-instance
    :model 'gpt-4.1-mini
    :provider 'openai)

   (make-hf-instance
    :model 'gpt-4.1-nano
    :provider 'openai)

   (make-hf-instance
    :model 'gpt-4o
    :provider 'openai)

   (make-hf-instance
    :model 'gpt-4o-mini
    :provider 'openai)

   (make-hf-instance
    :model 'o1
    :provider 'openai)

   (make-hf-instance
    :model 'o1-pro
    :provider 'openai)

   (make-hf-instance
    :model 'o3
    :provider 'openai)

   (make-hf-instance
    :model 'o3-deep-research
    :provider 'openai)

   (make-hf-instance
    :model 'o3-mini
    :provider 'openai)

   (make-hf-instance
    :model 'o3-pro
    :provider 'openai)

   (make-hf-instance
    :model 'o4-mini
    :provider 'openai)

   (make-hf-instance
    :model 'o4-mini-deep-research
    :provider 'openai)

   (make-hf-instance
    :model 'claude-haiku
    :name 'claude-3-5-haiku-20241022
    :provider 'anthropic)

   (make-hf-instance
    :model 'claude-opus
    :name 'claude-opus-4-1-20250805
    :provider 'anthropic)

   (make-hf-instance
    :model 'claude-sonnet
    :name 'claude-sonnet-4-20250514
    :provider 'anthropic)

   (make-hf-instance
    :model 'r1-1776
    :provider 'perplexity)

   (make-hf-instance
    :model 'sonar-deep-research
    :provider 'perplexity)

   (make-hf-instance
    :model 'sonar-pro
    :provider 'perplexity)

   (make-hf-instance
    :model 'sonar-reasoning-pro
    :provider 'perplexity)

   (make-hf-instance
    :model 'compound-beta
    :provider 'groq)

   (make-hf-instance
    :model 'deepseek-r1-distill-llama-70b
    :provider 'groq)

   (make-hf-instance
    :model 'llama-3.3-70b-versatile
    :provider 'groq)

   (make-hf-instance
    :model 'Llama-Guard-4-12B
    :name 'meta-llama/Llama-Guard-4-12B
    :provider 'groq)

   (make-hf-instance
    :model 'Llama-4-Maverick-17B-128E-Instruct
    :name 'meta-llama/llama-4-maverick-17b-128e-instruct
    :provider 'groq)

   (make-hf-instance
    :model 'Llama-4-Scout-17B-16E-Instruct
    :name 'meta-llama/llama-4-scout-17b-16e-instruct
    :provider 'groq)

   (make-hf-instance
    :model 'DeepSeek-R1-0528
    :name 'deepseek/deepseek-r1-0528:free
    :provider 'openrouter)

   (make-hf-instance
    :model 'Llama-4-Maverick-17B-128E-Instruct
    :name 'meta-llama/llama-4-maverick:free
    :provider 'openrouter)

   ))

(defun hf-instances-for-model (name)
  "Return all instances that match the given model NAME."
  (cl-loop for instance in hf-instances-list
           when (eq (hf-instance-model instance) name)
           collect instance))

;;; (inspect (hf-instances-for-model 'gemma-3-1b-it))

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
    (replace-regexp-in-string "--" "/" name)))

;;; (hf-full-model-name "~/Models/TheBloke_WizardCoder-Python-7B-V1.0-GGUF")
;;; (hf-full-model-name "~/Models/TheBloke_WizardCoder-Python-7B-V1.0-GGUF/Users/johnw/.cache/huggingface/hub/models--mlx-community--whisper-large-v3-mlx")

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

;; (inspect (hf-get-gguf-path "~/Models/TheBloke_WizardCoder-Python-34B-V1.0-GGUF"))

(defun hf-get-context-length (model)
  "Get maximum context length of MODEL."
  (when-let* ((gguf (expand-file-name (hf-get-gguf-path model))))
    (with-temp-buffer
      (when (zerop (call-process "gguf-tools" nil t nil "show" gguf))
        (goto-char (point-min))
        (when (search-forward ".context_length" nil t)
          (when (re-search-forward "\\[uint32\\] \\([0-9]+\\)" nil t)
            (string-to-number (match-string 1))))))))

;; (inspect (hf-get-context-length "~/Models/unsloth_gemma-3-27b-it-GGUF"))
;; (inspect (hf-get-context-length "~/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF"))

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

(defun hf-get-model (model-name &optional models-hash)
  "Using MODELS-HASH, find the model with the given MODEL-NAME."
  (let ((models-hash (or models-hash (hf-make-models-hash))))
    (gethash model-name models-hash)))

(defsubst hf-get-instance-model (models-hash instance)
  "Using MODELS-HASH, find the model for the given INSTANCE."
  (gethash (hf-instance-model instance) models-hash))

(defun hf-get-instance-model-name (instance)
  "Using MODELS-HASH, find the model name for the given INSTANCE."
  (or (hf-instance-name instance)
      (hf-instance-model instance)))

(defun hf-get-instance-context-length (models-hash instance)
  "Find maximum context-length for the given INSTANCE.
If the instance does not specify its own context-length, lookup the
model in MODELS-HASH and use that value."
  (or (hf-instance-context-length instance)
      (hf-model-context-length (hf-get-instance-model models-hash instance))))

;;; (hf-get-instance-context-length (gethash 'Qwen3-235B-A22B-Thinking-2507--llama-cpp--hera hf-instances-hash))

(defun hf-get-instance-max-tokens (models-hash instance)
  "Find maximum output tokens for the given INSTANCE.
If the instance does not specify its own maximum output tokens lookup
the model in MODELS-HASH and use that value."
  (or (hf-instance-max-tokens instance)
      (hf-model-max-tokens (hf-get-instance-model models-hash instance))))

(defun hf-get-instance-gguf-path (instance)
  "Return file path for the GGUF file related to INSTANCE."
  (or (hf-instance-file-path instance)
      (hf-get-gguf-path (hf-instance-model-path instance))))

;;; (hf-get-instance-gguf-path (gethash 'Qwen3-Coder-480B-A35B-Instruct--llama-cpp--hera hf-instances-hash))

(defun hf-insert-instance-llama-swap (instance &optional models-hash)
  "Instance the llama-swap.yaml config for INSTANCE given MODELS-HASH."
  (interactive)
  (let* ((models-hash (or models-hash (hf-make-models-hash)))
         (max-tokens
          (hf-get-instance-max-tokens models-hash instance))
         (context-length
          (hf-get-instance-context-length models-hash instance))
         (model (hf-instance-model instance))
         (args
          (mapconcat
           #'identity
           (append
            (hf-instance-arguments instance)
            (and context-length
                 (cl-case (hf-instance-engine instance)
                   ('llama-cpp (list "--ctx-size"
                                     (number-to-string context-length)))))
            (and max-tokens
                 (list (cl-case (hf-instance-engine instance)
                         ('llama-cpp "--predict")
                         ('mlx-lm "--max-tokens"))
                       (number-to-string max-tokens))))
           " "))
         (leader (format "
  \"%s\":
    proxy: \"http://127.0.0.1:${PORT}\"
    cmd: >" model))
         (footer "
    checkEndpoint: /health
"))
    (cl-case (hf-instance-engine instance)
      ('llama-cpp
       (when-let* ((path (hf-get-instance-gguf-path instance)))
         (insert
          leader
          (format "
      /etc/profiles/per-user/johnw/bin/llama-server
        --host 127.0.0.1 --port ${PORT} --offline --jinja
        --model %s %s" (expand-file-name path) args)
          footer)))
      ('mlx-lm
       (insert
        leader
        (format "
      /etc/profiles/per-user/johnw/bin/mlx-lm server
        --host 127.0.0.1 --port ${PORT}
        --model %s %s" model args)
        footer)))))

(defun hf-generate-build-yaml (hostname &optional models-hash)
  "Build llama-swap.yaml configuration for HOSTNAME.
If MODELS-HASH is provided, use that instead of recomputing it."
  (interactive)
  (let ((models-hash (or models-hash (hf-make-models-hash))))
    (with-current-buffer (get-buffer-create "*llama-swap.yaml*")
      (erase-buffer)
      (insert hf-llama-swap-prolog)
      (insert "\nmodels:")
      (dolist (instance hf-instances-list)
        (when (and (eq 'local (hf-instance-provider instance))
                   (member hostname (hf-instance-hostnames instance)))
          (hf-insert-instance-llama-swap instance models-hash)))
      (insert hf-llama-swap-epilog)
      (yaml-mode)
      (current-buffer))))

;;; (display-buffer (hf-generate-build-yaml "hera"))

(defun hf-build-yaml ()
  "Build llama-swap.yaml configuration."
  (interactive)
  (let ((models-hash (hf-make-models-hash)))
    (hf-check-instances models-hash)
    (let ((yaml-path (expand-file-name "llama-swap.yaml" hf-gguf-models)))
      (with-temp-buffer
        (insert (with-current-buffer
                    (hf-generate-build-yaml hf-default-hostname models-hash)
                  (buffer-string)))
        (write-file yaml-path))
      (shell-command "killall llama-swap 2>/dev/null"))))

(defun hf-get-instance-gptel-backend (instance &optional hostname models-hash)
  "Instance the llama-swap.yaml config for INSTANCE given MODELS-HASH.
If HOSTNAME is non-nil, only generate definitions for that host."
  (interactive)
  (let* ((models-hash (or models-hash (hf-make-models-hash)))
         (max-tokens (hf-get-instance-max-tokens models-hash instance))
         (context-length (hf-get-instance-context-length models-hash instance))
         (model (hf-get-instance-model models-hash instance))
         (model-name (hf-get-instance-model-name instance)))
    (when (null model)
      (error "Unknown model: %S" (hf-instance-model instance)))
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
  (cl-loop for models-hash = (hf-make-models-hash)
           for instance in hf-instances-list
           for backends = (hf-get-instance-gptel-backend instance hostname)
           when backends
           nconc backends))

;;; (inspect (hf-gptel-backends))

(defun hf-lookup-instance (model)
  "Return the instance whole model matches the symbol MODEL."
  (cl-loop for instance in hf-instances-list
           when (eq model (hf-instance-model instance))
           return instance))

;;; (hf-get-instance-gptel-backend (hf-lookup-instance 'Qwen3-Coder-480B-A35B-Instruct))

(defun hf-check-instances (&optional models-hash)
  "Check all model and instances definitions.
If MODELS-HASH is provided, use that instead of recomputing it."
  (interactive)
  (let ((models-hash (or models-hash (hf-make-models-hash))))
    (dolist (model hf-models-list)
      (let ((capabilities (hf-model-capabilities model))
            (mime-types (hf-model-mime-types model))
            (kind (hf-model-kind model)))
        (dolist (cap capabilities)
          (unless (member cap hf-all-model-capabilities)
            (error "Unknown capability: %S" cap)))
        (dolist (mime mime-types)
          (unless (member mime hf-all-model-mime-types)
            (error "Unknown mime-type: %S" mime)))
        (unless (member kind hf-all-model-kinds)
          (error "Unknown kind: %S" kind))))
    (dolist (instance hf-instances-list)
      (let ((model (hf-get-instance-model models-hash instance))
            (model-path (hf-instance-model-path instance))
            (file-path (hf-instance-file-path instance))
            (hostnames (hf-instance-hostnames instance))
            (provider (hf-instance-provider instance))
            (engine (hf-instance-engine instance))
            (draft-model (hf-instance-draft-model instance)))
        (unless model
          (error "Unknown model: %S" (hf-instance-model instance)))
        (unless (or (null model-path)
                    (file-directory-p model-path))
          (error "Unknown model-path: %s" model-path))
        (unless (or (null file-path)
                    (file-regular-p file-path))
          (error "Unknown file-path: %s" file-path))
        (dolist (host hostnames)
          (unless (member host hf-valid-hostnames)
            (error "Unknown hostname: %s" host)))
        (unless (member provider hf-all-model-providers)
          (error "Unknown provider: %s" provider))
        (unless (member engine hf-all-model-engines)
          (error "Unknown engine: %s" engine))
        (unless (or (null draft-model)
                    (gethash draft-model models-hash))
          (error "Unknown draft-model: %S" draft-model))))))

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

(cl-defun hf-generate-instance-declarations
    (&key (hostname hf-default-hostname)
          (directory "~/Models"))
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
