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

(defconst model-formats '(GGUF safetensors))

(defconst model-kinds '(text-generation embedding reranker))

(defconst model-engines '(llama-cpp koboldcpp mlx-lm))

(cl-defstruct hf-model
  "Configuration data for a model, and its family of instances."
  name                                  ; name of the model
  context-length                        ; model context length
  max-tokens                            ; number of tokens to predict
  temperature                           ; model temperature
  min-p                                 ; minimum p
  top-p                                 ; top p
  top-k                                 ; top k
  kind                                  ; nil, or symbol from model-kinds
  reasoning                             ; t if model supports reasoning
  aliases                               ; model alias names
  inactive)                             ; t if model is not being used

(cl-defstruct hf-instance
  "Configuration data for a model, and its family of instances."
  model                                 ; reference to model config
  context-length                        ; context length to use for instance
  max-tokens                            ; number of tokens to predict
  hostname                              ; where does the model run?
  file-format                           ; GGUF, safetensors
  model-path                            ; path to model directory
  file-path                             ; (optional) path to model file
  draft-model                           ; (optional) path to draft model file
  engine                                ; llama.cpp, koboldcpp, etc.
  arguments)

(defvar hf-models-list
  (list

   (make-hf-model :name 'Qwen.Qwen3-Reranker-8B
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20
                  :kind 'reranker)

   (make-hf-model :name 'Qwen3-Embedding-8B
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20
                  :kind 'embedding)

   (make-hf-model :name 'WizardCoder-Python-34B-V1.0
                  :context-length 16384
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'WizardCoder-Python-7B-V1.0
                  :context-length 16384
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Mistral-Nemo-Instruct-2407
                  :context-length 1024000
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Llama-3.3-Nemotron-Super-49B-v1
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'r1-1776-distill-llama-70b
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'bge-m3
                  :context-length 8192
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20
                  :kind 'embedding)

   (make-hf-model :name 'DeepSeek-R1-Distill-Qwen-32B
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'DeepSeek-R1-0528
                  :context-length 163840
                  :temperature 0.6
                  :min-p 0.01
                  :top-p 0.95
                  :top-k 20)

   (make-hf-model :name 'DeepSeek-R1-0528-Qwen3-8B
                  :context-length 131072
                  :temperature 0.6
                  :min-p 0.01
                  :top-p 0.95
                  :top-k 20)

   (make-hf-model :name 'DeepSeek-V3-0324-UD
                  :context-length 163840
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Devstral-Small-2505
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Kimi-K2-Instruct
                  :context-length 131072
                  :temperature 0.6
                  :min-p 0.01
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Llama-4-Maverick-17B-128E-Instruct
                  :context-length 1048576
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Llama-4-Scout-17B-16E-Instruct
                  :context-length 10485760
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Magistral-Small-2506
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Mistral-Small-3.2-24B-Instruct-2506
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'nomic-embed-text-v2-moe
                  :context-length 512
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20
                  :kind 'embedding)

   (make-hf-model :name 'Phi-4-reasoning-plus
                  :context-length 32768
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-0.6B
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-1.7B
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-4B
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-8B
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-14B
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-32B
                  :context-length 40960
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'Qwen3-30B-A3B-Thinking-2507
                  :context-length 262144
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

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
                  :top-k 20)

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
                  :context-length 32768
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'gemma-3-4b-it
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'gemma-3-12b-it
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'gemma-3-27b-it
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'gemma-3n-E4B-it
                  :context-length 32768
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'gpt-oss-20b
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'gpt-oss-120b
                  :context-length 131072
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'BAAI/bge-base-en-v1.5
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'BAAI/bge-large-en-v1.5
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'mlx-community/whisper-large-v3-mlx
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'nvidia/NV-Embed-v2
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   (make-hf-model :name 'sentence-transformers/all-MiniLM-L6-v2
                  :temperature 1.0
                  :min-p 0.05
                  :top-p 0.8
                  :top-k 20)

   ))

(defvar hf-models-hash
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
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/DevQuasar_Qwen.Qwen3-Reranker-8B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-Embedding-8B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/Qwen_Qwen3-Embedding-8B-GGUF"
    :engine 'llama-cpp
    :arguments '("--embedding"
                 "--pooling" "last"
                 "--ubatch-size" "8192"
                 "--batch-size" "2048"))

   (make-hf-instance
    :model 'WizardCoder-Python-34B-V1.0
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/TheBloke_WizardCoder-Python-34B-V1.0-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'WizardCoder-Python-7B-V1.0
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/TheBloke_WizardCoder-Python-7B-V1.0-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Mistral-Nemo-Instruct-2407
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/bartowski_Mistral-Nemo-Instruct-2407-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Llama-3.3-Nemotron-Super-49B-v1
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/bartowski_nvidia_Llama-3.3-Nemotron-Super-49B-v1-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'r1-1776-distill-llama-70b
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/bartowski_perplexity-ai_r1-1776-distill-llama-70b-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'bge-m3
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/gpustack_bge-m3-GGUF"
    :engine 'llama-cpp
    :arguments '("--embedding"
                 "--pooling" "mean"
                 "--ubatch-size" "8192"
                 "--batch-size" "4096"))

   (make-hf-instance
    :model 'DeepSeek-R1-Distill-Qwen-32B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/lmstudio-community_DeepSeek-R1-Distill-Qwen-32B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'nomic-embed-text-v2-moe
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/nomic-ai_nomic-embed-text-v2-moe-GGUF"
    :engine 'llama-cpp
    :arguments '("--embedding"
                 "--ubatch-size" "8192"))

   (make-hf-instance
    :model 'DeepSeek-R1-0528
    :context-length 16384
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_DeepSeek-R1-0528-GGUF"
    :engine 'llama-cpp
    :arguments '("--cache-type-k" "q4_1"
                 "--seed" "3407"))

   (make-hf-instance
    :model 'DeepSeek-R1-0528-Qwen3-8B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_DeepSeek-R1-0528-Qwen3-8B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'DeepSeek-V3-0324-UD
    :context-length 12000
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_DeepSeek-V3-0324-GGUF-UD"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Devstral-Small-2505
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Devstral-Small-2505-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Kimi-K2-Instruct
    :context-length 32768
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Kimi-K2-Instruct-GGUF"
    :engine 'llama-cpp
    :arguments '("--cache-type-k" "q4_1"
                 "-n" "32768"
                 "--seed" "3407"))

   (make-hf-instance
    :model 'Llama-4-Maverick-17B-128E-Instruct
    :context-length 65536
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Llama-4-Maverick-17B-128E-Instruct-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Llama-4-Scout-17B-16E-Instruct
    :context-length 1048576
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Llama-4-Scout-17B-16E-Instruct-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Magistral-Small-2506
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Magistral-Small-2506-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Mistral-Small-3.2-24B-Instruct-2506
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Mistral-Small-3.2-24B-Instruct-2506-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Phi-4-reasoning-plus
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Phi-4-reasoning-plus-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-0.6B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-0.6B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-1.7B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-1.7B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-14B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-14B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-235B-A22B-Instruct-2507
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-235B-A22B-Instruct-2507-GGUF"
    :engine 'llama-cpp
    :arguments '("--repeat-penalty" "1.05"
                 "--cache-type-k" "q8_0"
                 "--top-k" "20"
                 "--flash-attn"
                 "--cache-type-v" "q8_0"
                 "-n" "81920"))

   (make-hf-instance
    :model 'Qwen3-235B-A22B-Thinking-2507
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-235B-A22B-Thinking-2507-GGUF"
    :engine 'llama-cpp
    :arguments '("--repeat-penalty" "1.05"
                 "--cache-type-k" "q8_0"
                 "--top-k" "20"
                 "--flash-attn"
                 "--cache-type-v" "q8_0"
                 "-n" "32768"))

   (make-hf-instance
    :model 'Qwen3-30B-A3B-Thinking-2507
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-30B-A3B-Thinking-2507-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-32B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-32B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-4B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-4B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-8B
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-8B-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'Qwen3-Coder-30B-A3B-Instruct
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-Coder-30B-A3B-Instruct-GGUF"
    :engine 'llama-cpp
    :arguments '("--repeat-penalty" "1.05"
                 "--cache-type-k" "q8_0"
                 "--top-k" "20"
                 "--flash-attn"
                 "--cache-type-v" "q8_0"
                 "--rope-scaling" "yarn"
                 "--rope-scale" "4"
                 "--yarn-orig-ctx" "262144"
                 "-n" "65536"))

   (make-hf-instance
    :model 'Qwen3-Coder-480B-A35B-Instruct
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF"
    :file-path "~/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF/UD-Q4_K_XL/Qwen3-Coder-480B-A35B-Instruct-UD-Q4_K_XL-00001-of-00006.gguf"
    :engine 'llama-cpp
    :arguments '("--repeat-penalty" "1.05"
                 "--cache-type-k" "q4_1"
                 "--top-k" "20"
                 "--flash-attn"
                 "--cache-type-v" "q4_1"
                 "--rope-scaling" "yarn"
                 "--rope-scale" "4"
                 "--yarn-orig-ctx" "262144"
                 "-n" "65536"
                 "--chat-template-file" "/Users/johnw/Models/unsloth_Qwen3-Coder-480B-A35B-Instruct-GGUF/chat_template.jinja"))

   (make-hf-instance
    :model 'gemma-3-1b-it
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_gemma-3-1b-it-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'gemma-3-4b-it
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_gemma-3-4b-it-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'gemma-3-12b-it
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_gemma-3-12b-it-GGUF"
    :draft-model 'gemma-3-1b-it
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'gemma-3-27b-it
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_gemma-3-27b-it-GGUF"
    :draft-model 'gemma-3-4b-it
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'gemma-3n-E4B-it
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_gemma-3n-E4B-it-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'gpt-oss-20b
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_gpt-oss-20b-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'gpt-oss-120b
    :hostname "hera"
    :file-format 'GGUF
    :model-path "~/Models/unsloth_gpt-oss-120b-GGUF"
    :engine 'llama-cpp)

   (make-hf-instance
    :model 'BAAI/bge-base-en-v1.5
    :hostname "hera"
    :file-format 'safetensors
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'BAAI/bge-large-en-v1.5
    :hostname "hera"
    :file-format 'safetensors
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'mlx-community/whisper-large-v3-mlx
    :hostname "hera"
    :file-format 'safetensors
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'nvidia/NV-Embed-v2
    :hostname "hera"
    :file-format 'safetensors
    :engine 'mlx-lm)

   (make-hf-instance
    :model 'sentence-transformers/all-MiniLM-L6-v2
    :hostname "hera"
    :file-format 'safetensors
    :engine 'mlx-lm)

   ))

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

(defsubst hf-get-instance-model (instance)
  (gethash (hf-instance-model instance) hf-models-hash))

(defun hf-get-instance-context-length (instance)
  (or (hf-instance-context-length instance)
      (hf-model-context-length (hf-get-instance-model instance))))

;;; (hf-get-instance-context-length (gethash 'Qwen3-235B-A22B-Thinking-2507--llama-cpp--hera hf-instances-hash))

(defun hf-get-instance-max-tokens (instance)
  (or (hf-instance-max-tokens instance)
      (hf-model-max-tokens (hf-get-instance-model instance))))

(defun hf-get-instance-path (instance)
  (or (hf-instance-file-path instance)
      (hf-get-gguf-path
       (hf-instance-model-path instance))))

;;; (hf-get-instance-path (gethash 'Qwen3-Coder-480B-A35B-Instruct--llama-cpp--hera hf-instances-hash))

(defun hf-generate-build-yaml ()
  "Build llama-swap.yaml configuration."
  (interactive)
  (with-current-buffer (get-buffer-create "*llama-swap.yaml*")
    (erase-buffer)
    (insert hf-llama-swap-prolog)
    (insert "\nmodels:")
    (dolist (instance hf-instances-list)
      (let* ((model (hf-instance-model instance))
             (max-tokens (hf-get-instance-max-tokens instance))
             (context-length (hf-get-instance-context-length instance))
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
               " ")))
        (insert (format "
  \"%s\":
    proxy: \"http://127.0.0.1:${PORT}\"
    cmd: >" model))
        (cl-case (hf-instance-engine instance)
          ('llama-cpp
           (let ((path (expand-file-name (hf-get-instance-path instance))))
             (insert (format "
      /etc/profiles/per-user/johnw/bin/llama-server
        --host 127.0.0.1 --port ${PORT} --offline --jinja
        --model %s %s" path args))))
          ('mlx-lm
           (insert (format "
      /etc/profiles/per-user/johnw/bin/mlx-lm server
        --host 127.0.0.1 --port ${PORT}
        --model %s %s" model args))))
        (insert "
    checkEndpoint: /health
")))
    (insert hf-llama-swap-epilog)
    (yaml-mode)
    (current-buffer)))

;;; (display-buffer (hf-generate-build-yaml))

(defun hf-build-yaml ()
  "Build llama-swap.yaml configuration."
  (interactive)
  (let ((yaml-path (expand-file-name "llama-swap.yaml" hf-gguf-models)))
    (with-temp-buffer
      (insert (with-current-buffer (hf-generate-build-yaml)
                (buffer-string)))
      (write-file yaml-path))
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

(cl-defun hf-generate-instances-from-models-dir (&key (directory "~/Models"))
  "Generate model declarations from DIRECTORY's subdirectories."
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
                  "  :hostname \"" hf-hostname "\"\n"
                  "  :file-format 'GGUF\n"
                  "  :model-path \"" dir "\"\n"
                  "  :engine 'llama-cpp\n"
                  "  :arguments '())\n\n")))
      (display-buffer (current-buffer)))))

(provide 'hf)

;;; hf.el ends here
