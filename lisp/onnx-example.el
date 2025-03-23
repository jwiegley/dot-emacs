;; We assume the library is available in your load-path and you have downloaded
;; the necessary model onnx file
(require 'onnx)
(require 'onnx-ml-utils)
(setq model (onnx-load "model_O2.onnx"))

(require 'tokenizers)

;; Model loading here happens via automatic http downloads
;; `encoding' is a list of token-ids, token-type-ids, and attention-mask
(setq encoding (let ((tk (tokenizers-from-pretrained "sentence-transformers/all-MiniLM-L6-v2")))
                 (tokenizers-enable-padding tk 0 "[PAD]")
                 (tokenizers-encode-batch tk ["This is an example sentence" "Each sentence is converted"] t)))

(let ((output (onnx-run model `(("input_ids" . ,(nth 0 encoding))
                                ("token_type_ids" . ,(nth 1 encoding))
                                ("attention_mask" . ,(nth 2 encoding)))
                        '("last_hidden_state"))))
  (setq output (onnx-ml-utils-nmean-pool output (nth 2 encoding)))
  (onnx-ml-utils-nl2-normalize output)
  output) ;; Shape N x D
