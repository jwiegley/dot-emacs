;;
;; A module to help with proofreading thanks to gptel
;;

(require 'gptel)
(require 'uuidgen)

(defvar gptel-proof-gentle-prompt
  (concat "Please fix spelling, punctuation and grammar in the follow text. "
          "Where possible, keep the word choice and tone unchanged. "
          "Output only the corrected text.\n"
          "\n"
          "The outputed text should use a line length line breaks "
          "that are similar to the input text. Visually, the old "
          "and new text should look similar. They should also have "
          "as few whitespace changes as possible. The new and old text "
          "will be run through the unix command diff, so only "
          "critical changes should be visible."))

(defvar gptel-proof-aggressive-prompt
  (concat "Please fix spelling, punctuation and grammar in the follow text. "
          "Where possible, rewrite the text to use  active voice and to use fewer words."
          "Use a tone that's appropriate to publish in a social media post, so that it's casual "
          "but still something that my Mom would understand.\n\n"
          "\n"
          "The outputed text should use a line length line breaks "
          "that are similar to the input text. Visually, the old "
          "and new text should look similar. They should also have "
          "as few whitespace changes as possible. The new and old text "
          "will be run through the unix command diff, so only "
          "critical changes should be visible."))

(defun gptel-proof-apply-fix (buffer marker correction)
  "Apply the changes chatgpt has suggested."
  (with-current-buffer buffer
    (goto-char (point-min))
    (when (re-search-forward marker nil t)
      (let* ((end (point))
             (start (- end (length marker))))
        (delete-region start end)
        (insert correction)))))

(defun gptel-proof (start end &optional aggressive)
  "Proofread either the region using ChatGPT magic."
  (interactive "r\nP")
  (when (not (use-region-p))
    (error "No region selected"))
  (let* ((marker (format "{proof:%s}" (with-temp-buffer
                                        (uuidgen nil)
                                        (upcase (buffer-string)))))
         (input (buffer-substring start end))
         (prompt-style (if aggressive "aggressive" "gentle"))
         (start-conflict "<<<<<<< Original\n")
         (sep-conflict "=======\n")
         (end-conflict (format ">>>>>>> Proofread (%s)\n" prompt-style))
         (gptel-model 'gemma2:27b)
         (gptel-backend
          (gptel-make-ollama "Ollama"
            :host "localhost:11434"
            :protocol "http"
            :stream t
            :request-params '(:options (:num_ctx 32768))
            :models
            '((gemma2:27b
               :description "Google Gemma 2 is a high-performing and efficient model"
               :capabilities (media)
               :mime-types ("image/jpeg" "image/png" "text/plain"))))))
    (save-excursion
      (goto-char start)
      (insert start-conflict)
      (goto-char (+ end (length start-conflict)))
      (insert (concat sep-conflict marker "\n" end-conflict)))
    (gptel-request input
      :callback (lambda (response info)
                  (if response
                      (gptel-proof-apply-fix (plist-get info :buffer)
                                             (plist-get info :context)
                                             response)
                    (error "Proofread error: %s" (plist-get info :status))))
      :context marker
      :system (if aggressive
                  gptel-proof-aggressive-prompt
                gptel-proof-gentle-prompt))))

(provide 'gptel-proof)
