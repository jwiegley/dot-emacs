(require 'ert)
(require 'ido)
(require 'ido-vertical-mode)

(ido-mode 1)
(ido-vertical-mode 1)

;;; invoke ido-switch-buffer to initialize ido variables that would
;;; otherwise throw void error
(execute-kbd-macro [24 98 return] 1)

(ert-deftest ivm-should-install-decorations ()
  (ido-vertical-mode 1)
  (let ((prospects (ido-completions "")))
    (should (string-match "->" prospects))
    (should (string-match "\n" prospects))))

(ert-deftest ivm-should-indicate-more-results ()
  (ido-vertical-mode 1)
  (let ((buffers (mapcar (lambda (num)
                           (get-buffer-create
                            (format "ivm-test-buffer-%s" num)))
                         (number-sequence 1 11)))
        prospects)
    (save-window-excursion
      (execute-kbd-macro [24 98 ?i ?v ?m ?- ?t ?e ?s ?t])
      (setq prospects (ido-completions "ivm-test"))
      (should (string-match "\.\.\.$" prospects)))
    (mapc 'kill-buffer buffers)))

(ert-deftest ivm-should-properly-disable-itself ()
  (ido-vertical-mode 1)
  (ido-vertical-mode -1)
  (should (not (string-match "\n" (ido-completions "")))))

(ert-deftest ivm-should-show-confirm-dialog ()
  (ido-vertical-mode 1)
  (let* ((no-results [24 98 ?t ?h ?i ?s ?s ?h ?o ?u ?l ?d ?n ?o ?t ?m ?a ?t ?c ?h])
         (confirm (vconcat no-results [return])))
    (execute-kbd-macro no-results 1)
    (should (string-match "No Match" (buffer-name (current-buffer))))
    (kill-buffer (current-buffer))
    (execute-kbd-macro confirm 1)
    (should (string-match "Confirm" (buffer-name (current-buffer))))
    (kill-buffer (current-buffer))))

(ert-deftest ivm-should-handle-fontified-candidates ()
  (let ((ido-matches '((#(".ido.last" 1 4 (face ido-vertical-match-face)) "/Users/JS/")
                       ""
                       (#("200-ido.el" 4 7 (face ido-vertical-match-face)) "/Users/JS/.emacs.d/configs/" "~/.emacs.d/configs/"))))
    (should (ido-vertical-completions "ido"))))

;;; The following tests are pretty fragile. ido-vertical-completions
;;; depends on the global value of ido-matches, which we set. It
;;; returns the completions as a string, and we can check the text
;;; properties of particular characters in the return to see that they
;;; have the expected faces.

(ert-deftest ivm-should-highlight-matched-candidates ()
  (let* ((ido-use-faces t)
         (ido-matches '("ido" "ido-vertical"))
         (ido-query (ido-vertical-completions "ido"))
         (first-comp-pos (string-match "ido" ido-query))
         (ido-query-first-comp-face (get-text-property first-comp-pos 'face ido-query))
         (ido-query-second-comp-face (get-text-property (+ first-comp-pos 7) 'face ido-query))
         (debug nil))
    (when debug (prin1 ido-query))
    (should (and (memq 'ido-vertical-match-face ido-query-first-comp-face)
                 (memq 'ido-vertical-first-match-face ido-query-first-comp-face)))
    (should (and (memq 'ido-vertical-match-face `(,ido-query-second-comp-face))
                 (eq nil (get-text-property 19 'face ido-query))))))

(ert-deftest ivm-should-not-highlight-without-ido-use-faces ()
  (let* ((ido-use-faces nil)
         (ido-matches '("ido"))
         (ido-query (ido-vertical-completions "ido"))
         (first-comp-pos (string-match "ido" ido-query))
         (ido-query-first-comp-face (get-text-property first-comp-pos 'face ido-query))
         (debug nil))
    (when debug (prin1 ido-query))
    (should (eq nil ido-query-first-comp-face))))

(ert-deftest ivm-should-not-highlight-missed-candidates ()
  (let* ((ido-use-faces t)
         (ido-matches '("ido" "ido-vertical"))
         (ido-query (ido-vertical-completions "no results"))
         (first-comp-pos (string-match "ido" ido-query))
         (second-comp-pos (+ 7 first-comp-pos))
         (ido-query-first-comp-face (get-text-property first-comp-pos 'face ido-query))
         (ido-query-second-comp-face (get-text-property second-comp-pos 'face ido-query))
         (debug nil))
    (when debug (prin1 ido-query))
    (should (memq 'ido-vertical-first-match-face `(,ido-query-first-comp-face)))
    (should (and (eq nil ido-query-second-comp-face)))))

(ert-deftest ivm-should-highlight-only-candidate ()
  (let* ((ido-use-faces t)
         (ido-matches '("ido"))
         (ido-query (ido-vertical-completions "no results"))
         (first-comp-pos (string-match "ido" ido-query))
         (ido-query-first-comp-face (get-text-property first-comp-pos 'face ido-query))
         (debug nil))
    (when debug (prin1 ido-query))
    (should (memq 'ido-vertical-only-match-face `(,ido-query-first-comp-face)))))

(ert-deftest ivm-should-show-count ()
  (let* ((ido-matches '("1" "2" "3" "4" "5"))
         (ido-vertical-show-count t)
         (ido-use-faces nil)
         (query (ido-vertical-completions "")))
    ;; Exposes a bug where we were toggling the count on and off
    ;; instead of keeping it on
    (setq query (ido-vertical-completions ""))
    (should (string= " [5]\n" (substring query 0 5)))
    ;; Count should update when filtering completions
    (setq ido-matches '("1"))
    (setq query (ido-vertical-completions "1"))
    (should (string= " [1]" (substring query 0 4)))))

(ert-deftest ivm-should-turn-off-count ()
  (let* ((ido-matches '("1"))
         (ido-vertical-show-count nil)
         (query (ido-vertical-completions "")))
    (should (string= "\n-> " (substring-no-properties query 0 4)))))
