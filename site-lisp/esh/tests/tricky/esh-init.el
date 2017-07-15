(when (bound-and-true-p esh-server-initializing)
  (load-theme 'tango t))

(define-minor-mode tricky-mode
  "Minor mode demonstrating tricky highlighting."
  :lighter " trk"
  (add-to-list 'font-lock-extra-managed-props 'line-height)
  (esh-add-keywords
    `(("abcdef" (0 '(face ((:slant italic))) append))
      ("efghij" (0 '(face ((:foreground "red"))) append))
      ("ijklmn" (0 '(face ((:weight bold))) append))
      ("bcdefghijkl" (0 '(face ((:box t))) append))
      ("4" (0 '(face ((:height 2.5)))))
      ("tall\\(\n\\)" (1 '(face nil line-height 2.0))))))


(define-minor-mode subsup-mode
  "Minor mode demonstrating subscripts and superscripts."
  :lighter " subssup"
  (add-to-list 'font-lock-extra-managed-props 'display)
  (esh-add-keywords
    `(("x\\(.*\\)" (1 '(face nil display (raise 1))))
      ("y\\(.*\\)" (1 '(face nil display (raise -1)))))))

(defun ~/setup-overlays ()
  "Add a collection of conflicting overlays to the current buffer."
  (erase-buffer)
  (insert "abcdefghijklmnopqrstuv")
  (put 'esh-test 'face '((:box "#000000")))
  (mapc #'delete-overlay (overlays-in (point-min) (point-max)))
  (let ((ov (make-overlay 1 9)))
    (overlay-put ov 'face '((:foreground "#FF0000"))))
  (let ((ov (make-overlay 3 11)))
    (overlay-put ov 'face '((:background "#00FF00"))))
  (let ((ov (make-overlay 5 14)))
    (overlay-put ov 'face '((:weight bold :slant italic))))
  (let ((ov (make-overlay 7 16)))
    (overlay-put ov 'category 'esh-test))
  (let ((ov (make-overlay 16 23)))
    (overlay-put ov 'display (propertize "display" 'face '((:background "blue"))))
    (overlay-put ov 'before-string (propertize "before" 'face '((:underline t))))
    (overlay-put ov 'after-string (propertize "after" 'face '((:underline t))))))

(define-minor-mode overlays-mode
  "Minor mode demonstrating overlays over text."
  :lighter " overlays"
  (~/setup-overlays)
  (add-hook 'esh-pre-highlight-hook #'~/setup-overlays nil t))
