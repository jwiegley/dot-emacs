(require 'cl-lib)
(require 'esh-io)
(require 'esh-cmd)

(defalias 'eshell-with-copied-handles 'eshell-copy-handles)

(defun eshell/wc ()
  (eshell-with-copied-handles
   (let ((buf (get-buffer-create " *eshell/wc*")))
     (eshell-function-target-create
      `(lambda (input)
         (with-current-buffer ,buf
           (insert input)))
      `(lambda (_status)
         (let ((eshell-current-handles ,eshell-current-handles))
           (eshell-print
            (format "%s\n" (with-current-buffer ,buf (point-max)))))
         (kill-buffer ,buf))))))

