;; -*- flycheck-disabled-checkers: (emacs-lisp-checkdoc) -*-
(load (concat (file-name-directory (or load-file-name (buffer-file-name)
                                       default-directory))
              "utils.el") nil 'nomessage 'nosuffix)
(require 'cl-lib)



(describe "Hiding process buffer does not switch current window"
  (it "when process is active"
    (with-lua-buffer
     (let ((cur-buf (current-buffer)))
       (expect (get-buffer-window cur-buf))
       (lua-start-process)
       (lua-hide-process-buffer)
       (expect (get-buffer-window cur-buf)))))

  (it "and does not signal when process is already killed"
    (with-lua-buffer
     (let ((cur-buf (current-buffer)))
       (lua-start-process)
       (lua-kill-process)
       (lua-hide-process-buffer)
       (expect (get-buffer-window cur-buf)))))

  (it "when process is not started"
    (with-lua-buffer
     (let ((cur-buf (current-buffer)))
       (expect lua-process-buffer :to-be nil)
       (lua-hide-process-buffer)
       (expect (get-buffer-window cur-buf))))))


(require 'compile)
(if (fboundp 'compilation--loc->file-struct)
    (defun get-error-file (err-info)
      (caar (compilation--loc->file-struct
             (compilation--message->loc (compilation-next-error 0)))))
  (defun get-error-file (err-info)
    (caar (nth 2 (car err-info)))))


(describe "Fontification in compilation buffer"
  (xit "fontifies runtime error messages"
    (with-lua-buffer
     (insert "\
function bar()
   error(123)
end

function foo()
   bar()
end
")
     (rename-buffer "test-send-runtime-error.lua" 'unique)
     ;; By default non-nil compilation-message-face is appended to
     ;; compilation-error faces, let's simplify the checks.
     (let ((compilation-message-face nil))
       (lua-send-buffer)
       (lua-send-string "foo()")
       ;; Make sure to wait enough to get all the output from the subprocess.
       (while (accept-process-output lua-process 0 200))
       (with-current-buffer lua-process-buffer
         (expect
          (get-buffer-line-faces)
          :to-equal
          '(nil ;; motd line (not highlighted)
            nil ;; first prompt (also not highlighted)
            ("test-send-runtime-error.lua" compilation-error
             "2" compilation-line-number) ;; error message
            nil                           ;; stack traceback
            nil                           ;; in function error
            ("test-send-runtime-error.lua" compilation-error
             "2" compilation-line-number) ;; in 'bar'
            ("test-send-runtime-error.lua" compilation-error
             "6" compilation-line-number) ;; in 'foo'
            ("stdin" compilation-error "1" compilation-line-number)
            nil ;; in main chunk
            nil))))))

  (xit "fontifies syntax error messages"
    (with-lua-buffer
     (rename-buffer "test-send-syntax-error.lua")
     (insert "\
function () end
")
     ;; By default non-nil compilation-message-face is appended to
     ;; compilation-error faces, let's simplify the checks.
     (let ((compilation-message-face nil))
       (lua-send-buffer)
       (while (accept-process-output lua-process 0 200))
       (with-current-buffer lua-process-buffer
         (expect
          (get-buffer-line-faces)
          :to-equal
          '(nil ;; motd line, no highlight
            nil ;; first prompt, also no highlight
            (;; "stdin" is being highlighted here because compilation mode
             ;; thinks it is some sort of "make: ..." message.  This doesn't
             ;; happen in wildlife, because there's a default message face
             ;; (underline) that prevents this.  In tests this is turned off,
             ;; see `(compilation-message-face nil)' above, to simplify
             ;; font-lock face checks.
             "stdin" font-lock-function-name-face
             "test-send-syntax-error.lua" compilation-error
             "1" compilation-line-number)
            ;; stacktrace with misc info, no font-lock
            nil nil
            ("stdin" compilation-error "1" compilation-line-number)
            ("stdin" compilation-error "1" compilation-line-number)
            nil nil))))))


  (it "does not ask for file on \"stdin:NN\" errors"
    (let ((fname (make-temp-file "lua_mode_test" nil ".lua"))
          buf)
      (unwind-protect
          (progn
            (save-current-buffer
              (setq buf (find-file fname))
              (insert "function () end")
              ;; Make sure the buffer can be killed cleanly
              (set-buffer-modified-p nil)
              (lua-send-buffer)
              (while (accept-process-output lua-process 0 200))
              (with-current-buffer lua-process-buffer
                (font-lock-fontify-buffer))
              (cl-letf
                  (((symbol-function 'read-file-name)
                    (lambda (&rest args)
                      (error "read-file-name must not be called"))))
                (expect (next-error) :to-be nil)
                (with-current-buffer lua-process-buffer
                  (expect fname :to-equal
                          (get-error-file (compilation-next-error 0))))

                (expect (next-error) :to-be nil)
                (with-current-buffer lua-process-buffer
                  (expect "stdin" :to-equal
                          (get-error-file (compilation-next-error 0)))))))
        (when buf
          (kill-buffer buf))
        (delete-file fname)
        (kill-buffer "*lua*")))))

(describe "String escaping"
  (it "Escapes literal tabs"
    (expect (string=
	     (lua-make-lua-string "\
	-- comment indented with a tab")
	     "'\\t-- comment indented with a tab'"))))
