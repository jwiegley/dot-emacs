;; deferred.el samples  -*- lexical-binding: t; -*-

(require 'cl-lib)
(require 'deferred)

;;; Basic Chain

(deferred:$
  (deferred:next
    (lambda () (message "deferred start")))
  (deferred:nextc it
    (lambda ()
      (message "chain 1")
      1))
  (deferred:nextc it
    (lambda (x)
      (message "chain 2 : %s" x)))
  (deferred:nextc it
    (lambda ()
      (read-minibuffer "Input a number: ")))
  (deferred:nextc it
    (lambda (x)
      (message "Got the number : %i" x)))
  (deferred:error it
    (lambda (err)
      (message "Wrong input : %s" err))))


;;; Timer

(deferred:$
  (deferred:wait 1000) ; 1000msec
  (deferred:nextc it
    (lambda (x)
      (message "Timer sample! : %s msec" x))))


;;; Command process

(deferred:$
  (deferred:process "ls" "-la")
  (deferred:nextc it
    (lambda (x) (insert x))))


;;; Web Access

;; Simple web access

(require 'url)

(deferred:$
  (deferred:url-retrieve "http://www.gnu.org")
  (deferred:nextc it
    (lambda (buf)
      (insert  (with-current-buffer buf (buffer-string)))
      (kill-buffer buf))))

;; Get an image

(deferred:$
  (deferred:url-retrieve "http://www.google.co.jp/intl/en_com/images/srpr/logo1w.png")
  (deferred:nextc it
    (lambda (buf)
      (insert-image
       (create-image
        (let ((data (with-current-buffer buf (buffer-string))))
          (substring data (+ (string-match "\n\n" data) 2)))
        'png t))
      (kill-buffer buf))))

;; HTTP POST

(deferred:$
  (deferred:url-post
    "http://127.0.0.1:8080/post-test.cgi"
    '(('a . "test") ('param . "OK")))
  (deferred:nextc it
    (lambda (buf)
      (insert (with-current-buffer buf (buffer-string)))
      (kill-buffer buf))))


;; Parallel deferred

(deferred:$
  (deferred:parallel
    (lambda ()
      (deferred:url-retrieve "http://www.google.co.jp/intl/en_com/images/srpr/logo1w.png"))
    (lambda ()
      (deferred:url-retrieve "http://www.google.co.jp/images/srpr/nav_logo14.png")))
  (deferred:nextc it
    (lambda (buffers)
      (cl-loop for i in buffers
               do
               (insert
                (format
                 "size: %s\n"
                 (with-current-buffer i (length (buffer-string)))))
               (kill-buffer i)))))

;; Get an image by wget and resize by ImageMagick

(deferred:$

  ;; try
  (deferred:$
    (deferred:process "wget" "-O" "a.jpg" "http://www.gnu.org/software/emacs/tour/images/splash.png")
    (deferred:nextc it
      (lambda () (deferred:process "convert" "a.jpg" "-resize" "100x100" "jpg:b.jpg")))
    (deferred:nextc it
      (lambda ()
        (clear-image-cache)
        (insert-image (create-image (expand-file-name "b.jpg") 'jpeg nil)))))

  ;; catch
  (deferred:error it ;
    (lambda (err)
      (insert "Can not get a image! : " err)))

  ;; finally
  (deferred:nextc it
    (lambda ()
      (deferred:parallel
        (lambda () (delete-file "a.jpg"))
        (lambda () (delete-file "b.jpg")))))
  (deferred:nextc it
    (lambda (x) (message ">> %s" x))))


;; Timeout Process

(deferred:$
  (deferred:earlier
    (deferred:process "sh" "-c" "sleep 3 | echo 'hello!'")
    (deferred:$
      (deferred:wait 1000) ; timeout msec
      (deferred:nextc it (lambda () "canceled!"))))
  (deferred:nextc it
    (lambda (x) (insert x))))


;; Loop and animation

(let ((count 0) (anm "-/|\\-")
      (end 50) (pos (point))
      (wait-time 50))
  (deferred:$
    (deferred:next
      (lambda (_) (message "Animation started.")))

    (deferred:nextc it
      (deferred:lambda (_)
        (save-excursion
          (when (< 0 count)
            (goto-char pos) (delete-char 1))
          (insert (char-to-string
                   (aref anm (% count (length anm))))))
        (if (> end (cl-incf count))
            (deferred:nextc (deferred:wait wait-time) self))))

    (deferred:nextc it
      (lambda (_)
        (save-excursion
          (goto-char pos) (delete-char 1))
        (message "Animation finished.")))))
