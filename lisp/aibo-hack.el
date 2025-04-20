;;; aibo-hack.el --- InPlace Diff -*- lexical-binding: t; -*-

(require 'cl-lib)
(require 'cl-macs)

(defun gptel-aibo--summon-apply
    (point insertion &optional nearby-modification next-predicts)
  "Apply INSERTION and NEARBY-MODIFICATION at POINT."
  (let* ((buffer (current-buffer))
         (insertion-diff-parts
          (gptel-aibo--extract-diff-lines (car insertion) (cdr insertion)))
         (insertion-diff-lines (car insertion-diff-parts))
         (insertion-diff-offsets (cadr insertion-diff-parts))
         (nearby-diff-parts
          (when nearby-modification
            (gptel-aibo--extract-diff-lines
             (car nearby-modification) (cdr nearby-modification))))
         (nearby-diff-lines
          (when nearby-diff-parts (car nearby-diff-parts)))
         (nearby-diff-offsets
          (when nearby-diff-parts (cadr nearby-diff-parts)))
         (insertion-diffs nil)
         (nearby-modification-diffs nil)
         (insertion-ready nil)
         (modification-ready nil))

    (cl-flet
        ((maybe-apply-diffs ()
           (when (and insertion-ready
                      (or (not nearby-modification) modification-ready))
             (with-current-buffer buffer
               (gptel-aibo--summon-apply-with-diffs
                point
                (list (car insertion)
                      insertion-diff-offsets
                      insertion-diff-lines
                      insertion-diffs)
                (when nearby-modification
                  (list (car nearby-modification)
                        nearby-diff-offsets
                        nearby-diff-lines
                        nearby-modification-diffs))
                next-predicts)))))

      (gptel-aibo--inplace-diff
       (car insertion-diff-lines)
       (cdr insertion-diff-lines)
       (lambda (diffs)
         (setq insertion-diffs diffs
               insertion-ready t)
         (maybe-apply-diffs)))

      (when nearby-modification
        (gptel-aibo--inplace-diff
         (car nearby-diff-lines)
         (cdr nearby-diff-lines)
         (lambda (diffs)
           (setq nearby-modification-diffs diffs
                 modification-ready t)
           (maybe-apply-diffs)))))))

(provide 'aibo-hack)
