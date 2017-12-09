(eval-when-compile (require 'cl))

(When "^I place the cursor after \"\\(.+\\)\"$"
      (lambda (arg)
        (goto-char (point-min))
        (let ((search (search-forward arg nil t))
              (message "Can not place cursor after '%s', because there is no such point: '%s'"))
          (assert search nil message arg (espuds-buffer-contents)))))

(When "^I place the cursor before \"\\(.+\\)\"$"
      (lambda (arg)
        (goto-char (point-max))
        (let ((search (search-backward arg nil t))
              (message "Can not place cursor before '%s', because there is no such point: '%s'"))
          (assert search nil message arg (espuds-buffer-contents)))))

(When "^I go to the \\(front\\|end\\) of the word \"\\(.+\\)\"$"
      (lambda (pos word)
        (goto-char (point-min))
        (let ((search (re-search-forward (format "%s" word) nil t))
              (message "Can not go to character '%s' since it does not exist in the current buffer: %s"))
          (assert search nil message word (espuds-buffer-contents))
          (if (string-equal "front" pos) (backward-word)))))

(When "^I edit the string at point$"
     (lambda ()
       (call-interactively 'string-edit-at-point)))
