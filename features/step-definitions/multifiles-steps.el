(Given "^I open and erase file \"\\(.+\\)\"$"
       (lambda (filename)
         (find-file filename)
         (kill-buffer)
         (find-file filename)))

(When "^I press \"\\(.+\\)\"$"
      (lambda (keybinding)
        (let ((macro (edmacro-parse-keys keybinding)))
          (if espuds-chain-active
              (setq espuds-action-chain (vconcat espuds-action-chain macro))
            (if (and (equal keybinding "C-g")
                     (eq (key-binding (kbd "C-g")) 'keyboard-quit))
                (espuds-quit)
              (execute-kbd-macro macro))))))

(When "^I go to character \"\\(.+\\)\"$"
      (lambda (char)
        (goto-char (point-min))
        (let ((search (re-search-forward (format "%s" char) nil t))
              (message "Can not go to character '%s' since it does not exist in the current buffer: %s"))
          (assert search nil message char (espuds-buffer-contents)))))

(When "^I go to the \\(front\\|end\\) of the word \"\\(.+\\)\"$"
      (lambda (pos word)
        (goto-char (point-min))
        (let ((search (re-search-forward (format "%s" word) nil t))
              (message "Can not go to character '%s' since it does not exist in the current buffer: %s"))
          (assert search nil message word (espuds-buffer-contents))
          (if (string-equal "front" pos) (backward-word)))))

(When "^I select the last \"\\(.+\\)\"$"
      (lambda (text)
        (goto-char (point-max))
        (let ((search (re-search-backward text nil t)))
          (assert search nil "The text '%s' was not found in the current buffer." text))
        (set-mark (point))
        (re-search-forward text)))

(Then "^the major-mode should be \"\\(.+\\)\"$"
      (lambda (mode)
        (assert (string= (symbol-name major-mode) mode) nil
                "The major mode should be %s but was %S." mode major-mode)))

(Then "^the buffer should be saved$"
       (lambda ()
         (assert (not (buffer-modified-p)) nil
                 "The buffer should be saved, but was modified.")))
