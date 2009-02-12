;;;_ * circe

(autoload 'circe "circe" "Connect to an IRC server" t)

(setq circe-default-realname "http://www.newartisans.com/"
      circe-server-coding-system '(utf-8 . undecided)
      circe-server-auto-join-channels '(("^freenode$" "#ledger")))

(setq lui-max-buffer-size 30000
      lui-flyspell-p nil
      lui-flyspell-alist '(("." "american")))

(eval-after-load "circe"
  '(progn
     (require 'circe-highlight-all-nicks)
     (enable-circe-highlight-all-nicks)

     (add-to-list 'circe-receive-message-functions 'nickserv-auth)))

(eval-after-load "lui"
  '(progn
     (require 'lui-irc-colors)
     (add-to-list 'lui-pre-output-hook 'lui-irc-colors)
     (add-to-list 'lui-post-output-hook 'lui-hide-joins-and-quits)
     (add-to-list 'lui-post-output-hook 'circe-thou-art-but-a-fool-sir)))

(defun lui-hide-joins-and-quits ()
  "Mark joins and quits with the `fool' property.
This is an appropriate function for `lui-pre-output-hook'."
  (goto-char (point-min))
  (let ((inhibit-read-only t))
    (while (re-search-forward "^\\*\\*\\* \\(Join\\|Quit\\|Part\\|Nick change\\)" nil t)
      (let ((start (match-beginning 0)))
	(save-excursion
	  (goto-char start)
	  (forward-line 1)
	  (while (and (not (eobp)) (looking-at "    "))
	    (forward-line 1))
	  (delete-region start (point)))))))

(defcustom circe-fools-list nil
  "*List of nicks to mark as fools."
  :type '(repeat regexp)
  :group 'circe)

(defun circe-command-FOOL (line)
  "Add the regex on LINE to the `circe-fools-list'."
  (with-current-buffer (circe-server-last-active-buffer)
    (cond
     ((string-match "\\S-+" line)
      (let ((regex (match-string 0 line)))
        (add-to-list 'circe-fools-list regex)
        (circe-server-message
	 (format "Fools list, meet %s (for now)" regex))))
     ((not circe-fools-list)
      (circe-server-message "Your fools list is empty"))
     (t
      (circe-server-message "Your fools list:")
      (mapc (lambda (regex)
              (circe-server-message (format "- %s" regex)))
            circe-fools-list)))))

(defun circe-command-UNFOOL (line)
  "Remove an entry from `circe-fools-list'."
  (with-current-buffer (circe-server-last-active-buffer)
    (cond
     ((string-match "\\S-+" line)
      (let ((regex (match-string 0 line)))
        (setq circe-fools-list (delete regex circe-fools-list))
        (circe-server-message (format "Fools list forgot about %s" regex))))
     (t
      (circe-server-message
       "Who do you want to unfool? UNFOOL requires one argument")))))

(defun circe-thou-art-but-a-fool-sir ()
  (goto-char (point-min))
  (let ((inhibit-read-only t))
    (while (re-search-forward "^<\\([^>]+\\)>" nil t)
      (let ((start (match-beginning 0))
	    (nick (match-string 1))
	    a-foolish-boy-p)
	(if (dolist (regex circe-fools-list)
	      (if (string-match regex nick)
		  (return t)))
	    (save-excursion
	      (goto-char start)
	      (forward-line 1)
	      (while (and (not (eobp)) (looking-at " "))
		(forward-line 1))
	      (put-text-property start (point) 'lui-fool t)))))))

(defun nickserv-auth (nick user host command args)
  "Authenticate to a bitlbee server."
  (when (and (string= command "JOIN")
             (circe-server-my-nick-p nick))
    (with-circe-server-buffer
      (when (string= circe-server-network "irc.freenode.net")
        (circe-server-send "PRIVMSG NickServ IDENTIFY xco8imer")))))

(defun irc ()
  "Connect to IRC."
  (interactive)
  (circe "irc.freenode.net" "6667" "freenode"))

;_ * csharp-mode

(autoload 'csharp-mode "csharp-mode" nil t)

(add-to-list 'auto-mode-alist '("\\.cs\\'" . csharp-mode))

(defun my-csharp-mode-hook ()
  (set (make-local-variable 'parens-require-spaces) nil)
  (setq tab-width 8 c-basic-offset 2)
  (setq fill-column (- (window-width) 8)))

(add-hook 'csharp-mode-hook 'my-csharp-mode-hook)

(eval-after-load "whitespace"
  '(add-to-list 'whitespace-modes 'csharp-mode))

(add-to-list 'auto-mode-alist '("\\.as[cphma]x\\'" . html-mode))
(add-to-list 'auto-mode-alist '("\\.master\\'" . html-mode))
(add-to-list 'auto-mode-alist '("\\.css\\'" . css-mode))

