(require 'magit)
(require 'magithub-issue)

(defcustom magithub-hub-executable "hub"
  "The hub executable used by Magithub."
  :group 'magithub
  :package-version '(magithub . "0.1")
  :type 'string)

(defmacro magithub-with-hub (&rest body)
  `(let ((magit-git-executable magithub-hub-executable)
         (magit-pre-call-git-hook nil)
         (magit-git-global-arguments nil))
     ,@body))

;;;###autoload
(defun magithub-pull-request-merge (pull-request &optional args)
  "Merge PULL-REQUEST with ARGS.
See `magithub-pull-request--completing-read'.  If point is on a
pull-request object, that object is selected by default."
  (interactive (list (magithub-issue-completing-read-pull-requests)
                     (magit-am-arguments)))
  (unless (executable-find magithub-hub-executable)
    (user-error "This hasn't been supported in elisp yet; please install/configure `hub'"))
  (unless (member pull-request (magithub-pull-requests))
    (user-error "Unknown pull request %S" pull-request))
  (let-alist pull-request
    (magithub-with-hub
     (magit-run-git-sequencer "am" args .html_url))
    (message "#%d has been applied" .number)))

(provide 'magithub-issue-tricks)
