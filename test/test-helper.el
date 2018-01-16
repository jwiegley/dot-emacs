;;; test-helper.el --- Tests for emojify              -*- lexical-binding: t; -*-

;;; Commentary:
;;; Helpers to write tests for emojify

;;; Code:

;; Setup load-path, some of this is redundant when tests are run from the
;; command line
(let ((project-dir (locate-dominating-file (or (buffer-file-name) load-file-name)
                                           ".cask")))
  (if (not project-dir)
      (user-error "Could not locate project root")
    (let ((default-directory (expand-file-name (format ".cask/%d.%d"
                                                       emacs-major-version
                                                       emacs-minor-version)
                                               project-dir)))
      (normal-top-level-add-subdirs-to-load-path))

    (add-to-list 'load-path project-dir)))

;; Libs required for tests
(require 'ert)
(require 'el-mock)
(eval-when-compile
  (require 'cl))
(require 'cl-lib)
(require 'noflet)

(when (require 'undercover nil t)
  (undercover "*.el"))

;; Load emojify
(require 'emojify)

;; Define custom emoji config
(defvar emojify-test-custom-emojis)
(let* ((project-dir (locate-dominating-file (or (buffer-file-name) load-file-name)
                                            ".cask"))
       (custom-emoji-dir (expand-file-name "test/assets/" project-dir)))
  (setq emojify-test-custom-emojis
        `((":troll:" . (("name" . "Troll") ("image" . ,(expand-file-name "trollface.png" custom-emoji-dir)) ("style" . "github")))
          (":neckbeard:" . (("name" . "Neckbeard") ("image" . ,(expand-file-name "neckbeard.png" custom-emoji-dir)) ("style" . "github")))
          ("λ" .  (("name" . "Lambda") ("image" . ,(expand-file-name "lambda.png" custom-emoji-dir)) ("style" . "unicode"))))))

;; Helper macros for tests
(defmacro emojify-tests-with-saved-customizations (&rest forms)
  "Run FORMS saving current customizations and restoring them on completion.

Helps isolate tests from each other's customizations."
  (declare (indent 0))
  `(let ((emojify-saved-emoji-json emojify-emoji-json)
         (emojify-saved-user-emojis emojify-user-emojis)
         (emojify-saved-user-emojis-parsed emojify--user-emojis)
         (emojify-saved-emojify-regexps emojify-regexps)
         (emojify-saved-display-style emojify-display-style)
         (emojify-saved-inhibit-major-modes emojify-inhibit-major-modes)
         (emojify-saved-inhibit-in-buffer-functions emojify-inhibit-in-buffer-functions)
         (emojify-saved-emoji-style emojify-emoji-styles)
         (emojify-saved-program-contexts emojify-program-contexts)
         (emojify-saved-inhibit-functions emojify-inhibit-functions)
         (emojify-saved-point-entered-behaviour emojify-point-entered-behaviour)
         (emojify-saved-show-help emojify-show-help)
         (emojify-saved-reveal-on-isearch emojify-reveal-on-isearch)
         (emojify-saved-composed-text-p emojify-composed-text-p))
     (unwind-protect
         (progn
           (unless (file-exists-p (emojify-image-dir))
             (emojify-download-emoji emojify-emoji-set))
           (emojify-debug-mode +1)
           (setq emojify-composed-text-p nil)
           ,@forms)
       (setq emojify-emoji-json emojify-saved-emoji-json
             emojify-display-style emojify-saved-display-style
             emojify-inhibit-major-modes emojify-saved-inhibit-major-modes
             emojify-user-emojis emojify-saved-user-emojis
             emojify--user-emojis emojify-saved-user-emojis-parsed
             emojify-regexps emojify-saved-emojify-regexps
             emojify-inhibit-in-buffer-functions emojify-saved-inhibit-in-buffer-functions
             emojify-program-contexts emojify-saved-program-contexts
             emojify-inhibit-functions emojify-saved-inhibit-functions
             emojify-point-entered-behaviour emojify-saved-point-entered-behaviour
             emojify-show-help emojify-saved-show-help
             emojify-reveal-on-isearch emojify-saved-reveal-on-isearch
             emojify-composed-text-p emojify-saved-composed-text-p)
       (emojify-set-emoji-styles emojify-saved-emoji-style))))

(defmacro emojify-tests-with-emojified-buffer (str &rest forms)
  "Create a buffer with STR and execute FORMS.

The FORMS are executed with emojify enabled."
  (declare (indent 1))
  ;; Run tests in a new buffer
  `(let ((test-buffer (get-buffer-create " *emojify-test-buffer*")))
     (noflet ((emojify-buffer-p (buffer)
                                (or (string-match-p "^ \\*emojify-test-buffer\\*" (buffer-name buffer))
                                    (funcall this-fn buffer))))
       (unwind-protect
           (save-window-excursion
             (switch-to-buffer test-buffer)
             ;; Rename it uniquely so that subsequent buffers do not conflict with it
             (rename-uniquely)
             ;; Save all possible customizations
             (emojify-tests-with-saved-customizations
               (setq emojify-point-entered-behaviour nil)
               (insert ,str)
               (emojify-mode +1)
               ;; Force refontification since JIT does it lazily
               (emojify-display-emojis-in-region (point-min) (point-max))
               (goto-char (point-min))
               ,@forms))
         ;; Keep the buffer around for interactive tests, helps debugging failing
         ;; tests
         (when noninteractive
           (kill-buffer test-buffer))))))

(defmacro emojify-tests-with-emojified-static-buffer (str &rest forms)
  "Create a buffer with STR and execute FORMS.

All kinds of dynamic behaviour on buffer are disabled.  See
`emojify-with-saved-buffer-state'"
  (declare (indent 1))
  `(emojify-tests-with-emojified-buffer ,str
     (emojify-with-saved-buffer-state
       ,@forms)))

(defun emojify-tests-should-be-emojified (point)
  "Assert there is an emoji at POINT."
  (should (get-text-property point 'emojified))
  (should (get-text-property point 'emojify-display))
  (should (get-text-property point 'emojify-buffer))
  (should (get-text-property point 'emojify-beginning))
  (should (get-text-property point 'emojify-end))
  (should (get-text-property point 'emojify-text))
  (should (get-text-property point 'display)))

(defun emojify-tests-should-not-be-emojified (point)
  "Assert there is not emoji at POINT."
  (should-not (get-text-property point 'emojified))
  (should-not (get-text-property point 'emojify-display))
  (should-not (get-text-property point 'emojify-buffer))
  (should-not (get-text-property point 'emojify-beginning))
  (should-not (get-text-property point 'emojify-end))
  (should-not (get-text-property point 'emojify-text))
  (should-not (get-text-property point 'display)))

(defun emojify-tests-should-be-uncovered (point)
  "Assert the emoji at POINT is uncovered."
  (should (get-text-property point 'emojified))
  (should (get-text-property point 'emojify-buffer))
  (should (get-text-property point 'emojify-beginning))
  (should (get-text-property point 'emojify-end))
  (should (get-text-property point 'emojify-text))
  (should-not (get-text-property point 'display)))

;;; test-helper.el ends here
