;; Define the format conversion going to and from Org mode/OPML.
;;
;; Change "~/src/org-opml/opml2org.py" to wherever that file is located.
(add-to-list 'format-alist '(opml "Outline Processor Markup Language"
                                  "<[?]xml version=\"1.0\"[^>]*[?]>[\n]?.*[\n]?.*[\n]?<opml version=\"[1|2].0\">"
                                  "~/src/org-opml/opml2org.py" opml-encode t))

;; If it ends with .opml, use `opml-encode' when saving.
(defun set-buffer-file-format-to-opml ()
  "Set buffer-file-format to '(opml) when visiting an .opml file.

This is needed as otherwise newly created .opml files wouldn't
know to pass their contents through `opml-encode' because they
don't yet contain the `format-alist' regexp pattern."
  (when (string-match "\.opml$" (buffer-file-name))
    (setq buffer-file-format '(opml))))

;; Run the above function each time Emacs opens a file.
(add-hook 'find-file-hooks 'set-buffer-file-format-to-opml)

;; Activate org-mode when opening OPML files.
(add-to-list 'auto-mode-alist '("\\.opml$" . org-mode))

;; Load the OPML export backend.
(load-library "ox-opml")

;; The function called when converting from Org mode to OPML.
(defun opml-encode (begin end buffer)
  "Export Org mode buffer to OPML."
  (let ((org-export-show-temporary-export-buffer nil)
        (name "*OPML Export Buffer*"))
    (org-export-to-buffer 'opml name)
    (erase-buffer)
    (insert-buffer-substring (get-buffer name))
    (point-max)))
