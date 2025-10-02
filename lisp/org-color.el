;;; org-color --- Function for colorizing text using links -*- lexical-binding: t -*-

;;; Commentary:

;;; Code:

(require 's)
(require 'term/tty-colors)

(defun color-fg-comp (&optional _arg)
  "Completion function for color links.

Displays the *Colors* buffer, extracts available color names, prompts
user to select one via completion, and returns a formatted \"fg:COLOR\"
string suitable for org-mode link insertion.

ARG is currently unused but reserved for future extensibility."
  (let ((color-fg-data
         (prog2
             (save-selected-window
               (list-colors-display))
             (with-current-buffer (get-buffer "*Colors*")
               (mapcar (lambda (line)
                         (append (list line)
                                 (s-split " " line t)))
                       (s-split "\n" (buffer-string))))
           (kill-buffer "*Colors*"))))
    (format "fg:%s"
            (s-trim (cadr (assoc (completing-read "Color: " color-fg-data)
                                 color-fg-data))))))

(defun color-fg-link-face (path)
  "Return a face property list to set foreground color to PATH.

PATH should be a valid color name or hex color string recognized by
Emacs. This function is intended for use as the :face property in
`org-link-parameters'.

Returns a plist of the form (:foreground COLOR)."
  `(:foreground ,path))

(defun color-fg-link-export (path description backend)
  "Export color link with PATH and optional DESCRIPTION for BACKEND.

PATH is the color name from the link.
DESCRIPTION is the optional link description text.
BACKEND is the export backend symbol (e.g., \\='html).

For HTML export, converts color names to RGB format and wraps content in
a span with inline color styling. Returns nil for unsupported backends."
  (cond
   ((eq backend 'html)
    (let ((rgb (assoc (downcase path) color-name-rgb-alist))
          r g b)
      (setq r (* 255 (/ (nth 1 rgb) 65535.0))
            g (* 255 (/ (nth 2 rgb) 65535.0))
            b (* 255 (/ (nth 3 rgb) 65535.0)))
      (format "<span style=\"color: rgb(%s,%s,%s)\">%s</span>"
              (truncate r) (truncate g) (truncate b)
              (or description path))))))

(org-link-set-parameters "fg"
                         :face 'color-fg-link-face
                         :complete 'color-fg-comp
                         :export 'color-fg-link-export)

(defun color-bg-comp (&optional _arg)
  "Completion function for background color links.

Prompts user to select a color name from the list of available colors.
ARG is unused but accepted for compatibility with completion frameworks.

Returns a formatted \"fg:COLOR\" link string with the selected color name."
  (let ((color-bg-data
         (prog2
             (save-selected-window
               (list-colors-display))
             (with-current-buffer (get-buffer "*Colors*")
               (mapcar (lambda (line)
                         (append (list line)
                                 (s-split " " line t)))
                       (s-split "\n" (buffer-string))))
           (kill-buffer "*Colors*"))))
    (format "fg:%s"
            (s-trim (cadr (assoc (completing-read "Color: " color-bg-data)
                                 color-bg-data))))))

(defun color-bg-link-face (path)
  "Face function for background color links.

PATH is the color name to use as the background color.

Returns a face property list with :background set to PATH."
  `(:background ,path))

(defun color-bg-link-export (path description backend)
  "Export function for background color links.

PATH is the color name from the link.
DESCRIPTION is the optional link description text.
BACKEND is the export backend symbol.

For HTML export, converts the named color to RGB format and wraps the
text in a span with inline color styling."
  (cond
   ((eq backend 'html)
    (let ((rgb (assoc (downcase path) color-name-rgb-alist))
          r g b)
      (setq r (* 255 (/ (nth 1 rgb) 65535.0))
            g (* 255 (/ (nth 2 rgb) 65535.0))
            b (* 255 (/ (nth 3 rgb) 65535.0)))
      (format "<span style=\"color: rgb(%s,%s,%s)\">%s</span>"
              (truncate r) (truncate g) (truncate b)
              (or description path))))))

(org-link-set-parameters "bg"
                         :face 'color-bg-link-face
                         :complete 'color-bg-comp
                         :export 'color-bg-link-export)

(provide 'org-color)

;;; org-color.el ends here
