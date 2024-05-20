(require 's)

(defun color-fg-comp (&optional arg)
  "Completion function for color links."
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
  "Face function for color links."
  `(:foreground ,path))

(defun color-fg-link-export (path description backend)
  "Export function for color links."
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

(defun color-bg-comp (&optional arg)
  "Completion function for color links."
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
  "Face function for color links."
  `(:background ,path))

(defun color-bg-link-export (path description backend)
  "Export function for color links."
  (cond
   ((eq backend 'html)
    (let ((rgb (assoc (downcase path) color-bg-name-rgb-alist))
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
