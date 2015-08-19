;;; erc-image.el --- Show received image urls in the ERC buffer

;; Copyright (C) 2012  Jon de Andrés Frías
;; Copyright (C) 2012  Raimon Grau Cuscó
;; Copyright (C) 2012  David Vázquez

;; Author: Jon de Andrés Frías <jondeandres@gmail.com>
;;         Raimon Grau Cuscó <raimonster@gmail.com>
;; Version: 0.9
;; Package-Requires: ((erc "5.3"))
;; Keywords: multimedia

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:
;;
;; Show inlined images (png/jpg/gif/svg) in erc buffers.  Requires
;; Emacs 24.2
;;
;; (require 'erc-image)
;; (add-to-list 'erc-modules 'image)
;; (erc-update-modules)
;;
;; Or `(require 'erc-image)` and  `M-x customize-option erc-modules RET`
;;
;; This plugin subscribes to hooks `erc-insert-modify-hook' and
;; `erc-send-modify-hook' to download and show images.  In this early
;; version it's doing this synchronously.
;;
;; The function used to display the image is bound to the variable
;; `erc-image-display-func'. There are two possible values for that,
;; `erc-image-insert-inline' and `erc-image-insert-other-buffer'.
;;
;;
;;; Code:


(require 'erc)
(require 'url-queue)
(require 'image-dired)

(defgroup erc-image nil
  "Enable image."
  :group 'erc)

(defcustom erc-image-regex-alist '(("http://\\(www\\.\\)?imgur\\.com" . erc-image-get-imgur-url)
				   ("http://\\(www\\.\\)?memecaptain\\.com/gend_image_pages/" .
				    erc-image-get-memecaptain-url)
				   ("http://\\(www\\.\\)?memecrunch\\.com/meme/[^.]*$" .
				    erc-image-get-memecrunch-url)
				   ("http://\\(www\\.\\)?quickmeme.com/meme/[^.]*$" .
				    erc-image-get-quickmeme-url)
                                   ("\\.\\(png\\|jpg\\|jpeg\\|gif\\|svg\\)$" . identity))
  "Pairs of regex and function to match URLs to be downloaded.
The function needs to have one argument to which the url will be
supplied and it should return the real URL to download an image.
If several regex match prior occurring have higher priority."
  :group 'erc-image
  :type '(alist :key-type string :value-type function))

(defcustom erc-image-images-path temporary-file-directory
  "Path where to store downloaded images."
  :group 'erc-image)

(defcustom erc-image-display-func 'erc-image-insert-inline
  "Function to use to display the image."
  :group 'erc-image
  :type '(choice (const :tag "Inline" 'erc-image-insert-inline)
                 (const :tag "Other buffer" 'erc-image-insert-other-buffer)
                 function))

(defcustom erc-image-inline-rescale-to-window t
  "Rescale to window height or width (whatever is smaller) if the
image is bigger than the window."
  :group 'erc-image
  :type 'boolean)

(defun erc-image-insert-other-buffer (status file-name marker)
  "Open a new buffer and display file-name image there, scaled."
  (goto-char (point-min))
  (search-forward "\n\n")
  (write-region (point) (point-max) file-name)
  (image-dired-create-display-image-buffer)
  (display-buffer image-dired-display-image-buffer)
  (image-dired-display-image file-name))

(defun erc-image-insert-inline (status file-name marker)
  "Open file-name image in the marker position."
  (goto-char (point-min))
  (search-forward "\n\n")
  (write-region (point) (point-max) file-name)
  (with-current-buffer (marker-buffer marker)
    (save-excursion
      (let ((inhibit-read-only t)
	    (im (erc-image-create-image file-name)))
	(goto-char (marker-position marker))
	(insert-before-markers
	 (propertize " " 'display im)
	 "\n")
	(when (image-animated-p im) (image-animate im 0 t))
	(put-text-property (point-min) (point-max) 'read-only t)))))

(defun erc-image-create-image (file-name)
  "Create an image suitably scaled for the current window if
`ERC-IMAGE-INLINE-RESCALE-TO-WINDOW' is non-nil."
  (let* ((positions (window-inside-absolute-pixel-edges))
         (width (- (nth 2 positions) (nth 0 positions)))
         (height (- (nth 3 positions) (nth 1 positions)))
         (image (create-image file-name))
         (dimensions (image-size image t)))
    (if (and (fboundp 'imagemagick-types) erc-image-inline-rescale-to-window
             (not (image-animated-p image))
           (or (> (car dimensions) width)
               (> (cdr dimensions) height)))
        (if (> width height)
            (create-image file-name 'imagemagick nil :height height)
          (create-image file-name 'imagemagick nil :width width))
      image)))

;(image-dired-display-image FILE &optional ORIGINAL-SIZE)

(defun erc-image-show-url-image ()
  (goto-char (point-min))
  (search-forward "http" nil t)
  (let ((url (thing-at-point 'url)))
    (when url
      (let ((file-name (expand-file-name (md5 url) erc-image-images-path))
            (dl (erc-image-extract-image-url url)))
        (when dl
          (goto-char (point-max))
          (url-queue-retrieve dl
                              erc-image-display-func
                              (list
                               file-name
                               (point-marker))
                              t))))))

(defun erc-image-extract-image-url (url)
  "Extract the download url using the RE and functions in
`erc-image-regex-alist'."
  (catch 'download-url
    (dolist (pair erc-image-regex-alist)
      (let ((re (car pair))
            (f (cdr pair)))
        (when (string-match-p re url)
          (throw 'download-url (funcall f url)))))))

(defun erc-image-get-imgur-url (url)
  "Return the download URL for the imgur `url'."
  (let ((id (progn (string-match "/\\([^/]*?\\)$" url)
                   (match-string 1 url))))
     (format "http://imgur.com/download/%s" id)))

(defun erc-image-get-memecrunch-url (url)
  "Return the download URL for the memecrunch `url'."
  (let ((id (progn (string-match "memecrunch.com/meme/\\(.*?\\)$" url)
                   (match-string 1 url))))
     (format "http://memecrunch.com/meme/%s/image.png" id)))

(defun erc-image-get-memecaptain-url (url)
  "Return the download URL for the memecaptain `url'."
  (let ((id (progn (string-match "/\\([^/]*?\\)$" url)
                   (match-string 1 url))))
     (format "http://memecaptain.com/gend_images/%s" id)))

(defun erc-image-get-quickmeme-url (url)
  "Return the download URL for the quickmeme `url'."
  (let ((id (progn (string-match "quickmeme.com/meme/\\(.*?\\)/*$" url)
                   (match-string 1 url))))
     (format "http://i.qkme.me/%s.jpg" id)))

;;;###autoload
(eval-after-load 'erc
  '(define-erc-module image nil
     "Display inlined images in ERC buffer"
     ((add-hook 'erc-insert-modify-hook 'erc-image-show-url-image t)
      (add-hook 'erc-send-modify-hook 'erc-image-show-url-image t))
     ((remove-hook 'erc-insert-modify-hook 'erc-image-show-url-image)
      (remove-hook 'erc-send-modify-hook 'erc-image-show-url-image))
     t))

(provide 'erc-image)
;;; erc-image.el ends here
