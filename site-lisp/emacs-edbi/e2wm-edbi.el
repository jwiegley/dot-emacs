(require 'edbi)

;;; edbi / DB perspective
;;;--------------------------------------------------

(defvar e2wm:c-edbi-recipe
  '(| (:left-max-size 40) database
      (- (:upper-size-ratio 0.3)
         editor result)))

(defvar e2wm:c-edbi-winfo
  '((:name database)
    (:name editor)
    (:name result)))

(e2wm:pst-class-register 
  (make-e2wm:$pst-class
   :name   'edbi
   :title  "DB"
   :init   'e2wm:dp-edbi-init
   :start  'e2wm:dp-edbi-start
   :leave  'e2wm:dp-edbi-leave
   :main   'editor
   :switch 'e2wm:dp-edbi-switch
   :popup  'e2wm:dp-edbi-popup
   :keymap 'e2wm:dp-edbi-minor-mode-map))

(defun e2wm:dp-edbi-init ()
  (let* 
      ((edbi-wm 
        (wlf:no-layout e2wm:c-edbi-recipe e2wm:c-edbi-winfo)))
    edbi-wm))

(defun e2wm:dp-edbi-start (wm)
  (let ((dbview-buf (get-buffer edbi:dbview-buffer-name)))
    (cond
     ((null dbview-buf)
      (e2wm:pst-buffer-set 'database e2wm:c-blank-buffer)
      (wlf:hide wm 'editor)
      (e2wm:pst-buffer-set 'result (edbi:open-db-viewer) t t))
     (t
      (e2wm:dp-edbi-show-buffers wm dbview-buf)
      (wlf:select wm 'database)))))

(defun e2wm:dp-edbi-leave (wm)
  (setq e2wm:prev-selected-buffer nil))

(defun e2wm:dp-edbi-show-buffers (wm dbview-buf)
  (let* ((conn (buffer-local-value 'edbi:connection dbview-buf))
         (editor-buf (edbi:dbview-query-editor-open conn))
         (result-buf (edbi:dbview-query-result-get-buffer editor-buf)))
  (e2wm:pst-buffer-set 'editor editor-buf t)
  (e2wm:pst-buffer-set 'result result-buf t)
  (e2wm:pst-buffer-set 'database dbview-buf t)))

(defun e2wm:dp-edbi-switch (buf)
  (e2wm:message "#DP EDBI switch : %s" buf)
  (let ((buf-name (buffer-name buf))
        (wm (e2wm:pst-get-wm)))
    (cond
     ((equal buf-name edbi:dialog-buffer-name)
      (set-window-buffer (wlf:get-window wm 'result) buf) t)
     ((eq (buffer-local-value 'major-mode buf) 'edbi:sql-mode)
      (e2wm:pst-buffer-set 'editor buf t t) t)
     ((equal buf-name edbi:dbview-buffer-name)
      (e2wm:pst-buffer-set 'database buf t t) t)
     (t 
      (e2wm:dp-edbi-popup-result buf) t))))

(defun e2wm:dp-edbi-popup (buf)
  (let ((cb (current-buffer)))
    (e2wm:message "#DP EDBI popup : %s (current %s / backup %s)"
                  buf cb e2wm:override-window-cfg-backup))
  (let ((buf-name (buffer-name buf))
        (wm (e2wm:pst-get-wm)))
    (cond
     ((equal buf-name edbi:dialog-buffer-name)
      (set-window-buffer (wlf:get-window wm 'result) buf) t)
     ((equal buf-name edbi:dbview-buffer-name)
      (e2wm:dp-edbi-show-buffers wm buf) t)
     ((and e2wm:override-window-cfg-backup
           (eq (selected-window) (wlf:get-window wm 'result)))
      (setq e2wm:override-window-cfg-backup nil)
      (set-window-buffer (wlf:get-window wm 'editor) buf)
      t)
     (t (e2wm:dp-edbi-popup-result buf) t))))

(defun e2wm:dp-edbi-popup-result (buf)
  (let ((wm (e2wm:pst-get-wm))
        (not-minibufp (= 0 (minibuffer-depth))))
    (e2wm:with-advice
     (e2wm:pst-buffer-set 'result buf t not-minibufp))))

;; Commands / Keybindings

(defun e2wm:dp-edbi ()
  (interactive)
  (e2wm:pst-change 'edbi))

(defun e2wm:dp-edbi-database-toggle-command ()
  (interactive)
  (wlf:toggle (e2wm:pst-get-wm) 'database)
  (e2wm:pst-update-windows))
(defun e2wm:dp-edbi-result-toggle-command ()
  (interactive)
  (wlf:toggle (e2wm:pst-get-wm) 'result)
  (e2wm:pst-update-windows))
(defun e2wm:dp-edbi-navi-editor-command ()
  (interactive)
  (wlf:select (e2wm:pst-get-wm) 'editor))
(defun e2wm:dp-edbi-navi-result-command ()
  (interactive)
  (wlf:select (e2wm:pst-get-wm) 'result))
(defun e2wm:dp-edbi-editor-maximize-toggle-command ()
  (interactive)
  (wlf:toggle-maximize (e2wm:pst-get-wm) 'editor))
(defun e2wm:dp-edbi-result-maximize-toggle-command ()
  (interactive)
  (wlf:toggle-maximize (e2wm:pst-get-wm) 'result))

(defvar e2wm:dp-edbi-minor-mode-map 
      (e2wm:define-keymap
       '(("prefix D" . e2wm:dp-edbi-database-toggle-command)
         ("prefix S" . e2wm:dp-edbi-result-toggle-command)
         ("prefix E" . e2wm:dp-edbi-editor-maximize-toggle-command)
         ("prefix R" . e2wm:dp-edbi-result-maximize-toggle-command))
       e2wm:prefix-key))

;; Bind [Super-d]
(global-set-key (kbd "s-d") 'e2wm:dp-edbi)
(global-set-key (kbd "M-s-d") 'e2wm:dp-edbi)
