;; a minor mode for Haskell refactoring
;
; (generated automatically, manual edits may be lost)
;
;  put this file in your Emacs load-path, and add something 
;  like this to your .emacs (the hook assumes that you're 
;  using haskell-mode, and always want to enable the refactoring
;  minor mode when entering haskell-mode):
;
;   (autoload 'haskell-refac-mode "haskell-refac"
;      "Minor mode for refactoring Haskell programs" t)
;   (add-hook 'haskell-mode-hook 'haskell-refac-mode)
;

;; menu silently disappears if this defvar is moved after define-minor-mode..
(defvar haskell-refac-mode-map (make-sparse-keymap "Refactor"))
(define-minor-mode haskell-refac-mode
  "Toggle Haskell Refactoring mode.
   With no argument, this command toggles the mode. 
   Non-null prefix argument turns on the mode.
   Null prefix argument turns off the mode.

   When Haskell Refactoring mode is enabled, the \"Refactor\"
   menu provides access to a list of refactorings. These are
   implemented as commands of an external refactoring tool
   (default hare, see option haskell-refac-refactorer).
   "
  ;; The initial value.
  nil
  ;; The indicator for the mode line.
  " HaRe 0.6.0.1 "
  ;; The minor mode bindings.
  nil
)

;;JP: Quick & dirty: add hooks for the mode we are defining...
;; Alternative is not to use define-minor-mode
(add-hook 'haskell-refac-mode-on-hook 'turn-on-haskell-refac)
(add-hook 'haskell-refac-mode-off-hook 'turn-off-haskell-refac)

;;JP: moved to top
(defvar haskell-refac-output-marker (make-marker))
(defvar haskell-refac-buffer-list nil)

(defgroup haskell-refac nil "Haskell refactoring options")

(defcustom haskell-refac-refactorer "hare"
	"*Path to Haskell refactoring tool"
	:type 'file
	:group 'haskell-refac)

(defcustom haskell-refac-chasePaths (cons (expand-file-name ".") '("HaskellLibraries"))
	"*List of directories to chase for missing files (including Prelude!)"
	:type '(repeat directory)
	:group 'haskell-refac)

;;JP: easy-menu should work with Emacs too
(easy-menu-define
 haskell-refac-menu
 haskell-refac-mode-map
 "Haskell refactorer minor mode menu"
 '("Refactor"


("Projects"
   ["New project" haskell-refac-new  :active t]
   ["Add file" haskell-refac-add  :active t]
   ["Chase imports" haskell-refac-chase  :active t]
   ["List files" haskell-refac-files  :active t]
)

("Names/Scopes"
   ["Rename" haskell-refac-rename  :active t]
   ["Lift def to top level" haskell-refac-liftToTopLevel  :active t]
   ["Lift def one level" haskell-refac-liftOneLevel  :active t]
   ["Demote def" haskell-refac-demote  :active t]
   ["Create Type Signatures" haskell-refac-refacTypeSig  :active t]
   ["ReadFile" haskell-refac-parseAnswers  :active t]
   ["Convert Let to Where" haskell-refac-letToWhere  :active t]
   ["Convert Where to Let" haskell-refac-whereToLet  :active t]
   ["Introduce patterns over an argument position" haskell-refac-introPattern  :active t]
   ["Introduce case analysis" haskell-refac-introCase  :active t]
   ["Fold term against pattern variable" haskell-refac-foldPattern  :active t]
)

("Slicing"
   ["Remove redundant declarations" haskell-refac-refacRedunDec  :active t]
   ["Slicing based on a subexpression" haskell-refac-refacSlicing  :active t]
   ["Slicing a tuple" haskell-refac-refacSlicTuple  :active t]
   ["Merge definitions" haskell-refac-refacMerge  :active t]
   ["Add definition for merge" haskell-refac-refacCacheMerge  :active t]
   ["Instantiate a general pattern" haskell-refac-refacInstantiate  :active t]
)

("Fold/Unfold"
   ["Unfold def" haskell-refac-unfoldDef  :active t]
   ["Fold Definition" haskell-refac-subFunctionDef  :active t]
   ["Generative Fold of Definition" haskell-refac-genFold  :active t]
   ["Select an equation for generative fold" haskell-refac-genFoldCache  :active t]
   ["Convert pattern to use an as pattern" haskell-refac-refacAsPatterns  :active t]
   ["Unfold references to AS patterns" haskell-refac-refacUnfoldAsPatterns  :active t]
   ["Simplify Expression via Symbolic Evalutaion" haskell-refac-simplifyExpr  :active t]
)

("Definitions"
   ["Introduce new def" haskell-refac-introNewDef  :active t]
   ["Generalise def" haskell-refac-generaliseDef  :active t]
   ["Remove def" haskell-refac-removeDef  :active t]
   ["Duplicate def" haskell-refac-duplicateDef  :active t]
   ["Add one parameter" haskell-refac-addOneParameter  :active t]
   ["Rm one parameter" haskell-refac-rmOneParameter  :active t]
   ["Move def to another module" haskell-refac-moveDefBtwMod  :active t]
   ["Converts guards to an if then else" haskell-refac-guardToIte  :active t]
   ["Shortcut Deforestration" haskell-refac-deforest  :active t]
)

("Import/Export"
   ["Clean imports" haskell-refac-cleanImports  :active t]
   ["Make import explicit" haskell-refac-mkImpExplicit  :active t]
   ["Add to export" haskell-refac-addToExport  :active t]
   ["Remove from export" haskell-refac-rmFromExport  :active t]
)

("Data types"
   ["Add field labels" haskell-refac-addFieldLabels  :active t]
   ["Add discriminators" haskell-refac-addDiscriminators  :active t]
   ["Add constructors" haskell-refac-addConstructors  :active t]
   ["eliminate nested patterns" haskell-refac-elimNestedPatterns  :active t]
   ["eliminate patterns" haskell-refac-elimPatterns  :active t]
   ["Create an ADT module" haskell-refac-createADTMod  :active t]
   ["From concrete to abstract data type" haskell-refac-fromAlgebraicToADT  :active t]
   ["Add a new constructor to a data type" haskell-refac-refacAddCon  :active t]
   ["Remove a constructor from a data type" haskell-refac-refacRmCon  :active t]
   ["Remove a field from a data type" haskell-refac-refacRemoveField  :active t]
   ["Add a field to a data type" haskell-refac-refacAddField  :active t]
)

("Duplicate Code"
   ["Duplicate Code Analysis" haskell-refac-duplicateCode  :active t]
   ["Transform Duplicate Code" haskell-refac-goDup  :active t]
   
)

   ["undo" haskell-refac-undo  :active t]

   "-"
   ["Customize" (customize-group 'haskell-refac) t]
   ))

(defun turn-on-haskell-refac ()
  "Turn on Haskell Refactoring support"
  (interactive)

  (if (not (buffer-file-name))
    (message-box "Error: can only refactor if buffer is associated with file")

    (progn 
      ;; keep track of buffers involved in refactoring

      (add-to-list 'haskell-refac-buffer-list (buffer-name) )

      ;; key bindings and menu entries

      (easy-menu-add haskell-refac-menu)
      (hare-selection-init)

      ;; refactoring sub-process, only one, please

      (unless (get-process "haskell-refac-process")
        (start-process "haskell-refac-process" "*refac*"
            haskell-refac-refactorer "emacs")

        ; does this work on unix as well, or do we need to be os-specific?
        ;;JP: XEmacs doesn't know this
        ;;(set-process-coding-system (get-process "haskell-refac-process") 
        ;;                           'raw-text-dos 'raw-text-unix)

        (set-marker haskell-refac-output-marker 0 (get-buffer-create "*refac*"))

        (set-process-filter (get-process "haskell-refac-process") 
                            'haskell-refac-process-filter) ) ) )
)

(defun haskell-refac-process-filter (proc string)
     (let* ((refac-buffer (process-buffer proc)) 
            (refac-end-mark (process-mark proc))
            (refac-buffer-window (display-buffer refac-buffer))
            (modified nil))
       (with-current-buffer refac-buffer
           ;; Insert the text, advancing the process marker.
           (goto-char refac-end-mark)
           (insert string)
           (set-marker refac-end-mark (point))
           ;; has the refactorer changed files on disk?
           (save-excursion
               (goto-char (marker-position haskell-refac-output-marker))
               (let ((found nil))
                  (while (setq found (re-search-forward "^\\(message\\|modified\\): \\(.*\\)\n" nil t)) 
                    (progn
                      (let ((cmd (match-string 1)) (param (match-string 2)))
                       (goto-char found)
                       (set-marker haskell-refac-output-marker found)
                       (cond
                         ((string= cmd "modified") (setq modified (cons param modified)))
                         ((string= cmd "message")  (message-box param))
                         )
                      )
                     ) )
               )
           )
       )
       (save-selected-window 
         (select-window refac-buffer-window)
         (goto-char (marker-position refac-end-mark))
         (recenter -2))
       (dolist (f modified) 
         (let ((buffer (get-file-buffer f)))
           (if buffer (with-current-buffer buffer (revert-buffer nil t t))
             (message-box (format "modified unopened file: %s" f)))))
     )
)

(defun turn-off-haskell-refac ()
  "Turn off Haskell Refactoring support"
  (interactive)
  (delete (buffer-name) haskell-refac-buffer-list)
  (easy-menu-remove haskell-refac-menu)
  (if (null haskell-refac-buffer-list) 
    (set-process-filter (get-process "haskell-refac-process") nil)
    (kill-process "haskell-refac-process")
    (kill-buffer "*refac*")
  )
  )

;; try to provide command to call pfe with current
;; file name and position in file

(defun line-no ()
  "grmpff. does anyone understand count-lines?"
  (+ (if (eq 0 (current-column)) 1 0)
     (count-lines (point-min) (point)))
  )

(defun line-no-pos (pos)
  "grmpff. why no parameter to current-column?"
  (save-excursion
    (goto-char pos)
    (+ (if (eq 0 (current-column)) 1 0)
       (count-lines (point-min) (point))))
  )

(defun current-column-pos (pos)
  "grmpff. why no parameter to current-column?"
  (save-excursion
    (goto-char pos) (current-column))
  )


(defun haskell-refac-new ()
  "new"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "new " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-add ()
  "add"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "add " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-chase ()
  "chase"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "chase " (mapconcat 'identity (append 
		haskell-refac-chasePaths) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-files ()
  "files"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "files " (mapconcat 'identity (append ) " ")
         "\n"))
     )
  ) )



(defun haskell-refac-rename ( name1)
  "rename"
  (interactive "sNew name? \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "rename " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-liftToTopLevel ()
  "liftToTopLevel"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "liftToTopLevel " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-liftOneLevel ()
  "liftOneLevel"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "liftOneLevel " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-demote ()
  "demote"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "demote " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacTypeSig ()
  "refacTypeSig"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacTypeSig " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-parseAnswers ()
  "parseAnswers"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "parseAnswers " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-letToWhere ()
  "letToWhere"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "letToWhere " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-whereToLet ()
  "whereToLet"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "whereToLet " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-introPattern ()
  "introPattern"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "introPattern " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-introCase ()
  "introCase"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "introCase " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-foldPattern ( name1 start2 end2)
  "foldPattern"
  (interactive "sName of pattern variable: \nr")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "foldPattern " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no-pos start2))
		(number-to-string (+ 1 (current-column-pos start2)))
		(number-to-string (line-no-pos end2))
		(number-to-string (+ 1 (current-column-pos end2))))) " ")
         "\n"))
     )
  ) )



(defun haskell-refac-refacRedunDec ( start1 end1)
  "refacRedunDec"
  (interactive "r")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacRedunDec " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacSlicing ( start1 end1)
  "refacSlicing"
  (interactive "r")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacSlicing " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacSlicTuple ( name2)
  "refacSlicTuple"
  (interactive "sElements to slice: (A for all; (x,_x,_) for some): \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacSlicTuple " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))
		(list name2)) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacMerge ( name1)
  "refacMerge"
  (interactive "sName for new definition: \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacMerge " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacCacheMerge ()
  "refacCacheMerge"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacCacheMerge " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacInstantiate ( name2)
  "refacInstantiate"
  (interactive "spatterns: \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacInstantiate " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))
		(list name2)) " ")
         "\n"))
     )
  ) )



(defun haskell-refac-unfoldDef ()
  "unfoldDef"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "unfoldDef " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-subFunctionDef ( start1 end1)
  "subFunctionDef"
  (interactive "r")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "subFunctionDef " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-genFold ( start1 end1)
  "genFold"
  (interactive "r")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "genFold " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-genFoldCache ()
  "genFoldCache"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "genFoldCache " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacAsPatterns ( name1 start2 end2)
  "refacAsPatterns"
  (interactive "sName for Pattern: \nr")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacAsPatterns " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no-pos start2))
		(number-to-string (+ 1 (current-column-pos start2)))
		(number-to-string (line-no-pos end2))
		(number-to-string (+ 1 (current-column-pos end2))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacUnfoldAsPatterns ( start1 end1)
  "refacUnfoldAsPatterns"
  (interactive "r")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacUnfoldAsPatterns " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-simplifyExpr ( start1 end1)
  "simplifyExpr"
  (interactive "r")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "simplifyExpr " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))
     )
  ) )



(defun haskell-refac-introNewDef ( name1 start2 end2)
  "introNewDef"
  (interactive "sName for new definition? \nr")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "introNewDef " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no-pos start2))
		(number-to-string (+ 1 (current-column-pos start2)))
		(number-to-string (line-no-pos end2))
		(number-to-string (+ 1 (current-column-pos end2))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-generaliseDef ( name1 start2 end2)
  "generaliseDef"
  (interactive "sname of new parameter? \nr")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "generaliseDef " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no-pos start2))
		(number-to-string (+ 1 (current-column-pos start2)))
		(number-to-string (line-no-pos end2))
		(number-to-string (+ 1 (current-column-pos end2))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-removeDef ()
  "removeDef"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "removeDef " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-duplicateDef ( name1)
  "duplicateDef"
  (interactive "sName for duplicate? \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "duplicateDef " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-addOneParameter ( name1)
  "addOneParameter"
  (interactive "sname of new parameter? \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "addOneParameter " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-rmOneParameter ()
  "rmOneParameter"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "rmOneParameter " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-moveDefBtwMod ( name1)
  "moveDefBtwMod"
  (interactive "sname of the destination module? \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "moveDefBtwMod " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-guardToIte ()
  "guardToIte"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "guardToIte " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-deforest ()
  "deforest"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "deforest " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))) " ")
         "\n"))
     )
  ) )



(defun haskell-refac-cleanImports ()
  "cleanImports"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "cleanImports " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-mkImpExplicit ()
  "mkImpExplicit"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "mkImpExplicit " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-addToExport ()
  "addToExport"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "addToExport " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-rmFromExport ()
  "rmFromExport"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "rmFromExport " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )



(defun haskell-refac-addFieldLabels ()
  "addFieldLabels"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "addFieldLabels " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-addDiscriminators ()
  "addDiscriminators"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "addDiscriminators " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-addConstructors ()
  "addConstructors"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "addConstructors " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-elimNestedPatterns ()
  "elimNestedPatterns"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "elimNestedPatterns " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-elimPatterns ()
  "elimPatterns"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "elimPatterns " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-createADTMod ()
  "createADTMod"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "createADTMod " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-fromAlgebraicToADT ()
  "fromAlgebraicToADT"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "fromAlgebraicToADT " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacAddCon ( name1)
  "refacAddCon"
  (interactive "sEnter text for constructor and parameters: \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacAddCon " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacRmCon ()
  "refacRmCon"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacRmCon " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacRemoveField ( name1)
  "refacRemoveField"
  (interactive "sEnter position of field to be removed: \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacRemoveField " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacAddField ( name1)
  "refacAddField"
  (interactive "sType of Field : \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacAddField " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)
		(list (number-to-string (line-no)) (number-to-string (+ 1 (current-column))))) " ")
         "\n"))
     )
  ) )



(defun haskell-refac-duplicateCode ( name1)
  "duplicateCode"
  (interactive "sClone Token Size: \n")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "duplicateCode " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list name1)) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacDupTrans ( start1 end1)
  "refacDupTrans"
  (interactive "r")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacDupTrans " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))
     )
  ) )


(defun haskell-refac-refacIdentify ( start1 end1)
  "refacIdentify"
  (interactive "r")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacIdentify " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))
     )
  ) )



(defun haskell-refac-undo ()
  "undo"
  (interactive "")
  (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "undo " (mapconcat 'identity (append ) " ")
         "\n"))
     )
  ) )


; ----------------------------- Hare selection

(defun hare-selection-init ()
  (interactive)
  (define-minor-mode hare-selection-mode
    "Hare selection
     In selection buffer, use [tab] to jump to current entry,
     and [(control k)] to delete current entry.
    "
    nil
    " Hare selection "
    '(([tab] . hare-select-goto)
      ([(control k)] . hare-select-goto-delete)
      )
    )
  (with-current-buffer (get-buffer-create "*hare-selection*")
    (hare-selection-mode t)
    )
  (defvar hare-selection '())
  (easy-menu-change '("Refactor") "Selection"
    '(["Clear selection" hare-select-clear :active t]
      ["Add to selection" hare-select-add :active t]
      ["Delete from selection" hare-select-delete :active t]
      ["Show selection" hare-select-display :active t]
      ["Visit next entry" hare-select-goto-next :active t]
      ["Visit current entry" hare-select-goto :active t]
      ["Visit previous entry" hare-select-goto-previous :active t]
     )
    )
  )
(defun hare-select-clear()
  (interactive)
  (setq hare-selection '())
  (hare-select-update)
  )
(defun hare-select-add () 
  (interactive) 
  (setq hare-selection
        (append hare-selection
                `((,(point) ,(current-buffer) ,(thing-at-point 'line)))
                )
        )
  (hare-select-update)
  )
(defun hare-select-goto-delete ()
  (interactive)
  (hare-select-goto)
  (hare-select-delete)
  )
(defun hare-select-delete ()
  (interactive)
  (setq hare-selection 
	(hare-select-delete-aux `(,(point) ,(current-buffer)) hare-selection)
	)
  (hare-select-update)
  )
(defun hare-select-delete-aux (e l)
  (if (null l)
      l
      (let ((h (car l)) (r (cdr l)))
	(if (equal e `(,(nth 0 h) ,(nth 1 h)))
	  (hare-select-delete-aux e r)
	  (cons h (hare-select-delete-aux e r))
	  )
	)
      )
  )
(defun hare-select-update ()
  (interactive)
  (save-excursion
    (set-buffer (get-buffer-create "*hare-selection*"))
    (erase-buffer)
    (insert (mapconcat 'hare-select-get-line hare-selection ""))
    (delete-blank-lines)
    )
  )
(defun hare-select-display ()
  (interactive)
  (save-excursion
    (pop-to-buffer (get-buffer-create "*hare-selection*"))
    (erase-buffer)
    (insert (mapconcat 'hare-select-get-line hare-selection ""))
    (shrink-window-if-larger-than-buffer)
    )
  )
(defun hare-select-goto-next ()
  (interactive)
  (set-buffer (get-buffer-create "*hare-selection*"))
  (forward-line 1)
  (hare-select-goto)
  )
(defun hare-select-goto-previous ()
  (interactive)
  (set-buffer (get-buffer-create "*hare-selection*"))
  (forward-line -1)
  (hare-select-goto)
  )
(defun hare-select-goto ()
  (interactive)
  (set-buffer (get-buffer-create "*hare-selection*"))
  (let ((i (- (line-no-pos (point)) 1)))
    (message (concat (number-to-string i) (buffer-name (nth 1 (nth i hare-selection)))))
    (pop-to-buffer (nth 1 (nth i hare-selection)))
    (goto-char (nth 0 (nth i hare-selection)))
    )
  )
(defun hare-select-get-line (pos)
  (save-excursion
    (set-buffer (cadr pos))
    (goto-char (car pos))
    (concat 
	 "\"" (buffer-file-name (cadr pos)) "\" "
	 (number-to-string (line-no-pos (car pos))) " "
	 (number-to-string (current-column-pos (car pos))) " : "
	 (nth 2 pos)
	 )
    )
  )
(defun haskell-refac-goDup ( start1 end1)
  "clonesExtraction"
  (interactive "r")
  (progn 
   (let (modified)
     (dolist (b (buffer-list) modified)
       (let* ((n (buffer-name b)) (n1 (substring n 0 1)))
        (if (and (not (or (string= " " n1) (string= "*" n1))) (buffer-modified-p b))
          (setq modified (cons (buffer-name b) modified)))))
     (if modified (message-box (format "there are modified buffers: %s" modified))
       (process-send-string "haskell-refac-process" 
         (concat
         
         "refacIdentify " (mapconcat 'identity (append 
		(list (if (buffer-file-name) (buffer-file-name) "<missing filename>"))
		(list (number-to-string (line-no-pos start1))
		(number-to-string (+ 1 (current-column-pos start1)))
		(number-to-string (line-no-pos end1))
		(number-to-string (+ 1 (current-column-pos end1))))) " ")
         "\n"))

     )
  )
  (haskell-refac-parseAnswers2)
  
) )

(defun haskell-refac-parseAnswers2 ()
  "parseAnswers2"
  (interactive "") 
  (progn
    (process-send-string "haskell-refac-process" (concat
         "parseAnswers " (mapconcat 'identity (append 
		
		(list "")) " ")
         "\n"))
    (let ((F (read-from-minibuffer "Would you like to extract this expression?"))    )  
    (if (equal F  "q") 
         (process-send-string "haskell-refac-process" (concat
          "refacDupTrans " (mapconcat 'identity (append 
		  (list "")) " ")
         "\n"))
         (progn
          (process-send-string "haskell-refac-process" (concat
           "parseAnswers " (mapconcat 'identity (append 
		
		   (list F)) " ")
           "\n"))
           (haskell-refac-parseAnswers2)
           "\n")))
  )
) 
