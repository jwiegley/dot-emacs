;;; -*- lexical-binding: t -*-

;;; Code:

;;;; Requirements

(require 'helm-org-rifle)

;;;; Helper functions

(defun helm-org-rifle--test-helper-process-candidates (candidates)
  "Remove text properties and convert buffers to buffer names in CANDIDATES."
  (->> candidates
       (helm-org-rifle--test-helper-remove-properties-from-candidates)
       (helm-org-rifle--test-helper-convert-buffers-to-buffer-names-in-candidates)))

(defun helm-org-rifle--test-helper-remove-properties-from-candidates (candidates)
  "Remove text properties from CANDIDATES display values.
Since the properties could vary from one user to another
depending on settings, active packages, etc, we should remove
them."
  (cl-loop for entry in candidates
           do (setf (car entry) (substring-no-properties (car entry)))
           finally return candidates))

(defun helm-org-rifle--test-helper-convert-buffers-to-buffer-names-in-candidates (candidates)
  "Convert buffer objects to buffer names in CANDIDATES."
  ;; FIXME: Is there a way to represent buffer objects directly to
  ;; avoid having to do this?
  (cl-loop for (display . real) in candidates
           do (setf (car real) (buffer-name (car real)))
           finally return candidates))

;;;; Tests

(describe "helm-org-rifle"

  (before-all
    ;; TODO: Make sure customizable options are set uniformly, here and/or in the steps
    ;; TODO: Use assess's buffer-related functions to do this more cleanly

    ;; (setq test-buffer (or (find-buffer-visiting "data.org") (find-file-noselect "data.org")))
    (setq test-buffer (find-file-noselect (concat default-directory "test/data.org"))))

  (before-each
    ;; Set options consistently
    ;; TODO: Can we get these defaults from the other file?
    (setq helm-org-rifle-always-show-entry-contents-chars 50
          helm-org-rifle-before-command-hook '(helm-org-rifle-set-sort-mode)
          helm-org-rifle-after-command-hook '(helm-org-rifle-reset-sort-mode)
          helm-org-rifle-close-unopened-file-buffers t
          helm-org-rifle-context-characters 25
          helm-org-rifle-directories-recursive t
          helm-org-rifle-ellipsis-string "..."
          helm-org-rifle-ellipsis-face 'font-lock-comment-delimiter-face
          helm-org-rifle-directories-filename-regexp "\.org$"
          helm-org-rifle-fontify-headings t
          helm-org-rifle-heading-contents-separator "\n"
          helm-org-rifle-input-idle-delay 0.05
          helm-org-rifle-multiline t
          helm-org-rifle-show-entry-function 'helm-org-rifle-show-entry-in-real-buffer
          helm-org-rifle-show-full-contents nil
          helm-org-rifle-show-todo-keywords t
          helm-org-rifle-show-path nil
          helm-org-rifle-re-prefix "\\(\\_<\\|[[:punct:]]\\)"
          helm-org-rifle-re-suffix "\\(\\_>\\|[[:punct:]]\\)"
          helm-org-rifle-sort-order nil
          helm-org-rifle-unlinkify-entry-links t
          helm-org-rifle-sort-order-persist nil
          helm-org-rifle-occur-kill-empty-buffer t))

  (describe "helm-org-rifle--parse-input"
    (it "Can parse a string of search terms correctly"
      (expect (let ((org-todo-keywords-1 '("TODO" "DONE")))
                (helm-org-rifle--parse-input
                 "notatag :tag1:tag2: :tag3: notatageither !:excludedtagA: !:excludedtagB: !excludeA TODO DONE"))
              :to-equal '(("notatageither" "notatag")
                          ("excludeA")
                          ("tag1" "tag2" "tag3")
                          ("excludedtagA" "excludedtagB")
                          ("DONE" "TODO")))))

  (describe "helm-org-rifle--get-candidates-in-buffer"

    ;; FIXME: For some reason the REAL cons in (DISPLAY . REAL) gets
    ;; flattened into the parent cons.  The test works, but
    ;; I guess it's not exactly the same as the non-test, so
    ;; these tests should probably be fixed.

    (it "Can match against headings"
      (expect (helm-org-rifle--test-helper-process-candidates
               (helm-org-rifle--get-candidates-in-buffer test-buffer "berry"))
              :to-equal '(("**** Banana  
le fruit – botanically a berry^[1]^[2] – produced by se" "data.org" . 174)
                          ("**** Blueberry  
#+BEGIN_QUOTE
Blueberries are perennial floweri..." "data.org" . 1143)
                          ("**** Strawberry  
The garden strawberry (or simply strawberry; F...which is not a botanical berry, but an aggregate access...colates. Artificial strawberry flavorings and aromas ar" "data.org" . 1640))))

    (it "Can match against entry text"
      (expect (helm-org-rifle--test-helper-process-candidates
               (helm-org-rifle--get-candidates-in-buffer test-buffer "food"))
              :to-equal '(("* Food :food: 
" "data.org" . 2)
                          ("**** Strawberry  
resh or in such prepared foods as preserves, fruit jui" "data.org" . 1640)
                          ("**** Chicken :barbecue:fowl: 
primarily as a source of food, consuming both their me" "data.org" . 3114)
                          ("***** Fries  
he menus of diners, fast food restaurants, pubs, and b" "data.org" . 4375))))

    (it "Can match against multiple path elements"
      (expect (let ((helm-org-rifle-show-path t))
                (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "fresh meat")))
              :to-equal '(("Food/Ingredients/Meat/Pork
is the culinary name for meat from the domestic pig (S...e most commonly consumed meat worldwide, with evidence...0 BC. Pork is eaten both freshly cooked and preserved." "data.org" . 3541))))

    (describe "Can match against tags..."
      (it "...in any order"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer ":fowl:barbecue:"))
                :to-equal '(("**** Chicken :barbecue:fowl: 
#+BEGIN_QUOTE
The chicken (Gallus gallus domest..." "data.org" . 3114)))))

    (describe "Can negate matches..."
      (it "...on headings"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "meat !chicken"))
                :to-equal '(("*** Meat :meat: 
" "data.org" . 2400)
                            ("***** Brisket :barbecue: 
Brisket is a cut of meat from the breast or lower...tissue, so the resulting meat must be cooked correctly" "data.org" . 2488)
                            ("**** Pork  
is the culinary name for meat from the domestic pig (S...e most commonly consumed meat worldwide, with evidence" "data.org" . 3541)
                            ("***** Pulled pork :barbecue: 
erwise be a tough cut of meat is cooked slowly at low...mperatures, allowing the meat to become tender enough" "data.org" . 3942))))

      (it "...on entry text"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "fruit !edible"))
                :to-equal '(("*** Fruit :fruit: 
" "data.org" . 97)
                            ("**** Blueberry  
are the most common^[1] fruits sold as \"blueberries\" a" "data.org" . 1143)
                            ("**** Strawberry  
ivated worldwide for its fruit. The fruit (which is not...t an aggregate accessory fruit) is widely appreciated f...ared foods as preserves, fruit juice, pies, ice creams," "data.org" . 1640))))

      (it "...on tags in individual headings"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "meat !:fowl:"))
                :to-equal '(("*** Meat :meat: 
" "data.org" . 2400)
                            ("***** Brisket :barbecue: 
Brisket is a cut of meat from the breast or lower...tissue, so the resulting meat must be cooked correctly" "data.org" . 2488)
                            ("**** Pork  
is the culinary name for meat from the domestic pig (S...e most commonly consumed meat worldwide, with evidence" "data.org" . 3541) ("***** Pulled pork :barbecue: 
erwise be a tough cut of meat is cooked slowly at low...mperatures, allowing the meat to become tender enough" "data.org" . 3942)))))

    (describe "Can match against TODO keywords..."
      (it "...alone"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "DONE"))
                :to-equal '(("***** DONE  Tater tots  
#+BEGIN_QUOTE
Tater tots are pieces of deep-fri..." "data.org" . 5401))))

      (it "...with multiple keywords alone"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "DONE TODO"))
                :to-equal '(("***** DONE  Tater tots  
#+BEGIN_QUOTE
Tater tots are pieces of deep-fri..." "data.org" . 5401)
                            ("***** TODO  Potato pancakes  
est when they're not too done.  DONE, I say." "data.org" . 5725))))

      (it "...with a keyword and a normal term"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "DONE tots"))
                :to-equal '(("***** DONE  Tater tots  
Tater tots are pieces of deep-fried...crispy exterior. \"Tater Tots\" is a registered tradema" "data.org" . 5401))))

      (it "...with two keywords and a normal term"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "DONE TODO potato"))
                :to-equal '(("***** DONE  Tater tots  
es of deep-fried, grated potatoes served as a side dish." "data.org" . 5401)
                            ("***** TODO  Potato pancakes  
est when they're not too done.  DONE, I say." "data.org" . 5725))))

      (it "...with two keywords and two normal terms"
        (expect (helm-org-rifle--test-helper-process-candidates
                 (helm-org-rifle--get-candidates-in-buffer test-buffer "TODO DONE best pancakes"))
                :to-equal '(("***** TODO  Potato pancakes  
These are best when they're not too don...e.  DONE, I say." "data.org" . 5725)))))

    (it "Can match against priorities"
      (setq expected-result '(("***** [#B] Mashed potatoes  
#+BEGIN_QUOTE
Mashed potato (British English) o..." "data.org" . 5066)))
      (expect (helm-org-rifle--test-helper-process-candidates
               (helm-org-rifle--get-candidates-in-buffer test-buffer "[#B]"))
              :to-equal expected-result)
      (expect (helm-org-rifle--test-helper-process-candidates
               (helm-org-rifle--get-candidates-in-buffer test-buffer "#B"))
              :to-equal expected-result))))

;;;; Update-results functions

(defun helm-org-rifle--test-update-result ()
  "Update result in next `expect'.
If region is active, update all results in it.  Otherwise update
the next result after point."
  (interactive)
  (cl-labels ((update ()
                      (forward-sexp)
                      (eval-print-last-sexp)
                      (transpose-sexps 1)
                      (kill-sexp)
                      (backward-sexp)
                      (cycle-spacing -1)
                      (insert "'")
                      (indent-pp-sexp t)))
    (if (use-region-p)
        (while (re-search-forward "(expect" (region-end) t)
          (update))
      (re-search-forward "(expect" (region-end) t)
      (update))))

;;; Config

;; Remove `delete-trailing-whitespace' from local `before-save-hook',
;; because it breaks the strings in the tests

;; Local Variables:
;; eval: (when (memq 'delete-trailing-whitespace before-save-hook) (remove-hook 'before-save-hook 'delete-trailing-whitespace t))
;; End:
