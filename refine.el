;;; refine.el --- interactive value editing         -*- lexical-binding: t; -*-

;; TODO: prompt the user to choose between local and global variables

;; Copyright (C) 2016-2017

;; Author: Wilfred Hughes <me@wilfred.me.uk>
;; Version: 0.4
;; Keywords: convenience
;; Package-Requires: ((emacs "24.3") (s "1.11.0") (dash "2.12.0") (list-utils "0.4.4") (loop "1.2"))

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

;; refine provides an interactive UI for manipulating lists.

;;; Code:

(require 's)
(require 'dash)
(require 'cl-lib) ;; cl-prettyprint, cl-incf, cl-decf
(require 'list-utils)
(require 'loop)
(eval-when-compile
  (require 'cl-macs)) ;; cl-assert

(defun refine--variables ()
  "Return a list of all symbols that are variables."
  (let (symbols)
    (mapatoms (lambda (symbol)
                (when (boundp symbol)
                  (push symbol symbols))))
    symbols))

(defun refine--custom-values (const-spec)
  "Given a list of (const ...) items from a `defcustom' spec,
 return the possible values."
  ;; E.g. (const :tag "Cider" cider) => 'cider
  (->> const-spec
       (--filter (consp it))
       (--filter (eq (-first-item it) 'const))
       (-map #'-last-item)))

(defun refine--possible-elements (symbol)
  "Return a list of the possible list elements SYMBOL can have.
Returns nil if SYMBOL is not a custom variable or if we can't
make useful suggestions."
  (when (custom-variable-p symbol)
    (let ((custom-type (get symbol 'custom-type))
          choices)
      (when (consp custom-type)
        ;; If custom-type takes the form '(repeat (choice (...)))
        (-when-let ((repeat-sym (choice-sym . repeated-choices)) custom-type)
          (when (and (eq repeat-sym 'repeat) (eq choice-sym 'choice))
            (setq choices repeated-choices)))
        ;; If custom-type takes the form '(set (...))
        (-when-let ((set-sym . set-choices) custom-type)
          (when (eq set-sym 'set)
            (setq choices set-choices))))
      (when choices
        (refine--custom-values choices)))))

(defun refine--possible-values (symbol)
  "Return a list of the possible values SYMBOL can have.
Returns nil if SYMBOL is not a custom variable."
  (when (custom-variable-p symbol)
    (let ((custom-type (get symbol 'custom-type)))
      ;; If custom-type takes the form '(choice (...))) or '(radio (...))
      (when (consp custom-type)
        (-let [(kind . choices) custom-type]
          (when (or (eq kind 'choice) (eq kind 'radio))
            (refine--custom-values choices)))))))

(defun refine--pretty-format (value)
  "Pretty print VALUE as a string."
  (let ((cl-formatted (with-temp-buffer
                        (cl-prettyprint value)
                        (s-trim (buffer-string)))))
    (cond ((stringp value)
           ;; We want propertized text, shown with the double-quotes,
           ;; and subsequent lines indented so they line up under the ".
           (let* ((escaped-quotes (s-replace "\"" "\\\"" value))
                  (lines (s-lines escaped-quotes))
                  (indented-lines (--map-indexed
                                   (if (zerop it-index)
                                       it
                                     (format " %s" it))
                                   lines)))
             (format "\"%s\"" (s-join "\n" indented-lines))))
          ;; Print nil and t as-is.
          ((or (eq t value) (eq nil value))
           (format "%s" value))
          ;; Print :foo symbols as-is.
          ((and (symbolp value) (s-prefix? ":" (symbol-name value)))
           (format "%s" value))
          ;; Display other symbols, and lists, with a quote, so we
          ;; show usable syntax.
          ((or (symbolp value) (consp value))
           (format "'%s" cl-formatted))
          (t
           cl-formatted))))

(defface refine-index-face
  '((((class color) (background light))
     :foreground "grey50")
    (((class color) (background dark))
     :foreground "grey50"))
  "Face for metadata in refine results buffers."
  :group 'refine)

(defun refine--vector->list (vector)
  "Shallow conversion from a vector to a list."
  (mapcar #'identity vector))

(defun refine--prefix-lines (prefix string)
  "Return STRING with PREFIX prepended on the first line.
If STRING contains multiple lines, indent subsequent lines
to preserve vertical indentation."
  (let* ((raw-lines (s-lines string))
         ;; Whitespace of the same length as PREFIX.
         (leading-whitespace (make-string (length prefix) ?\ ))
         ;; Append a prefix to each line.
         (prefixes
          (cons prefix
                (-repeat (1- (length raw-lines)) leading-whitespace)))
         (lines (--zip-with (concat it other) prefixes raw-lines)))
    (s-join "\n" lines)))

(defun refine--format-element (element index-string)
  "Given ELEMENT, an item from a list, and INDEX-STRING,
a string marking our position in the containing list/vector,
return a pretty, propertized string."
  (let* (;; Pretty print ELEMENT.
         (formatted-element (refine--pretty-format element))
         ;; Style the index.
         (propertized-index (propertize index-string 'face 'refine-index-face)))
    (refine--prefix-lines
     (concat propertized-index " ") formatted-element)))

(defun refine--format-with-index (value)
  "Given an elisp VALUE, return a pretty propertized
string listing the elements.

VALUE may be a list, string, vector or symbol.

If VALUE is a list or vector, show each list item along with its
index."
  (cond
   ((vectorp value)
    ;; TODO: this prints 'nil' for empty vectors
    (refine--format-with-index (refine--vector->list value)))

   ((null value)
    (propertize "nil" 'refine-index 'empty))

   ;; Scalar values are values that we treat as a single item.
   ((or (symbolp value) (stringp value) (numberp value))
    (propertize (refine--pretty-format value) 'refine-index 'scalar))

   ((refine--dotted-pair-p value)
    (format "%s\n%s"
            (refine--format-element (car value) "CAR")
            (refine--format-element (cdr value) "CDR")))

   (t
    (let* ((index-digits-required
            (if (null value) 0 (ceiling (log (safe-length value) 10))))
           ;; If there are 10 or more items, make sure we print the
           ;; index with a width of 2, and so on.
           (index-format-string (concat "%" (format "%s" index-digits-required) "d"))
           ;; Pretty-print each element, along with an index.
           (formatted-elements
            (--map-indexed
             (refine--format-element it (format index-format-string it-index))
             value))
           ;; Propertize each element, so we can work out which element
           ;; point is on.
           (propertized-elements
            (--map-indexed (propertize it 'refine-index it-index)
                           formatted-elements)))
      (s-join "\n" propertized-elements)))))

(define-button-type 'refine-buffer-button
  'action 'refine--switch-to-buffer
  'follow-link t
  'help-echo "Switch to this buffer")

(defun refine--switch-to-buffer (button)
  (switch-to-buffer (button-get button 'buffer)))

(defun refine--buffer-button (buffer)
  "Return a button that switches to BUFFER.."
  (with-temp-buffer
    (insert-text-button
     (buffer-name buffer)
     :type 'refine-buffer-button
     'buffer buffer)
    (buffer-string)))

(define-button-type 'refine-help-button
  'action 'refine--open-help
  'follow-link t
  'help-echo "View in *Help* buffer")

(defun refine--open-help (button)
  (describe-variable (button-get button 'symbol)))

(defun refine--help-button (symbol)
  "Return a button that opens a help buffer for SYMBOL."
  (with-temp-buffer
    (insert-text-button
     "Help"
     :type 'refine-help-button
     'symbol symbol)
    (buffer-string)))

(define-button-type 'refine-definition-button
  'action 'refine--go-to-definition
  'follow-link t
  'help-echo "Go to definition")

(defun refine--go-to-definition (button)
  (find-variable (button-get button 'symbol)))

(defun refine--definition-button (symbol)
  "Return a button that navigates to the definition of SYMBOL."
  (with-temp-buffer
    (insert-text-button
     "Definition"
     :type 'refine-definition-button
     'symbol symbol)
    (buffer-string)))

(defun refine--update (result-buffer target-buffer symbol)
  "Update RESULT-BUFFER with the current value of SYMBOL in TARGET-BUFFER."
  (let (value)
    (when (boundp symbol)
      (with-current-buffer target-buffer
        (setq value (symbol-value symbol))))
    (with-current-buffer result-buffer
      (let* ((current-line (line-number-at-pos))
             (current-column (current-column))
             buffer-read-only)
        (erase-buffer)
        (insert (format "%s\n\n" (refine--describe symbol value target-buffer)))
        (when (boundp symbol)
          (insert (refine--format-with-index value))
          (insert "\n\n")
          (insert (refine--help-button symbol) " " (refine--definition-button symbol)))
        ;; We can't use `save-excursion' because we erased the whole
        ;; buffer. Go back to the previous position.
        (goto-char (point-min))
        (forward-line (1- current-line))
        (forward-char current-column)))))

(defvar-local refine--symbol nil
  "The symbol being inspected in the current buffer.")

(defvar-local refine--target-buffer nil
  "When inspecting buffer-local variable, use this buffer.")

(defun refine-update ()
  "Update the current refine buffer."
  (interactive)
  (unless (eq major-mode #'refine-mode)
    (user-error "refine-update must be run in a refine buffer"))
  (refine--update (current-buffer) refine--target-buffer refine--symbol))

(defun refine--insert-list (list index value)
  "Insert VALUE at INDEX in LIST.
This mutates the list."
  ;; We can't handle empty lists: there's no cons cell to mutate.
  (assert (consp list))

  (if (= index (length list))
      ;; We're appending to the list.
      (progn
        ;; Find the last cons cell.
        (setq list (last list))
        ;; Append the value requested.
        (setcdr list (cons value nil)))
    ;; Otherwise, insert in-place.
    (progn
      ;; Walk down the list until we're one element away from our
      ;; target.
      (setq list (nthcdr index list))
      ;; Mutate this cons cell.
      (-let [(old-car . old-cdr) list]
        (setcar list value)
        (setcdr list (cons old-car old-cdr))))))

(defun refine--insert (symbol index value)
  "Insert VALUE at INDEX in list variable SYMBOL.
This mutates the list.

If SYMBOL is nil, assigns to SYMBOL instead."
  (interactive)
  (assert (symbolp symbol))
  (let* ((list (symbol-value symbol))
         (length (safe-length list)))
    (assert (or (consp list) (null list)))
    (cond
     ;; If list is nil, we can't modify destructively.
     ((= length 0) (set symbol (list value)))

     (t
      (assert (>= length index))
      (refine--insert-list list index value)))))

(defun refine--vector-pop (symbol index)
  "Remove the item at INDEX from vector variable SYMBOL.

This creates a new vector and assigns it to SYMBOL. Vectors have
fixed length, see *info* (elisp) Arrays."
  (let* ((vector (symbol-value symbol))
         (length (length vector)))
    (assert (and (vectorp vector) (< index length)))

    (let* ((all-items (refine--vector->list vector))
           (items (--reject (= it-index index) all-items)))
      (set symbol (apply #'vector items)))))


(defun refine--list-pop (list index)
  "Remove the item at INDEX from LIST.
This mutates the list."
  (let* ((length (safe-length list)))
    (assert (and (consp list) (> length 1) (< index length)))

    (if (equal index (1- length))
        ;; We're popping the very last cons cell.
        (progn
          (setq list (nthcdr (1- index) list))
          (setcdr list nil))
      (progn
        ;; Walk down the list until we're one element away from our
        ;; target.
        (setq list (nthcdr index list))
        
        ;; Mutate this cons cell to skip over the popped item and point
        ;; directly at the next cell.
        (-let [(_ new-car . new-cdr) list]
          (setcar list new-car)
          (setcdr list new-cdr))))))

(defun refine--pop (symbol index)
  "Remote the item at INDEX in vectory/list variable SYMBOL.
Mutates the value where possible."
  (let ((value (symbol-value symbol)))
    (cond ((vectorp value)
           (refine--vector-pop symbol index))
          ((equal (length value) 1)
           ;; We can't pop from a one-element list in-place, because a
           ;; cons cell requires a non-empty list.
           (set symbol nil))
          (t 
           (refine--list-pop value index)))))

(defun refine--index-at-point ()
  "Get the index of the list item at point."
  (save-excursion
    (when (eolp)
      (backward-char 1))
    (get-text-property (point) 'refine-index)))

(defun refine--read-eval-expr (prompt &optional initial-contents)
  "Read a lisp expression from the minibuffer and evaluate it.
Equivalent to interactive \"X\"."
  (eval (read--expression prompt initial-contents)))

(defun refine--read-element (symbol prompt &optional initial-contents)
  "Read a new value for a list element of SYMBOL."
  (let ((possibilities (refine--possible-elements symbol)))
    (if possibilities
        (eval (read (completing-read prompt (-map #'refine--pretty-format possibilities))))
      (refine--read-eval-expr prompt initial-contents))))

(defun refine-delete ()
  "Remove the current list item at point."
  (interactive)
  (-when-let (list-index (refine--index-at-point))
    (refine--pop refine--symbol list-index)
    (refine-update)))

;; TODO: inserts should support vectors too.
(defun refine-insert (value)
  "Insert a new item before the list item at point."
  (interactive
   (let ((index (refine--index-at-point)))
     (if index
         (list (refine--read-element
                refine--symbol
                (format "Value to insert at %s: "
                        (if (numberp index) index 0))))
       (user-error "No value here"))))
  (let ((index (refine--index-at-point)))
    (unless (numberp index)
      (setq index 0))
    (refine--insert refine--symbol index value)
    (refine-update)
    (refine--goto index)))

(defun refine-insert-after (value)
  "Insert a new item before the list item at point."
  (interactive
   (let ((index (refine--index-at-point)))
     (if index
         (list (refine--read-eval-expr
                (format "Value to insert at %s: " (1+ (refine--index-at-point)))))
       (user-error "No value here"))))
  (-when-let (list-index (refine--index-at-point))
    (refine--insert refine--symbol (1+ list-index) value)
    (refine-update))
  (refine-next 1))

(defun refine--swap (value index1 index2)
  "Switch the items at INDEX1 and INDEX2 in list VALUE."
  (let* ((index1-element (nth index1 value))
         (index2-element (nth index2 value)))
    (setf (nth index2 value) index1-element)
    (setf (nth index1 value) index2-element)))

(defun refine-move-forward (arg)
  "Move the current item one position forward.
When called with a prefix, move that many positions."
  (interactive "p")
  ;; Move the element.
  (let ((index (refine--index-at-point)))
    (if (numberp index)
        (refine--move-element (symbol-value refine--symbol) index arg)
      (user-error "No list element here")))
  (refine-update)
  ;; Move point to match.
  (refine-next arg))

(defun refine-move-backward (arg)
  "Move the current item one position forward.
When called with a prefix, move that many positions."
  (interactive "p")
  (refine-move-forward (- arg)))

;; TODO: extract all these internal manipulation functions to a
;; separate package.
(defun refine--move-element (value index distance)
  "Move the element at INDEX by DISTANCE positions in list VALUE.
If DISTANCE is too big, move it as far as possible."
  (let* ((target-index-raw (+ index distance))
         ;; Ensure 0 <= target-index <= length - 1
         (target-index (max (min target-index-raw (1- (length value))) 0)))
    (loop-until (equal index target-index)
      (if (> distance 0)
          ;; Moving forwards
          (progn
            (refine--swap value index (1+ index))
            (cl-incf index))
        ;; Moving backwards
        (progn
          (refine--swap value index (1- index))
          (cl-decf index))))))

(defun refine--move-point (distance)
  "Move point DISTANCE items forward.
If DISTANCE is negative, move backwards."
  (let* ((value (symbol-value refine--symbol)))
    ;; If we're dealing with a scalar or the empty list, just move to
    ;; the line where it's shown.
    (if (not (consp value))
        (progn
          (goto-char (point-min))
          (loop-until (not (null (refine--index-at-point)))
            (forward-line 1)))
      ;; Otherwise, we have a non-empty list.
      (let* ( ;; Work out which list index to go to.
             (current-index (or (refine--index-at-point) -1))
             (requested-index (+ current-index distance))
             ;; Ensure we don't try to go outside the range allowed for
             ;; this list.
             (length (safe-length value))
             (target-index (max 0 (min requested-index (1- length)))))
        (beginning-of-line)
        (if (> distance 0)
            ;; Go forwards until we're on the first line of the requested value.
            (loop-until (or (eq (refine--index-at-point) 'empty)
                            (equal (refine--index-at-point) target-index))
              (forward-line 1))
          ;; Go backwards until we're on the first line of the requested
          ;; value, even if it has multiple lines.
          (progn
            ;; Go to last line of the target value.
            (loop-until (equal (refine--index-at-point) target-index)
              (forward-line -1))
            ;; Go past the target value.
            (while (equal (refine--index-at-point) target-index)
              (forward-line -1))
            ;; Move back to the first line of this value.
            (forward-line 1)))))))

;; TODO: it would be nice for variables like `racer-cmd' (custom
;; variables for file paths) to be editable here too.
(defun refine-edit (new-value)
  "Edit the current item in the list or vector."
  (interactive
   (let* ((lst (symbol-value refine--symbol))
          (index (refine--index-at-point))
          (prompt (format "Set value at %s: " index))
          (current-value (elt lst index)))
     (list (refine--read-element refine--symbol prompt
                                 (refine--pretty-format current-value)))))
  (setf (elt (symbol-value refine--symbol) (refine--index-at-point))
        new-value)
  (refine-update))

(defun refine-next (arg)
  "Move point to the next item.
With a numeric prefix, move that many items."
  (interactive "p")
  (refine--move-point arg))

(defun refine-previous (arg)
  "Move point to the previous item.
With a numeric prefix, move that many items."
  (interactive "p")
  (refine--move-point (- arg)))

;; TODO: can we write refine--move-point in terms of refine--goto?
(defun refine--goto (index)
  "Move point to list INDEX requested."
  (goto-char (point-min))
  (loop-until (or (eq (refine--index-at-point) 'empty)
                  (equal (refine--index-at-point) index))
    (forward-line 1)))

(defun refine--next-item (current items)
  "Given a list ITEMS, return the item after CURRENT.
If CURRENT is at the end, or not present, use the first item."
  (let ((index (or (-elem-index current items) -1)))
    (nth (1+ index) (-cycle items))))

(defun refine--buffer (symbol buffer)
  "Get or create a refine buffer for SYMBOL in BUFFER."
  (assert (symbolp symbol))
  (let ((result-buffer (get-buffer-create (format "*refine: %s*" symbol))))
    (with-current-buffer result-buffer
      ;; Need to set the major mode before we set local variables.
      (refine-mode)
      (setq-local refine--symbol symbol)
      (setq-local refine--target-buffer buffer))
    result-buffer))

;; TODO: replace calls with just list-utils-improper-p
(defun refine--dotted-pair-p (value)
  "Return t if VALUE is a dotted pair."
  (and (consp value)
       (not (consp (cdr value))) (not (null (cdr value)))))

(defun refine--local-values (symbol)
  "Return a list of pairs (buffer, value) for all buffers
where SYMBOL is set."
  (let (result)
    (dolist (buf (buffer-list) result)
      (when (local-variable-p symbol buf)
        (push (cons buf (buffer-local-value symbol buf))
              result)))))

;; TODO: support hash maps
(defun refine--describe (symbol value buffer)
  "Return a human-readable description for SYMBOL set to VALUE in BUFFER."
  (let* ((pretty-symbol
          (propertize (format "%s" symbol)
                      'face 'font-lock-variable-name-face))
         (is-local (local-variable-p symbol buffer))
         (symbol-description
          (cond
           ((not (boundp symbol))
            "an unbound symbol")
           (is-local
            (format "a local variable in buffer %s"
                    (refine--buffer-button buffer)))
           (t
            "a global variable")))
         (local-description
          (let ((locals (refine--local-values symbol)))
            (if locals
                (format " It has a buffer-local value in %d buffers."
                        (length locals))
              "")))
         (type-description
          (cond
           ((stringp value) "a string")
           ((null value) "nil")
           ((symbolp value) "a symbol")
           ((numberp value) "a number")
           ((and (consp value) (not (consp (cdr value))) (not (null (cdr value))))
            "a pair")
           ((and (consp value) (list-utils-cyclic-p value))
            "an improper list")
           ;; TODO: it would be nice to say 'a list of symbols' etc
           ;; when all the elements are the same type.
           ((sequencep value)
            (let* ((type (if (vectorp value) "vector" "list"))
                   (length (length value))
                   (units (if (= length 1) "value" "values")))
              (format "a %s containing %d %s"
                      type length units)))
           (:else "an unsupported type")))
         (value-intro
          (if is-local
              (format "local value in buffer %s"
                      (refine--buffer-button buffer))
            "current value"))
         (value-description
          (if (boundp symbol)
              (format " Its %s is %s:"
                      value-intro type-description)
            "")))
    (s-word-wrap
     70
     (format "%s is %s.%s"
             pretty-symbol symbol-description value-description))))

;; TODO: add demo in readme of this command.
(defun refine-cycle ()
  "Cycle the variable or list element through all possible values.
For booleans, toggle nil/t."
  (interactive)
  (let ((value (symbol-value refine--symbol))
        (index (refine--index-at-point))
        (possible-values (refine--possible-values refine--symbol)))
    (cond
     ;; If we're on a list element of a `defcustom', try to cycle
     ;; the element.
     ((and (custom-variable-p refine--symbol) (consp value))
      (unless index
        (user-error "No list element at point"))
      ;; Find the values that an element can take.
      (let ((possible-elements (refine--possible-elements refine--symbol))
            (element-value (nth index value)))
        (if possible-elements
            ;; Set this element to the next possible value.
            (setf (nth index value) (refine--next-item element-value possible-elements))
          (user-error "I don't know what values elements of '%s can take" refine--symbol))))
     ;; For other `defcustom' values, cycle the whole variable.
     ((and (custom-variable-p refine--symbol) possible-values)
      ;; Set to the next value.
      (set refine--symbol (refine--next-item value possible-values)))
     ;; Toggle booleans.
     ((null value)
      (set refine--symbol t))
     ((eq value t)
      (set refine--symbol nil))
     ;; Otherwise, we don't know what to do.
     (t
      (user-error "I don't know what values '%s can take" refine--symbol)))
    (refine-update)))

;;;###autoload
(defun refine (symbol)
  "Interactively edit the value of a symbol \(usually a list\)."
  (interactive (list (read (completing-read "Variable: " (refine--variables)
                                            nil nil nil nil
                                            (-if-let (variable (variable-at-point))
                                                (and (symbolp variable) (symbol-name variable)))))))
  (let* ((results-buffer (refine--buffer symbol (current-buffer))))
    (refine--update results-buffer (current-buffer) symbol)
    (switch-to-buffer results-buffer)
    (goto-char (point-min))))

(define-derived-mode refine-mode fundamental-mode "Refine"
  "A major mode for interactively editing elisp values."
  (setq buffer-read-only t))

;; TODO: add a magit-style popup.

;; Buffer-level operations.
(define-key refine-mode-map (kbd "q") #'kill-this-buffer)
(define-key refine-mode-map (kbd "g") #'refine-update)

;; Modifying the list.
(define-key refine-mode-map (kbd "e") #'refine-edit)
(define-key refine-mode-map (kbd "RET") #'refine-edit)

(define-key refine-mode-map (kbd "c") #'refine-cycle)
;; another mnemonic for cycling is toggling, when the current value is a boolean.
(define-key refine-mode-map (kbd "t") #'refine-cycle)

(define-key refine-mode-map (kbd "k") #'refine-delete)
(define-key refine-mode-map (kbd "a") #'refine-insert-after)
(define-key refine-mode-map (kbd "i") #'refine-insert)
;; Provide keybindings familiar to lispy users, as well as to move-dup users.
(define-key refine-mode-map (kbd "<M-down>") #'refine-move-forward)
(define-key refine-mode-map (kbd "s") #'refine-move-forward)
(define-key refine-mode-map (kbd "<M-up>") #'refine-move-backward)
(define-key refine-mode-map (kbd "w") #'refine-move-backward)

;; Moving around.
(define-key refine-mode-map (kbd "n") #'refine-next)
(define-key refine-mode-map (kbd "p") #'refine-previous)

(provide 'refine)
;;; refine.el ends here
