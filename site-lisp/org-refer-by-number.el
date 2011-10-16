;;; org-refer-by-number.el --- Refer by number, where linking is not possible

;; Copyright (C) 2011
;;   Free Software Foundation, Inc.

;; Author: Marc-Oliver Ihm
;; Keywords: Org-mode, references
;; Version: 0.99

;;; License:

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs; see the file COPYING.  If not, write to the
;; Free Software Foundation, Inc., 51 Franklin Street, Fifth Floor,
;; Boston, MA 02110-1301, USA.

;;; Commentary:

;; Purpose:
;;
;;  Refer to things by number, when direct links are not possible. This is done by
;;  keeping a table with increasing numbers in the first column and a timestamp in the
;;  second.
;;
;;  These numbers may then be used to refer to things outside of Org (e.g. you may write
;;  them on a piece of paper or use them as part of a directory name). Within Org you may
;;  then refer to these things by their number (e.g. "R277").
;;
;;
;; Setup:
;;
;;  (require 'org-refer-by-number)
;;  (setq org-refer-by-number-id "7f480c3e-312f-4b9b-b833-6a7a253d1404")
;;  (global-set-key (kbd "C-c C-x r") 'org-refer-by-number)
;;
;; Further reading:
;;
;;  Setup: See the variable `org-refer-by-number-id'
;;  Usage: See the function `org-refer-by-number'

;;

;;; Code:

(require 'org-table)

(defvar org-refer-by-number-id nil 
  "Id of the node, that contains the table with reference numbers.

Read below on how to set up things. See the documentation of
`org-refer-by-number' for normal usage after setup.

To create the Org-mode structure for `org-refer-by-number', you
need to:

- Create an Org-mode node, anywhere, any level.
- Get or create the Org-mode id of this node with `org-id-get-create'.
- Store this Id within `org-refer-by-number-id'; within your .emacs
  you may have a line like this:

  (setq org-refer-by-number-id \"7f480c3e-312f-4b9b-b833-6a7a253d1404\")

  your id, of course, will be different. The easiest way to get 
  your id, is to copy it from the property drawer of your reference node.


- Within your node: Add a table, that has at least two columns: a number 
  and a timstamp.
- Add one initial row to your table.

As an Example, your node may look like this:

*** My node for org-refer-by-number
  :PROPERTIES:
  :ID:       7f480c3e-312f-4b9b-b833-6a7a253d1404
  :END:

  | Number | Date            | Commentary      |
  |--------+-----------------+-----------------|
  | R277   | [2011-09-03 Sa] | My first number |



Now you may invoke `org-refer-by-number' to create a new
reference number.  For convenience, you might like to bind it to
a key like this:

  (global-set-key (kbd \"C-c C-x r\") 'org-refer-by-number)


So, putting it all together, your setup may look like this:


  (require 'org-refer-by-number)
  (setq org-refer-by-number-id \"7f480c3e-312f-4b9b-b833-6a7a253d1404\")
  (global-set-key (kbd \"C-c C-x r\") 'org-refer-by-number)


Create a node with a table as above, copy these lines to your .emacs,
replace the id with the one from your node and you are ready to 
use `org-refer-by-number'.

")

(defvar org-refer-by-number-windowconfig nil 
  "Saved Window-configuration during execution of `org-refer-by-number', only used internally.")

(defvar org-refer-by-number-last-action nil 
  "Last action performed by `org-refer-by-number', only used internally.")

(defun org-refer-by-number (arg) 
  "Add a new reference number or search for an existing one.

These numbers may then be used to refer to things outside of Org
for cases, where direct links are not possible. For example you
may write them on paper documents you receive or use them within
folder names you create.

Read below for a detailed description of this function and
three scenarios of common usage. See the documentation of
`org-refer-by-number-id' for the necessary setup.


This function operates on a dedicated table (called the reference
table) within a special Org-mode node, which you need to create
as part of your initial setup. The table has at least two
columns, the reference number (automatically increasing from row
to row) and the date of creation. The table is found through the
id of the containing node; this id must be stored within
`org-refer-by-number-id' (see there for an example).


This single function `org-refer-by-number' is the only
interactive function of this package. Its behaviour depends on
the position of the cursor, in the moment that you invoke it, as
well as on the possible presence of a prefix argument. There are
four cases:


Case one: Add a row. For this the cursor must be outside the node
containing your reference table and it must be on whitespace or
within a word that does not look like (see below for details) one
of your references.

In that case the current window configuration is saved and the
cursor jumps to the node, that contains your table. There, a
new line is added: The value within the first column is simply
created by incrementing the value from the previous line. This
new number is then pushed onto the kill ring, so that you may
later yank it. The second column of the new line is filled with
the current date. Any further columns are created empty and you
may fill them by hand, e.g. with a comment, which is higly
recommended.

Please note, that any decoration (e.g. non-numeric characters)
before or after the reference number are copied verbatim to the
newly added line. That means, if one row contains for example
\"R277\" within the first column, the next row will contain
\"R278\" by virtue of copying the \"R\" and adding 1 to 277 to
get 278.

If you like, you may even get more fancy and use references like
\"Reference-{277}\", e.g.

The main result of `org-refer-by-number' in this case is the new
number, that you may later use for reference-purposes, i.e. write
it down on some printed document or yank it into Org-mode or use
it within any non-Org application. The new row, that you just
have added to your table, records, when you have created this
reference along with any comment, that you supply.


Case two: Search for a reference within your table. For this, the
cursor must not be the node with your reference table, but it can
be anywhere in emacs and be within or immediately after a word,
that looks like one of your references (the cursor position makes
all the difference to case one). This reference then is searched
within the first column of your reference table (but before the
initial window configuration is stored away for a later
restore). This provides a quick way to look up references you
find within your Org-files: Just place the cursor on them
and invoke the function.


Case three: Return back to where you were and take the new
reference with you. For this, the cursor can be anywhere within
the node containing your reference table. The function then
restores the window configuration, that has been saved away
before. If a new reference has been created, it is appended to
the kill ring, so it may be yanked later on.


Case four: Search a reference within all your Org-files. For this
you need to supply a number as a prefix argument. On its first
invocation, the function will then search for this number within
your reference table; the cursor will be positioned on the
matching row. 

If then, from within your reference table, you invoke the
function again with a prefix argument, a multi-occur search over
all of your Org files is done (with the help of
`multi-occur'). You need not supply the reference number again in
this case, a sole and simple `C-u' as a prefix will do.


As examples, lets look at the three main scenarios where this
function can be useful:


Scenario 1: You receive a printed document and want to refer to
it from within Org-mode. For this you would:

- Type `C-c C-x r' (or whatever key you have chosen for
  `org-refer-by-number') to create a new reference number
  (e.g. \"R277\"). This positions the cursor within your
  reference table.
- Add some comments, if you like.
- Write this reference onto the printed paper document.
- Type `C-c C-x r' in emacs again to switch back to your original 
  window configuration.
- If you want, you may yank the newly generated number back
  anywhere into Org-mode as \"R277\".


Scenario 2: Some weeks later you read your Org-mode notes and
within them you find the reference \"R277\". You want to know,
what this reference refers to. For this you would:

- Position the cursor anywhere within this reference or
  immediately after it.
- Type `C-c C-x r' to look up this number within your reference table.
- Read the comment, that you have added before.
- Type `C-c C-x r' to go back to your original window
  configuration and position.
- Alternatively you could try `C-u C-c C-x r' for a `multi-occur'
  like described below.


Scenario 3: Within one of your desktop drawers, you find a paper
document with the reference \"R277\" written onto it and you
would like to know, where within Org-mode, you have referred to
this document. Then you would:

- Type `C-u 277 C-c C-x r' to search for this reference within
  your reference table.
- Read the respective line, date and maybe comment.
- If you want to find all of the occurences of this reference
  within your Org-files, type `C-u C-c C-x r' to do a
  `multi-occur' for this reference.
- Browse all the locations found.
- From within your reference table, type `C-c C-x r' to return to
  your original window configuration.


The three scenarios cover the most common cases of adding a reference
and looking up references, that you find either within Org or
somewhere outside.

"
  (interactive "P")

  (let (within-table parts maybe-search search what head last-number tail regex-tail columns kill-new-text message-text)
         
    ;; Find out, if we are within reference table or not
    (setq within-table (string= (org-id-get) org-refer-by-number-id))
    
    ;; Get the content of the active region or the word under cursor; do this before examinig reference table
    (if (and transient-mark-mode
             mark-active)
        (setq maybe-search (buffer-substring (region-beginning) (region-end)))
      (setq maybe-search (thing-at-point 'symbol)))
    (if (string= maybe-search "") (setq maybe-search nil))


    ;; Get decoration and number of last row from reference table
    (let ((m (org-id-find org-refer-by-number-id 'marker)))
      (unless m
        (error "Cannot find reference table with id \"%s\"; please check the value of 'org-refer-by-number-id'" org-refer-by-number-id))
      (with-current-buffer (marker-buffer m)
        (save-excursion
          (goto-char m)
          (setq parts (org-refer-by-number-trim-table nil t))
          )
        )
      (move-marker m nil)
      )
        
    (setq head (nth 0 parts))
    (setq last-number (nth 1 parts))
    (setq tail (nth 2 parts))
    (setq columns (nth 3 parts))
    
    ;; correct last action, if we have returned after leave
    (if (and within-table (eq org-refer-by-number-last-action 'leave))
        ;; we went back, but that was within reference table too
        (setq org-refer-by-number-last-action 'enter))


    ;; Find out, if we should search; do this in several tries, ordered by priority of
    ;; sources for search-string

    (unless search ; Superflous condition, just to make structure more clear
      ;; get search from numeric prefix
      (if (numberp arg) 
          (setq search (format "%s%d%s" head arg tail))
        )
      )
    
    (unless search
      ;; get search from table-field
      (when (and arg within-table)
        (save-excursion (setq search (org-table-get-field 1)))
        (if (string= search "") (setq search nil))
        )
      )

    (unless search
      ;; get search from maybe-search
      (when (or arg (not within-table))
        (when (and maybe-search 
                   (string-match (concat "\\(" (regexp-quote head) "[0-9]+" (regexp-quote tail) "\\)") maybe-search))
          (setq search (match-string 1 maybe-search))
          )
        )
      )

    ;; clean up search string
    (if (string= search "") (setq search nil))
    (if search (setq search (org-trim search)))
    (if (string= tail "") (setq regex-tail "\\($\\|[^0-9]\\)"))


    ;; Find out, what we are supposed to do
    (setq what (if within-table (if search 'multi-occur 'leave) (if search 'search 'add)))
    (when (and arg (not search)) (setq what 'enter))


    ;; move into table, if outside
    (when (not within-table)
      ;; save current window configuration
      (setq org-refer-by-number-windowconfig (current-window-configuration))
      (put 'org-refer-by-number-windowconfig 'marker (point-marker))
      
      ;; switch to reference table; this needs to duplicate some code from org-id-goto,
      ;; because point should be moved, if what equals 'enter
      (let ((m (org-id-find org-refer-by-number-id 'marker)))
        (org-pop-to-buffer-same-window (marker-buffer m))
        ;; after changing buffer we might be in table or not, so check again
        (setq within-table (string= (org-id-get) org-refer-by-number-id))
        ;; be careful with position within table, if we should just enter it
        (unless within-table (goto-char m))
        (org-refer-by-number-trim-table (if (eq what 'enter) nil t))
        (move-marker m nil)
        (org-show-context)
        )
      )

    ;; and actually do, what we are supposed to
    (cond
     ((eq what 'multi-occur) 
      (let (buff org-buffers)
        ;; Construct list of all org-buffers
        (dolist (buff (buffer-list))
          (set-buffer buff)
          (if (string= major-mode "org-mode")
              (setq org-buffers (cons buff org-buffers))))
        
        (multi-occur org-buffers (concat (regexp-quote search) regex-tail))
        (if (get-buffer "*Occur*")
            (setq message-text (format "multi-occur for '%s'" search))
          (setq message-text (format "Did not find '%s'" search))
          )
        )
      )

     ((eq what 'leave)
      (let ((column (org-table-current-column)))
        ;; copy different things depending on the last action
        (when (or (memq org-refer-by-number-last-action '(search multi-occur))
                  (<= column 1))
          ;; it does not help to copy the first field, because thats what we just searched for, so take last one
          (setq column columns)
          )
        (when (eq org-refer-by-number-last-action 'add)
          (setq column 1))
        
        ;; add to kill ring
        (if (memq org-refer-by-number-last-action '(add enter search))
            (while (progn 
                     (save-excursion (setq kill-new-text (org-trim (org-table-get-field column))))
                     (and (> column 0)
                          (string= kill-new-text ""))
                     )
              (setq column (- column 1))
              )
          )

        ;; clean up table before leaving
        (org-refer-by-number-trim-table)
        (when org-refer-by-number-windowconfig 
          (set-window-configuration org-refer-by-number-windowconfig)
          (goto-char (marker-position (get 'org-refer-by-number-windowconfig 'marker)))
          (set-marker (get 'org-refer-by-number-windowconfig 'marker) nil)
          (setq org-refer-by-number-windowconfig nil)
          )
        
        (setq message-text "Back")
        )
      )
        
    ((eq what 'search)
      ;; search upward in table within first column
      (let (found (initial (point)))
        (forward-line)
        (while (and (not found)
                    (forward-line -1)
                    (org-at-table-p))
          (save-excursion (setq found (string= search (org-trim (org-table-get-field 1)))))
          )
        (if found
            (progn
              (setq message-text (format "Found '%s'" search))
              (org-table-goto-column 1)
              (if (looking-back " ") (backward-char))
              )
          (setq message-text (format "Did not find '%s'" search))
          (goto-char initial)
          (forward-line)
          (setq what 'missed)
          )
        )
      )
        
    ((eq what 'add)
      ;; nothing to search for, add a new row
      (let ((new (format "%s%d%s" head (1+ last-number) tail)))
        (org-table-insert-row 1)
        (insert new)
        (org-table-goto-column 2)
        (org-insert-time-stamp nil nil t)
        (org-table-goto-column 3)
        (org-table-align)
        (if maybe-search (setq kill-new-text maybe-search))
        (setq message-text (format "Adding a new row '%s'" new))
        )
      )

    ((eq what 'enter)
     ;; already there, not much to do
     (setq message-text "At reference table")
     )

    (t (error "This is a bug: Unmatched condition '%s'" what))
    )
    
    ;; remember what we have done for next time
    (setq org-refer-by-number-last-action what)
        
    
    ;; tell, what we have done and what can be yanked
    (if (string= kill-new-text "") (setq kill-new-text nil))
    (let ((m (concat 
              message-text
              (if (and message-text kill-new-text) " and r" (if kill-new-text "R" ""))
              (if kill-new-text (format "eady to yank '%s'" kill-new-text) "")
              )))
      (unless (string= m "") (message m))
      )
    (if kill-new-text (kill-new kill-new-text))
    )
  )


(defun org-refer-by-number-trim-table (&optional goto-end get-parts)
  "Trim reference table, only used internally"

  (let ((initial (point-marker))
        field
        parts
        columns)
    ;; Go to heading of node
    (while (not (org-at-heading-p)) (forward-line -1))
    ;; Go beyound end of table
    (while (not (org-at-table-p)) (forward-line 1))
    (while (org-at-table-p) (forward-line 1))
    ;; Kill all empty rows at bottom
    (while (progn
             (forward-line -1)
             (org-table-goto-column 1)
             (save-excursion (string= "" (org-trim (org-table-get-field 1))))
             )
      (org-table-kill-row)
      )

    (when get-parts

      ;; find out number of columns
      (org-table-goto-column 100)
      (setq columns (- (org-table-current-column) 1))

        ;; retrieve any decorations around the number within first field of the last row
      (setq field (org-trim (org-table-get-field 1)))
      (or (string-match "^\\([^0-9]*\\)\\([0-9]+\\)\\([^0-9]*\\)$" field)
          (error "Last field of reference table '%s' does not contain a number." field))

      ;; these are the decorations used within the last row of the reference table
      (setq parts (list (match-string 1 field) (string-to-number (match-string 2 field)) (match-string 3 field) columns))
      )

    (unless goto-end (goto-char (marker-position initial)))
    (set-marker initial nil)
    
    parts
    )
)


(provide 'org-refer-by-number)

