;;; org-parser.el --- parse org files into structured datatypes.  -*- lexical-binding: t; -*-

;; Version: 0.4
;; This file is not part of GNU Emacs.

;; Copyright (C) 2016-2017 Zachary Kanfer

;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.


;; Keywords: files, outlines, tools
;; Homepage: https://bitbucket.org/zck/org-parser.el


;; Package-Requires: ((emacs "25.1") (dash "2.12.0") (ht "2.1"))

;;; Commentary:

;;; Code:

(require 'seq)
(require 'subr-x)
(require 'cl-lib)
(require 'dash)
(require 'ht)

;;;###autoload
(defun org-parser-parse-buffer (buffer)
  "Parse BUFFER into a list of structure items."
  (with-current-buffer buffer
    (org-parser-parse-string (buffer-string))))

;;;###autoload
(defun org-parser-parse-file (filename)
  "Parse FILENAME into a list of structure items."
  (with-temp-buffer
    (insert-file-contents filename)
    (org-parser-parse-buffer (current-buffer))))

;;;###autoload
(defun org-parser-parse-string (string)
  "Parse STRING into a list of structure items."
  (destructuring-bind (settings content) (-split-with (lambda (ele) (string-prefix-p "#+" ele))
                                                      (split-string (string-remove-suffix "\n" (substring-no-properties string))
                                                                    "\n"))
    (ht (:in-buffer-settings (org-parser--get-in-buffer-settings settings))
        (:content (org-parser--convert-text-tree (org-parser--make-text-tree (org-parser--split-into-blocks content)))))))

(defun org-parser--split-into-blocks (lines)
  "Split LINES into blocks; one block for each headline or plain list.

A block is a single string (with newlines in it if necessary) that,
optionally, begins with a headline or plain list, but otherwise has
no headlines or plain lists in it."
  (when lines
    (org-parser--split-into-blocks-helper lines)))

(defun org-parser--split-into-blocks-helper (lines)
  "Split LINES into blocks; one block for each headline or plain list.

A block is a single string (with newlines in it if necessary) that,
optionally, begins with a headline or plain list, but otherwise has
no headlines or plain lists in it."
  (when lines
    (let* ((this-block-end (-find-index #'org-parser--title-line-p
                                        (cl-rest lines)))
           (next-block-start (if this-block-end
                                 (1+ this-block-end)
                               (length lines))))
      (cons (string-join (seq-subseq lines 0 next-block-start)
                         "\n")
            (org-parser--split-into-blocks-helper (seq-subseq lines next-block-start))))))

(defun org-parser--drop-single-empty-string-at-beginning-and-end (string-list)
  "Drop a maximum of one empty string from each of the beginning and end of STRING-LIST."
  (when string-list
    (subseq string-list
            (if (equal (cl-first string-list)
                       "")
                1
              0)
            (if (equal (-last-item string-list)
                       "")
                (1- (length string-list))
              (length string-list)))))

(defun org-parser--get-in-buffer-settings (lines)
  "Get the buffer settings out of the initial lines of LINES.

In-buffer settings are described at http://orgmode.org/manual/In_002dbuffer-settings.html#In_002dbuffer-settings"
  (when lines
    (destructuring-bind (first . rest) lines
      (if (string-match "#\\+\\([[:graph:]]+\\):\\(.*\\)" first)
          (cons (cons (match-string 1 first)
                      (split-string (match-string 2 first)))
                (org-parser--get-in-buffer-settings rest))
        (org-parser--get-in-buffer-settings rest)))))

(defun org-parser--guess-level (text)
  "Attempts to guess the level of the TEXT.

This method will definitely work for headlines,
and will probably work for plain lists.

The situations where this breaks are where there have been multiple
ordered lists in parents for TEXT, as the bullet for ordered lists
is more than one character."
  (cond ((string-match "\\`\\(\\*+\\) " text)
         (length (match-string 1 text)))
        ((string-match "\\`\\(\s*\\)[-+[:digit:]]" text)
         (1+ (/ (length (match-string 1 text)) 2)))
        (t 1)))


(defun org-parser--bullet-type (full-bullet)
  "Return the bullet-type of FULL-BULLET.

For example, \"** \" has a bullet type of ?*.
Plain lists are the leading symbol (+ or -).
Ordered lists are ?. or ?)"
  (cond ((string-match "\\`\\*+ " full-bullet)
         ?*)
        ((string-match "\\`\s*\\([+-]\\) " full-bullet)
         (elt (match-string 1 full-bullet) 0))
        ((string-match "\\`\s*[[:digit:]]+\\([.)]\\) " full-bullet)
         (elt (match-string 1 full-bullet) 0))))


(defun org-parser--convert-text-tree (text-tree)
  "Convert TEXT-TREE to a list of org structures.

TEXT-TREE is a list generated by make-text-tree.  Each element could
be a single string, or a list where the head is the headline or plain
list, and the rest of the list is all the children."
  (mapcar #'org-parser--convert-text-block
          text-tree))

(defun org-parser--convert-text-block (text-block)
  "Convert TEXT-BLOCK to an org structure.

A TEXT-BLOCK is an element generated by make-text-tree.  This could be
a single string, or a list where the head is the headline or plain
list, and the rest of the list is all the children.

Return a single thing representing the block.  If the block is a
headline, it will be an org structure hash.  If the block is not a
headline, it'll be a list of strings.

Properties of structure hashes:
:text -- the text on the first line of the block.
:body -- the text on following lines of the block, as a list, where each line
    is represented by a list of items.
    For example:
    * this is the 'text'
      This is the 'body', which can
      continue to multiple lines.

    Results in:
    '((\"This is the 'body', which can\") (\"continue to multiple lines.\"))
:properties -- the org properties of the block, as an association list
of property-name to property-value. Each name and value is a string,
so you can't use #'alist-get, but must use #'assoc.
:children -- a list of child structure objects.
:bullet-type -- a character indicating the type of bullet used,
    either ?*, ?-, ?+, ?., or ?) .  For ordered lists --
    (either ?\) or ?.) -- this is the character /after/ the number.
    For other types of blocks, the bullet is the entire number."
  (if (org-parser--title-line-p (car text-block))
      (let ((table (make-hash-table))
            (text (car text-block)))
        (puthash :text (org-parser--get-text text) table)
        (puthash :body (org-parser--get-body text) table)
        (puthash :properties (org-parser--get-properties text) table)
        (puthash :tags (org-parser--get-tags text) table)
        (puthash :bullet-type (org-parser--bullet-type text) table)
        (puthash :children (org-parser--convert-text-tree (cdr text-block)) table)
        table)
    text-block))

(defun org-parser--remove-bullet (text)
  "Return TEXT without the bullet at the beginning."
  (cond ((string-match "\\`\\*+ ?\\(\\(.\\|\n\\)+\\)" text)
         (match-string 1 text))
        ((string-match "\\` *[-+*] ?\\(\\(.\\|\n\\)+\\)" text)
         (match-string 1 text))
        ((string-match "\\` *[[:digit:]]+[.)] ?\\(\\(.\\|\n\\)+\\)" text)
         (match-string 1 text))))

(defun org-parser--remove-tags (text)
  "Return TEXT, a single line, without tags at the end.

If TEXT has any tags, strip whitespace between the text and the
tags.  If there are no tags, don't strip ending whitespace.

The org manual says tags consist of \"letters, numbers, ‘_’, and ‘@’.\""
  (replace-regexp-in-string "[ \t]+\\(:[[:alnum:]@_]+\\)+:$"
                            ""
                            text))

(defun org-parser--parse-for-markup (text)
  "Parse TEXT into its structure, respecting markup.

This handles things like links and italic text.

This will return a list of things.  Each thing in this list will be
either a string (for no markup), or a hash, with a :type key to
indicate what the type of the markup is.

Possible :type values are :link, :block."
  (cond ((null text) nil)
        ((string-empty-p text) (list ""))
        ((string-prefix-p "#+BEGIN_" text)
         (org-parser--make-block text))
        ((string-match "\\(.*?\\)\\[\\[\\([^][]+\\)\\]\\[\\([^][]+\\)\\]\\]\\(.*\\)"
                       text)
         (let* ((text-before-link (match-string 1 text))
                (target-text (match-string 2 text))
                (link-text (match-string 3 text))
                (link-hash (org-parser--make-link-hash target-text link-text))
                (raw-text-after-link (match-string 4 text))
                (text-after-link (if (string-empty-p raw-text-after-link)
                                     nil
                                   raw-text-after-link)))
           (if (string-empty-p text-before-link)
               (cons link-hash
                     (org-parser--parse-for-markup text-after-link))
             (cl-list* text-before-link
                       link-hash
                       (org-parser--parse-for-markup text-after-link)))))
        (t (list text))))

(defun org-parser--make-link-hash (target-text link-text)
  "Make a link hash pointing to TARGET-TEXT with text LINK-TEXT.

It will have keys :target, :text, and :type.  The :type value will be :link."
  (let ((link-hash (make-hash-table)))
    (puthash :target target-text link-hash)
    (puthash :text link-text link-hash)
    (puthash :type :link link-hash)
    link-hash))

(defun org-parser--make-block (text)
  "Make a block from TEXT, some text representing a block.

TEXT should have both the beginning #+BEGIN_whatever and the ending
#+END_whatever lines."
  (let ((block (make-hash-table)))
    (when (string-match "^#\\+BEGIN_\\(\\w+\\) ?\\([^\n]*\\)\n\\(.*\\(\n.*\\)*\\)\n#\\+END_\\1\n?$" text)
     (puthash :type :block block)
     (puthash :block-type (match-string 1 text) block)
     (puthash :arguments (match-string 2 text) block)
     (puthash :body (match-string 3 text) block))
    block))

(defun org-parser--get-text (text)
  "Return the first line of TEXT without the bullet, parsed for org formatting.

This is a list of items."
  (--> text
       (org-parser--remove-bullet it)
       (split-string it "\n" t)
       (car it)
       (org-parser--remove-tags it)
       (org-parser--parse-for-markup it)))

(defun org-parser--get-body (text)
  "Return the body of a given TEXT.

This method will drop initial newlines of TEXT, drop any properties,
then treat everything after a newline as the body.

The body is returned as a list, where each item in the list represents
either a line in TEXT, or a #+BEGIN_ block.  Each line in TEXT is a
list of items itself, and a block is just a hash."


  (let ((lines (org-parser--split-body-text-into-groups text)))
    (when (cdr lines)

      ;;properties are not part of the body, so we drop properties
      (mapcar #'org-parser--parse-for-markup
              ;;zck maybe keeping property lines together should be done in the split-body-text-into-groups.
              (if (string-match-p "^\s*:PROPERTIES:$"
                                  (upcase (cl-second lines)))
                  (cdr (-drop-while (lambda (line) (not (string-match-p "^\s*:END:$" line)))
                                    (cddr lines)))
                (cdr lines))))))

(defun org-parser--split-body-text-into-groups (body-text)
  "Split BODY-TEXT into groups.

Normally this is just on newlines, but blocks are multiline."
  (let ((lines (org-parser--drop-single-empty-string-at-beginning-and-end (split-string body-text "\n")))
        (result nil)
        (cur-line nil))
    (while lines
      (let ((cur-line (pop lines)))
        (when (or (string-prefix-p "#+BEGIN_" cur-line t)
                  (string-prefix-p "#+NAME: " cur-line t))
          (destructuring-bind (rest-of-block post-block-body-text) (-split-with (lambda (line) (not (string-prefix-p "#+END_" line)))
                                                                              lines)
            (setq cur-line (concat cur-line "\n" (string-join rest-of-block "\n")))
            (setq lines post-block-body-text)
            (when (string-prefix-p "#+END_" (car lines))
              (setq cur-line (concat cur-line "\n" (pop lines))))))
        (push cur-line result)))
    (nreverse result)))

(defun org-parser--get-properties (text)
  "Return the properties of TEXT.

Properties are an alist, where the key is the property key, and the
value is the property value."
  (let ((properties-alist nil)
        (property-text (org-parser--extract-property-text text)))
    (when property-text
      (dolist (line (split-string property-text "\n" t))
        (when (string-match ":\\([^:]*\\):\s*\\(.*\\)"
                            line)
          (push (cons (match-string 1 line)
                      (match-string 2 line))
                properties-alist))))
    (nreverse properties-alist)))


(defun org-parser--get-tags (text)
  "Return the tags of TEXT, a string representing a block.

The tags are returned as a list of strings.  The org manual says tags
consist of \"letters, numbers, ‘_’, and ‘@’.\""
  (let ((first-line (car (split-string text "\n"))))
    (-some--> first-line
              (string-match "[ \t]+\\(\\(?::[[:alnum:]@_]+\\)+\\):$"
                            it)
              (match-string 1 first-line)
              (split-string it ":" t))))

(defun org-parser--extract-property-text (text)
  "Extract the property text from TEXT.

Property text is the text between :PROPERTIES: and :END: of a
  string."
  (let* ((begin-regexp "\n\s*:PROPERTIES:\n")
         (end-regexp "\n\s*:END:\\(:?\n\\|$\\)")
         (begin-match (string-match begin-regexp text))
         (beginning-of-drawer-internals (match-end 0))
         (end-match (string-match end-regexp text begin-match))
         (end-of-drawer-internals (match-beginning 0)))
    (when (and begin-match end-match)
      (substring text
                 beginning-of-drawer-internals
                 end-of-drawer-internals))))


(defun org-parser--make-text-tree (blocks)
  "Organize BLOCKS, a list of text blocks, into the overall tree structure.

Blocks are defined in org-parser--split-into-blocks

Return a list that represents the structure of BLOCKS.  Each element
is either a list or a string.  If an element is a list, the first item
in it is the headline, plain list head, or the bare string.  If it's a
bare string, there are no more elements in the list.  (This bare
string happens only when an org file doesn't start with a headline.)"
  (when blocks
    (let* ((first-line (car blocks))
           (first-block (seq-take-while (lambda (line)
                                          (org-parser--descendent-p first-line line))
                                        (cdr blocks))))
      (cons (cons first-line
                  (org-parser--make-text-tree first-block))
            (org-parser--make-text-tree (seq-drop blocks
                                                  (+ 1 (length first-block))))))))

(defun org-parser--descendent-p (root possible-descendent)
  "Whether ROOT and POSSIBLE-DESCENDENT should be in the same block.

For example, a block that starts '* headline' should be in the same block
 at '** nested', but not the same block as '* another headline.'"
  (if (org-parser--headline-p root)
      (or (and (org-parser--headline-p possible-descendent)
               (< (org-parser--guess-level root)
                  (org-parser--guess-level possible-descendent)))
          (org-parser--plain-list-p possible-descendent))
    (and (org-parser--plain-list-p possible-descendent)
         (< (org-parser--guess-level root)
            (org-parser--guess-level possible-descendent)))))

(defun org-parser--title-line-p (line)
  "Return whether LINE corresponds to a title line.

A title line is the first line of a headline or plain list."

  (or (org-parser--headline-p line)
      (org-parser--plain-list-p line)))

(defun org-parser--headline-p (line-or-char)
  "Return t if LINE-OR-CHAR is a headline.

LINE-OR-CHAR can be either a line, or the character in a structure
indicating the bullet type."
  (if (characterp line-or-char)
      (equal line-or-char ?*)
    (and (> (length line-or-char)
            0)
         (equal (elt line-or-char 0)
                ?*))))

(defun org-parser--plain-list-p (line-or-char)
  "Return t if LINE-OR-CHAR is a plain list.

LINE-OR-CHAR can be either a line, or the character in a structure
indicating the bullet type."
  (if (characterp line-or-char)
      (not (org-parser--headline-p line-or-char))
    (and (> (length line-or-char)
            0)
         (or (org-parser--ordered-list-p line-or-char)
             (string-match "\\`\s*[-*+] " line-or-char))
         (not (org-parser--headline-p line-or-char)))))

(defun org-parser--ordered-list-p (line-or-char)
  "Return t if LINE-OR-CHAR is an ordered list.

LINE-OR-CHAR can be either a line, or the character in a structure
indicating the bullet type."
  (if (characterp line-or-char)
      (or (= ?. line-or-char)
          (= ?\) line-or-char))
    (and (string-match "\\` *[[:digit:]]+[.)] " line-or-char) t)))

(defun org-parser--make-bullet (structure parent-bullet older-sibling-count)
  "Return the string representing the bullet for STRUCTURE.

This bullet includes the whitespace after the bullet.

PARENT-BULLET is used to determine indentation.

There should be OLDER-SIBLING-COUNT siblings before this one.  This only matters for ordered lists."
  (cond ((org-parser--headline-p (gethash :bullet-type structure))
         ;;we have a headline, so we must be under a headline (right?)
         (if (string-match "\\`\\(\\*+ \\)$" parent-bullet)
             (format "*%s" (match-string 1 parent-bullet))
           "* "))
        ((org-parser--ordered-list-p (gethash :bullet-type structure))
         (format "%s%d%c "
                 (org-parser--get-nested-whitespace parent-bullet)
                 (1+ older-sibling-count)
                 (gethash :bullet-type structure)))
        ((org-parser--plain-list-p (gethash :bullet-type structure))
         ;;zck plain lists can be under headlines, or under other plain lists
         (if t ;; (org-parser--headline-p parent-bullet)
             (format "%s%c "
                     (org-parser--get-nested-whitespace parent-bullet)
                     (gethash :bullet-type structure))))
        (t 'whaaat?)))

(defun org-parser--get-nested-whitespace (bullet)
  "Gets the nested whitespace for a plain list under BULLET.

BULLET can be the bullet for a plain list or a headline."
  (if (org-parser--headline-p bullet)
      ""
    (if (string-match "\\`\\(\s*[^\s]+\\)\s" bullet)
        (make-string (1+ (length (match-string 1 bullet)))
                     ?\s)
      "")))

(defun org-parser--to-string (org-file-structure)
  "Convert ORG-FILE-STRUCTURE to a string.

ORG-FILE-STRUCTURE is a structure created by org-parser
representing an org file.

The result should be identical to the org file parsed to create the
structure."
  (concat (when (gethash :in-buffer-settings org-file-structure)
            (concat (org-parser--in-buffer-settings-to-string (gethash :in-buffer-settings org-file-structure))
                    "\n"))
          (org-parser--to-string-helper (gethash :content org-file-structure) "")))

(defun org-parser--in-buffer-settings-to-string (in-buffer-properties-list)
  "Convert the IN-BUFFER-PROPERTIES-LIST to a string."
  (string-join (mapcar (lambda (property)
                         (format "#+%s: %s"
                                 (first property)
                                 (string-join (rest property) " ")))
                       in-buffer-properties-list)
               "\n"))

(defun org-parser--to-string-helper (org-file-structure parent-bullet)
  "Convert ORG-FILE-STRUCTURE, a list of structure hash tables, to a string.

These structure hash tables all have the same parent, whose bullet
is PARENT-BULLET.

This should be identical to the org file parsed to create the structure."
  (string-join (cl-mapcar (lambda (structure siblings-before-this-one)
                            (org-parser--single-to-string structure parent-bullet siblings-before-this-one))
                          org-file-structure
                          (number-sequence 0
                                           (1- (length org-file-structure))))))

(defun org-parser--single-to-string (structure parent-headline siblings-before-this-one)
  "Create the string for STRUCTURE, with parent having PARENT-HEADLINE.

SIBLINGS-BEFORE-THIS-ONE is the count of older siblings with the same parent."
  (cond ((hash-table-p structure)
         (let* ((this-bullet (org-parser--make-bullet structure parent-headline siblings-before-this-one))
                (title-line (org-parser--format-title-line structure this-bullet))
                (body-text (org-parser--format-body (gethash :body structure)))
                (properties-text (org-parser--format-properties (gethash :properties structure)))
                (children-text (org-parser--to-string-helper (gethash :children structure)
                                                             this-bullet)))
           (concat title-line
                   properties-text
                   body-text
                   children-text)))
        ((listp structure)
         (string-join (cl-mapcar (lambda (structure siblings-before-this-one)
                                   (org-parser--single-to-string structure parent-headline siblings-before-this-one))
                                 structure
                                 (number-sequence 0
                                                  (1- (length structure))))))
        ((stringp structure)
         (format "%s\n" structure))))

(defun org-parser--format-title-line (structure formatted-bullets)
  "Format STRUCTURE's title line, including FORMATTED-BULLETS.

This can't calculate FORMATTED-BULLETS because we don't pass in
enough information to know how much to indent STRUCTURE."
  (let ((pre-tags (format "%s%s"
                         formatted-bullets
                         (org-parser--format-text (gethash :text structure))))
        (tags (string-join (gethash :tags structure)
                           ":")))
    (if (string-empty-p tags)
        (format "%s\n"
                pre-tags)
      (format "%s%s:%s:\n"
              pre-tags

              ;;even if the text is very long, put in at least one space.
              (make-string (max 1
                                (- 77
                                   (length pre-tags)
                                   2 ;;the colons at the beginning and end of tags.
                                   (length tags)))
                           ?\s)
              tags))))

(defun org-parser--format-text (structure-text)
  "Format STRUCTURE-TEXT into a string.

STRUCTURE-TEXT is either a single string (in which case it returns
unchanged), or a list of structure items, in which case this returns a
string that's the formatted representation of the list."
  (if (stringp structure-text)
      structure-text
    (string-join (mapcar #'org-parser--format-text-single-item
                         ;;should this add newlines between items? Probably not. But does that mean that if we have a structure object with a body with multiple things in it, what happens?
                         structure-text))))

(defun org-parser--format-properties (properties-alist)
  "Format PROPERTIES-ALIST into a string."
  (when properties-alist
    (format ":PROPERTIES:\n%s\n:END:\n"
            (string-join (mapcar (lambda (ele)
                                   (format ":%s: %s"
                                           (car ele)
                                           (cdr ele)))
                                 properties-alist)
                         "\n"))))

(defun org-parser--format-body (body-list)
  "Format the body represented by BODY-LIST.

Each element of BODY-LIST should be a list itself."
  (when body-list
    (concat (string-join (mapcar #'org-parser--format-body-line
                                 body-list)
                         "\n")
            "\n")))

;;zck rename body-line? It can be a line, or a block.
(defun org-parser--format-body-line (body-line)
  "Format BODY-LINE into a string."
  (if (listp body-line)
      (string-join (mapcar #'org-parser--format-text-single-item
                           body-line))

    ;;then single-item can handle it by itself.
    (org-parser--format-text-single-item body-line)))

(defun org-parser--format-text-single-item (structure-item)
  "Format STRUCTURE-ITEM, a string or hash, into a string."
  (cond ((stringp structure-item)
         structure-item)
        ((hash-table-p structure-item)
         (case (gethash :type structure-item)
           (:link (format "[[%s][%s]]"
                          (gethash :target structure-item)
                          (gethash :text structure-item)))
           (:block (let ((block-type (gethash :block-type structure-item))
                         (args (gethash :arguments structure-item)))
                     (string-join (list (format "#+BEGIN_%s%s"
                                                block-type
                                                (if (and args (not (string-empty-p args)))
                                                    (format " %s" args)
                                                  ""))
                                        (gethash :body structure-item)
                                        (format "#+END_%s" block-type))
                                  "\n")))))
        (t "")))




(defun org-parser--get-nested-children (structure &rest children-indices)
  "Get children recursively from STRUCTURE; at each level, take the nth child, where n is the next element in CHILDREN-INDICES."
  (if (not children-indices)
      structure
    (apply #'org-parser--get-nested-children
           (elt (gethash :children structure)
                (cl-first children-indices))
           (cl-rest children-indices))))

(defun org-parser--get-bullet (text)
  "Get the bullet form from TEXT, including the space after.

If TEXT does not start with a bullet form, this will error."
  (cond ((string-match "\\`\\(\\*+ \\)" text)
         (match-string 1 text))
        ((string-match "\\`\\(\s*[+-] \\)" text)
         (match-string 1 text))
        ((string-match "\\`\\(\s*[[:digit:]]+[.)]\s\\)" text)
         (match-string 1 text))
        (t (error "Error calling org-parser--get-bullet on a string that doesn't have bullets"))))

(provide 'org-parser)

;;; org-parser.el ends here
