;;; fuzzy-match.el --- fuzzy matching
;; 
;; Filename: fuzzy-match.el
;; Description: fuzzy matching
;; Author: Simon Marshall <s i m o n  AT  g n u . o r g>
;; Maintainer: Drew Adams <d r e w . a d a m s  AT  o r a c l e . c o m>
;; Copyright (C) 2007-2012, Drew Adams, all rights reserved.
;; Copyright (C) 1993, 1994 Simon Marshall, all rights reserved.
;; Created: 1993, by Simon Marshall
;; Version: 1.04
;; Last-Updated: Sun Jan  1 14:05:19 2012 (-0800)
;;           By: dradams
;;     Update #: 176
;; URL: http://www.emacswiki.org/cgi-bin/wiki/fuzzy-match.el
;; Keywords: matching completion string
;; Compatibility: GNU Emacs: 20.x, 21.x, 22.x, 23.x
;; 
;; Features that might be required by this library:
;;
;;   None
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;;; Commentary:
;;
;; Purpose:
;; 
;; Fuzzy-match is a package of functions to provide non-exact comparison
;; between strings.  Since I am no expert on such things, and certain criteria
;; for non-exact comparison had to be dropped for reasons of efficiency (e.g.,
;; transposition), and the non-exact nature of non-exact comparison, this
;; package may or may not provide what you want.
;;
;; Caveat:
;;
;; This is fuzzy software.  Use it at your own risk.
;;
;; The fuzzy-matcher deals with comparing strings.  For a programmer wishing to
;; use the fuzzy-match library, the front-end functions are likely to be
;; `FM-matchiness' (and corresponding `FM-closeness'), `FM-all-fuzzy-matches'
;; (and corresponding `FM-all-close-matches'), and `FM-fuzzy-sort'.  These can
;; be thought to mirror `string-match', `all-completions' and `sort'.
;; 
;; The function `FM-matchiness' returns an integer which is the number of
;; matching characters from STRING1 in STRING2.  What denotes "the number of
;; matching characters" is arbitrary.
;; 
;; The fuzziness between two strings, STRING1 and STRING2, is calculated by
;; finding the position in STRING2 of a prefix of STRING1.  The first character
;; of STRING1 is found in STRING2.  If we find it, we continue matching
;; successive characters from STRING1 at successive STRING2 positions.  When we
;; have found the longest prefix of STRING1 in STRING2, we decide whether it is
;; a match.  It is considered a match if the length of the prefix is greater or
;; equal to the offset of the beginning of the prefix of STRING1 in STRING2.
;; This means that "food" will match "barfoo" because "foo" (the prefix)
;; matches "foo" in "barfoo" with an offset and length of 3.  However, "food"
;; will not be considered to match "barfu", since the length is 1 while the
;; offset is 3.  The fuzz value of the match is the length of the prefix.  If
;; we find a match, we take the prefix off STRING1 and the string upto the end
;; of the match in STRING2.  If we do not find a match, we take off the first
;; character in STRING1.  Then we try and find the next prefix.
;;
;; So, to walk through an example:
;;
;; (FM-matchiness "pigface" "pigsfly"):
;;
;; STRING1              STRING2         MATCH LENGTH    OFFSET          FUZZ
;; pigface              pigsfly         3               0               3
;; face                 sfly            1               1               1
;; ace                  ly              0               0               0
;; ce                   ly              0               0               0
;; c                    ly              0               0               0
;;
;;      => 4
;; 
;; (FM-matchiness "begining-of-l" "beginning-of-l"):
;; 
;; STRING1              STRING2         MATCH LENGTH    OFFSET          FUZZ
;; begining-of-l        beginning-of-l  5               0               5
;; ing-of-l             ning-of-l       8               1               8
;;
;;      => 13
;;
;; Another function of interest is `FM-all-fuzzy-matches'.  This returns a list
;; of those strings that have the highest fuzzy match with a given string.
;; Those strings are sorted so that there is a preference for strings with the
;; same number of characters, and sharing the longest prefix with the given
;; string:
;;
;; (FM-all-fuzzy-matches "abc" '("xxabcxx" "xabcxxx" "xabx"))
;;      => ("xabcxxx" "xxabcxx")
;;
;; (FM-all-fuzzy-matches "point-mx" (all-completions "point" obarray))
;;      => ("point-max" "point-max-marker")
;;
;; (FM-all-fuzzy-matches "begining-of-l" (all-completions "begin" obarray))
;;      => ("beginning-of-line")
;;
;; Corresponding to `FM-matchiness' and `FM-all-fuzzy-matches' are
;; `FM-closeness' and `FM-all-close-matches'.  They differ from the former
;; functions in that they take into account the difference in length between
;; the target string and candidate string:
;;
;; (FM-closeness "begining-of-l" "beginning-of-l")
;;      => 12
;;
;; Note from above that the matchiness is 13 and the difference in length of
;; the two strings is 1.
;;
;; (FM-all-close-matches "point-mx" (all-completions "point" obarray))
;;      => ("point-max")
;;
;; Note from above that although the matchiness is equal between the target
;; "point-mx" and the candidates "point-max" and "point-max-marker", the former
;; candidate has less of a difference in length from the target.
;;
;; Other functions that may be of use to package writers using this package are
;; `FM-map-fuzzy-matches' (and corresponding `FM-map-close-matches') and
;; `FM-max-matchiness' (and corresponding `FM-max-closeness').  The mapping
;; functions map matchiness or closeness to a list, while the max functions
;; return the maximum matchiness or closeness from a list.
;;
;; Also provided are some interface functions for user packages.  These
;; functions are `FM-offer-corrections' and `FM-list-candidates'.  To
;; demonstrate the usefulness of this package, `lisp-spell-symbol' (analogous
;; to `lisp-complete-symbol') is provided.  Without an arg, the command uses
;; `FM-all-close-matches' to find spelling corrections:
;;
;; (goto-char (point-mx M-x lisp-spell-symbol RET
;;      -| Replaced point-mx with point-max
;; (goto-char (point-max
;;
;; With a double prefix arg, the command uses `FM-all-fuzzy-matches' to find
;; spelling corrections:
;;
;; (goto-char (point-mx C-u C-u M-x lisp-spell-symbol RET
;;      -| Possible candidates are:
;;      -| point-max                       point-max-marker
;;
;; Any number of prefix args means that the user is prompted when replacing
;; with the single correction candidate.
;;
;; Installation:
;;
;; Put this file where your Emacs can find it and byte compile it.
;;
;; To use, put in your package that uses these functions:
;;
;; (require 'fuzzy-match)
;; 
;; To use the interactive package, put the following in your ~/.emacs file:
;;
;; (autoload 'lisp-spell-symbol "fuzzy-match"
;;   "Perform spell checking on Lisp symbol preceding point." t)
;; (define-key esc-map "#" 'lisp-spell-symbol)
;;
;; This will define the key M-# (ESC #) to call `lisp-spell-symbol'.
;; For Emacs-19 users you can also add an entry to the "ispell" menu-bar:
;;
;; (define-key-after ispell-menu-map [ispell-symbol]
;;   '("Check Symbol" . lisp-spell-symbol) 'ispell-word))
;;
;;
;;  If you like `fuzzy-match.el', you might also be interested in
;;  Icicles, which lets you use the same fuzzy matching for minibuffer
;;  input completion: http://www.emacswiki.org/cgi-bin/wiki/Icicles.
 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Change Log:
;;
;; 2011/01/04 dadams
;;     Added autoload cookies for commands.
;; 2007/10/01 dadams
;;     FM-lessiness:
;;       Return t if no occurrence of a STRING prefix in STRING1 or STRING2.
;;     FM-all-fuzzy-matches: Return nil if best fuzzy match has matchiness 0.
;;     FM-offer-corrections:
;;       Added a complete interactive spec using FM-symbol-name-before-point.
;;     lisp-spell-symbol: Use FM-symbol-name-before-point.
;;     Added: FM-symbol-name-before-point.  If no symbol, return "", not nil.
;;     Updated file header.
;; - 1.00--1.01: smarshall
;;   Inlined FM-strstr-intern into FM-matchiness-intern for speed.
;;   Added FM*close* to mirror FM*fuzzy* functions.
;;   Added FM-offer-corrections, FM-list-candidates, lisp-spell-symbol.
;; - 1.01--1.02: smarshall
;;   Made FM-offer-corrections deal with identical single correction.
;;   Made lisp-spell-symbol use FM-all-fuzzy-matches if user wants.
;;   Updated ispell-menu-map comments for Emacs-19.25.
;;   Removed mouse-choose-completion hack from FM-list-candidates.
;; - 1.02--1.03: smarshall
;;   Corrected Copyleft.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2, or
;; (at your option) any later version.
;; 
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;; 
;; You should have received a copy of the GNU General Public License
;; along with this program; see the file COPYING.  If not, write to
;; the Free Software Foundation, Inc., 51 Franklin Street, Fifth
;; Floor, Boston, MA 02110-1301, USA.
;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 
;;; Code:

;;; Bizarre, but FM-strstr-intern and FM-matchiness-intern are quickest when
;;; dealing with lists.  If coded to deal with strings using aref and
;;; string-match, it takes longer.  (Though this might not be true if we had a
;;; non-regexp version of string-match---of course it would be even better if
;;; we could interface to ispell.)  I'd be happy to be proved wrong.

(defsubst FM-string-to-char-list (string)
  "Return the character list of STRING.
If STRING is already a list, this function just returns STRING."
  (if (listp string) string (mapcar 'identity string)))

(defsubst FM-strings-to-char-lists (strings)
  "Return the character lists of STRINGS.
See `FM-string-to-char-list'."
 (mapcar 'FM-string-to-char-list strings))

(defsubst FM-char-list-to-string (charlist)
  "Return the string of CHARLIST.
If CHARLIST is not a list, this function just returns CHARLIST."
  (if (listp charlist) (mapconcat 'char-to-string charlist "") charlist))

(defsubst FM-char-lists-to-strings (charlists)
  "Return the strings of CHARLISTS.
See `FM-char-list-to-string'."
  (mapcar 'FM-char-list-to-string charlists))

(defsubst FM-strstr-intern (string1 string2)
  "Find first occurrence of a prefix of STRING1 in STRING2.
Returns a cons pair of the length of the substring and the offset into STRING2,
or nil if no match is found.
STRING1 and STRING2 are character lists."
  (let ((char1 (car string1))
        (offset 0) len)
    (while (and string2 (/= char1 (car string2)))
      (setq offset (1+ offset) string2 (cdr string2)))
    (if (null string2)
        nil
      (setq string1 (cdr string1) string2 (cdr string2) len 1)
      (while (and string1 string2 (= (car string1) (car string2)))
        (setq len (1+ len) string1 (cdr string1) string2 (cdr string2)))
      (cons len offset))))

(defsubst FM-matchiness-intern (string1 string2)
  "Return the fuzziness between STRING1 and STRING2.
STRING1 and STRING2 are character lists."
  (let ((fuzz 0) len offset s1 s2 c1)
    (while (and string1 string2)
      ;; This is (FM-strstr-intern string1 string2) incoded for speed.
      (setq c1 (car string1) s2 string2 offset 0)
      (while (and s2 (/= c1 (car s2)))          ; Where is c1 in s2?
        (setq offset (1+ offset) s2 (cdr s2)))
      (if (null s2)
          (setq string1 (cdr string1))
        (setq s1 (cdr string1) len 1)           ; How long is it in s2?
        (while (and s1 (setq s2 (cdr s2)) (= (car s1) (car s2)))
          (setq len (1+ len) s1 (cdr s1)))
        (if (< len offset)                      ; Is it regarded as a match?
            (setq string1 (cdr string1))
          (setq fuzz (+ fuzz len) string1 s1 string2 s2))))
    fuzz))

(defun FM-lessiness (string string1 string2)
  "Return non-nil if STRING1 is \"less\" than STRING2, based on STRING.
Comparison is based on the simularity:
- Between STRING and STRING1 and STRING2 (`FM-matchiness-intern').
- Between STRING and prefix length in STRING1 and STRING2 (`FM-strstr-intern').
- Between the length of STRING and STRING1 and STRING2.
- The offset of the first occurrence of a prefix in STRING1 and STRING2.
STRING, STRING1 and STRING2 can be character lists."
  (let* ((string (FM-string-to-char-list string))
         (string1 (FM-string-to-char-list string1))
         (string2 (FM-string-to-char-list string2))
         (fuzz1 (FM-matchiness-intern string string1))
         (fuzz2 (FM-matchiness-intern string string2)))
    (if (/= fuzz1 fuzz2)
        (> fuzz1 fuzz2)
      (let ((strstr1 (FM-strstr-intern string string1))
            (strstr2 (FM-strstr-intern string string2)))
        (cond ((or (null strstr1) (null strstr2)))
              ((/= (cdr strstr1) (cdr strstr2))
               (< (cdr strstr1) (cdr strstr2)))
              ((/= (length string1) (length string2))
               (< (length string1) (length string2)))
              (t (> (car strstr1) (car strstr2))))))))
 
;;; Useful functions...

(defun FM-matchiness (string1 string2)
  "Return the fuzziness between STRING1 and STRING2.
This provides a gauge of the number of characters of STRING1 in STRING2.
STRING1 and STRING2 can be character lists."
  (FM-matchiness-intern (FM-string-to-char-list string1)
                        (FM-string-to-char-list string2)))

(defun FM-closeness (string1 string2)
  "Return the closeness between STRING1 and STRING2.
This provides a gauge of the similarity of STRING1 and STRING2.
STRING1 and STRING2 can be character lists."
  (- (FM-matchiness-intern (FM-string-to-char-list string1)
                           (FM-string-to-char-list string2))
     (abs (- (length string1) (length string2)))))

(defun FM-all-fuzzy-matches (string strings)
  "Return most fuzzy matches to STRING in STRINGS.
Each element of STRINGS is tested to see if it fuzzily matches STRING.
The value is a list of all the strings from STRINGS that most fuzzily match.
The strings are fuzzily matched using `FM-matchiness'.
The list of fuzzy matches is sorted using `FM-fuzzy-sort'.
STRING and elements of STRINGS can be character lists."
  (let* ((string (FM-string-to-char-list string))
         (strings (FM-strings-to-char-lists strings))
         (bestfuzz (FM-matchiness-intern string (car strings)))
         (matches (list (car strings)))
         (strings (cdr strings))
         thisfuzz)
    (while strings
      (setq thisfuzz (FM-matchiness-intern string (car strings)))
      (cond ((= bestfuzz thisfuzz)
             (setq matches (cons (car strings) matches)))
            ((< bestfuzz thisfuzz)
             (setq bestfuzz thisfuzz
                   matches (list (car strings)))))
      (setq strings (cdr strings)))
    (and (not (zerop bestfuzz)) (FM-fuzzy-sort string matches))))

(defun FM-all-close-matches (string strings)
  "Return most close matches to STRING in STRINGS.
Each element of STRINGS is tested to see if it closely matches STRING.
The value is a list of all the strings from STRINGS that most closely match.
The strings are fuzzily matched using `FM-closeness'.
The list of close matches is sorted using `FM-fuzzy-sort'.
STRING and elements of STRINGS can be character lists."
  (let* ((bestfuzz (FM-closeness string (car strings)))
         (matches (list (car strings)))
         (strings (cdr strings))
         thisfuzz)
    (while strings
      (setq thisfuzz (FM-closeness string (car strings)))
      (cond ((= bestfuzz thisfuzz)
             (setq matches (cons (car strings) matches)))
            ((< bestfuzz thisfuzz)
             (setq bestfuzz thisfuzz
                   matches (list (car strings)))))
      (setq strings (cdr strings)))
    (FM-fuzzy-sort string matches)))

(defun FM-map-fuzzy-matches (string strings)
  "Return list of fuzzy matches to STRING in STRINGS.
Each element of the returned list is a cons pair of the form (string . fuzz)
where fuzz is the fuzzy match of string to STRING.  See `FM-matchiness'.
STRING and elements of STRINGS can be character lists."
  (let ((string (FM-string-to-char-list string)))
    (mapcar (function (lambda (str) (cons str (FM-matchiness string str))))
            strings)))

(defun FM-map-close-matches (string strings)
  "Return list of close matches to STRING in STRINGS.
Each element of the returned list is a cons pair of the form (string . close)
where close is the close match of string to STRING.  See `FM-closeness'.
STRING and elements of STRINGS can be character lists."
  (let ((string (FM-string-to-char-list string)))
    (mapcar (function (lambda (str) (cons str (FM-closeness string str))))
            strings)))

(defun FM-max-matchiness (string strings)
  "Return the maximum fuzzy matchiness of STRING in STRINGS.
STRING and elements of STRINGS can be character lists."
  (let ((string (FM-string-to-char-list string)))
    (apply 'max (mapcar (function (lambda (str) (FM-matchiness string str)))
                        strings))))

(defun FM-max-closeness (string strings)
  "Return the maximum closeness of STRING in STRINGS.
STRING and elements of STRINGS can be character lists."
  (let ((string (FM-string-to-char-list string)))
    (apply 'max (mapcar (function (lambda (str) (FM-closeness string str)))
                        strings))))

(defun FM-fuzzy-sort (string strings)
  "Return STRINGS fuzzily sorted based on STRING.
Sorting is done using `FM-lessiness' as predicate.
STRING and elements of STRINGS can be character lists."
  (let ((string (FM-string-to-char-list string))
        (strings (FM-strings-to-char-lists strings)))
    (FM-char-lists-to-strings
     (sort strings (function (lambda (string1 string2)
                               (FM-lessiness string string1 string2)))))))
 
;;;###autoload
(defun FM-offer-corrections (item candidates &optional prompt-p)
  "Offer corrections for ITEM from CANDIDATES.  Maybe replace ITEM.
If PROMPT-P is non-nil and there is only one candidate, ask the user before
replacing ITEM.  Replacement is performed by `replace-match'.
If more than one correction exists, call `FM-list-candidates' to display them.
Returns: nil if no correction was inserted.
         `sole' if corrected with the only correction match.
         `correct' if the only correction match is identical to ITEM.
         `listed' if a completion listing was shown."
  (interactive
   (let* ((symb (FM-symbol-name-before-point))
          (cands (and (not (string= "" symb))
                      (FM-all-fuzzy-matches
                       symb (all-completions (substring symb 0 1) obarray)))))
     (list symb cands current-prefix-arg)))
  (cond ((null candidates)
         (if (string= "" item)
             (message "No symbol before point to complete")
           (message "No candidates for `%s'" item))
         nil)
        ((> (length candidates) 1)      ; There's no unique correction.
         (FM-list-candidates candidates)
         'listed)
        (t
         (let ((candidate (car candidates)))
           (cond ((string= item candidate)
                  (message "Replacement is the same as `%s'" item)
                  'correct)
                 ((or (null prompt-p)
                      (y-or-n-p (format "Replace `%s' with `%s' " item candidate)))
                  (replace-match candidate t t)
                  (message "Replaced %s with %s" item candidate)
                  'sole)
                 (t
                  nil))))))

(defun FM-symbol-name-before-point ()
  "Return the symbol name before point or an empty string if no symbol."
  ;; Do it this way to avoid reading a symbol name,
  ;; which would create the symbol in obarray.
  (save-excursion
    (let* ((sym-chars "a-zA-Z0-9:_=<>/+-")
           (sym (concat "[" sym-chars "]"))
           (non-sym (concat "[^" sym-chars "]")) (limit (point)))
      (when (re-search-backward non-sym nil 'move) (forward-char 1))
      (if (or (eolp) (looking-at non-sym))
          ""
        (re-search-forward (concat sym "+") limit)
        (buffer-substring-no-properties (match-beginning 0) (match-end 0))))))

(defun FM-list-candidates (candidates)
  "List in help buffer CANDIDATES."
  (let ((conf (current-window-configuration)) (buf " *Candidates*"))
    (with-output-to-temp-buffer buf
      (display-completion-list candidates)
      (set-buffer buf)
      (forward-line 3)
      (while (search-backward "completion" nil 'move)
        (replace-match "candidate")))))
 
;;; Example code (see comment header):

;;;###autoload
(defun lisp-spell-symbol (prompt)
  "Perform spell checking on Lisp symbol preceding point.
With prefix arg(s) and only one candidate, ask the user before replacing.
With double prefix arg (\\[universal-argument] \\[universal-argument]), use \
`FM-all-fuzzy-matches' rather than
`FM-all-close-matches' to find Lisp symbol candidates.  This is useful if the
Lisp symbol stub is only partially complete.

To minimize matching effort and results, the first character of the
symbol is assumed to be correct.  See also `FM-offer-corrections'."
  (interactive "p")
  (let ((symbol (FM-symbol-name-before-point)))
    (if (string= "" symbol)
        (message "Not after a symbol")
      (let ((symbols (all-completions (substring symbol 0 1) obarray))
            (fuzzy-matcher (if (= prompt 16)
                               'FM-all-fuzzy-matches
                             'FM-all-close-matches)))
        (message "Checking symbol `%s'" symbol)
        (FM-offer-corrections symbol
                              (funcall fuzzy-matcher symbol symbols)
                              (/= prompt 1))))))
 

(provide 'fuzzy-match)

;;; fuzzy-match.el ends here
