
;;----------------------------------------------------------------------------;;
;; Customize                                                                  ;;
;;----------------------------------------------------------------------------;;

(eval-when-compile (require 'cl))
(require 'custom)

(defgroup tuareg2 nil
  "Support for the OCaml language."
  :group 'languages)

;; Comments

(defcustom tuareg2-indent-leading-comments t
  "*If true, indent leading comment lines (starting with `(*') like others."
  :group 'tuareg2 :type 'boolean)

(defcustom tuareg2-indent-comments t
  "*If true, automatically align multi-line comments."
  :group 'tuareg2 :type 'boolean)

(defcustom tuareg2-comment-end-extra-indent 0
  "*How many spaces to indent a leading comment end `*)'.
If you expect comments to be indented like
        (*
          ...
         *)
even without leading `*', use `tuareg2-comment-end-extra-indent' = 1."
  :group 'tuareg2
  :type '(radio :extra-offset 8
                :format "%{Comment End Extra Indent%}:
   Comment alignment:\n%v"
                (const :tag "align with `(' in comment opening" 0)
                (const :tag "align with `*' in comment opening" 1)
                (integer :tag "custom alignment" 0)))

(defcustom tuareg2-support-leading-star-comments t
  "*Enable automatic intentation of comments of the form
        (*
         * ...
         *)
Documentation comments (** *) are not concerned by this variable
unless `tuareg2-leading-star-in-doc' is also set.

If you do not set this variable and still expect comments to be
indented like
        (*
          ...
         *)
\(without leading `*'), set `tuareg2-comment-end-extra-indent' to 1."
  :group 'tuareg2 :type 'boolean)

(defcustom tuareg2-leading-star-in-doc nil
  "*Enable automatic intentation of documentation comments of the form
        (**
         * ...
         *)"
  :group 'tuareg2 :type 'boolean)

;; Indentation defaults

(defcustom tuareg2-default-indent 2
  "*Default indentation.

Global indentation variable (large values may lead to indentation overflows).
When no governing keyword is found, this value is used to indent the line
if it has to."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-let-always-indent t
  "*If true, enforce indentation is at least `tuareg2-let-indent' after a `let'.

As an example, set it to false when you have `tuareg2-with-indent' set to 0,
and you want `let x = match ... with' and `match ... with' indent the
same way."
  :group 'tuareg2 :type 'boolean)

(defcustom tuareg2-pipe-extra-unindent tuareg2-default-indent
  "*Extra backward indent for OCaml lines starting with the `|' operator.

It is NOT the variable controlling the indentation of the `|' itself:
this value is automatically added to `function', `with', `parse' and
some cases of `type' keywords to leave enough space for `|' backward
indentation.

For example, setting this variable to 0 leads to the following indentation:
  match ... with
    X -> ...
    | Y -> ...
    | Z -> ...

To modify the indentation of lines lead by `|' you need to modify the
indentation variables for `with', `function' and `parse', and possibly
for `type' as well. For example, setting them to 0 (and leaving
`tuareg2-pipe-extra-unindent' to its default value) yields:
  match ... with
    X -> ...
  | Y -> ...
  | Z -> ..."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-class-indent tuareg2-default-indent
  "*How many spaces to indent from a `class' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-sig-struct-align t
  "*Align `sig' and `struct' keywords with `module'."
  :group 'tuareg2 :type 'boolean)

(defcustom tuareg2-sig-struct-indent tuareg2-default-indent
  "*How many spaces to indent from a `sig' or `struct' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-method-indent tuareg2-default-indent
  "*How many spaces to indent from a `method' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-begin-indent tuareg2-default-indent
  "*How many spaces to indent from a `begin' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-for-while-indent tuareg2-default-indent
  "*How many spaces to indent from a `for' or `while' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-do-indent tuareg2-default-indent
  "*How many spaces to indent from a `do' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-fun-indent tuareg2-default-indent
  "*How many spaces to indent from a `fun' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-function-indent tuareg2-default-indent
  "*How many spaces to indent from a `function' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-if-then-else-indent tuareg2-default-indent
  "*How many spaces to indent from an `if', `then' or `else' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-let-indent tuareg2-default-indent
  "*How many spaces to indent from a `let' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-in-indent 0 ; tuareg2-default-indent
  "*How many spaces to indent from a `in' keyword.
Upstream <http://caml.inria.fr/resources/doc/guides/guidelines.en.html>
recommends 0, and this is what we default to since 2.0.1
instead of the historical `tuareg2-default-indent'."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-match-indent tuareg2-default-indent
  "*How many spaces to indent from a `match' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-try-indent tuareg2-default-indent
  "*How many spaces to indent from a `try' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-with-indent tuareg2-default-indent
  "*How many spaces to indent from a `with' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-rule-indent tuareg2-default-indent
  "*How many spaces to indent from a `rule' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-type-indent tuareg2-default-indent
  "*How many spaces to indent from a `type' keyword."
  :group 'tuareg2 :type 'integer)

(defcustom tuareg2-val-indent tuareg2-default-indent
  "*How many spaces to indent from a `val' keyword."
  :group 'tuareg2 :type 'integer)

(defgroup tuareg2-faces nil
  "Special faces for the Tuareg2 mode."
  :group 'tuareg2)

(defconst tuareg2-faces-inherit-p
  (and (boundp 'face-attribute-name-alist)
       (assq :inherit face-attribute-name-alist)))

(defface tuareg2-font-lock-governing-face
  '((((background light)) (:foreground "blue" :bold t))
    (t (:foreground "orange" :bold t)))
  "Face description for governing/leading keywords."
  :group 'tuareg2-faces)

(defvar tuareg2-font-lock-governing-face
  'tuareg2-font-lock-governing-face)

(defface tuareg2-font-lock-operator-face
  '((((background light)) (:foreground "brown"))
    (t (:foreground "khaki")))
  "Face description for all operators."
  :group 'tuareg2-faces)

(defvar tuareg2-font-lock-operator-face
  'tuareg2-font-lock-operator-face)

;;----------------------------------------------------------------------------;;
;; Util                                                                       ;;
;;----------------------------------------------------------------------------;;

(defun tuareg2-editing-ocamllex ()
  "Tells whether we are editing OCamlLex syntax."
  (string-match "\\.mll" (buffer-name)))

(defalias 'tuareg2-match-string 'match-string-no-properties)

(defun tuareg2-leading-star-p ()
  (and tuareg2-support-leading-star-comments
       (save-excursion ; this function does not make sense outside of a comment
         (tuareg2-beginning-of-literal-or-comment)
         (and (or tuareg2-leading-star-in-doc
                  (not (looking-at "(\\*[Tt][Ee][Xx]\\|(\\*\\*")))
              (progn
                (forward-line 1)
                (back-to-indentation)
                (looking-at "\\*[^)]"))))))

(defun tuareg2-auto-fill-insert-leading-star (&optional _leading-star)
  (save-excursion
    (back-to-indentation))
  nil)

(defun tuareg2-auto-fill-function ()
  (unless (tuareg2-in-literal-p)
    (let ((leading-star
           (and (not (char-equal ?\n last-command-event))
                (tuareg2-auto-fill-insert-leading-star))))
      (do-auto-fill)
      (unless (char-equal ?\n last-command-event)
        (tuareg2-auto-fill-insert-leading-star leading-star)))))

(defun tuareg2-forward-char (&optional step)
  "does not signal errors beginning-of-buffer and end-of-buffer"
  (if step (goto-char (+ (point) step))
    (goto-char (1+ (point)))))

(defun tuareg2-backward-char (&optional step)
  "does not signal errors beginning-of-buffer and end-of-buffer"
  (if step (goto-char (- (point) step))
    (goto-char (1- (point)))))

(defun tuareg2-in-indentation-p ()
  "Return non-nil if all chars between beginning of line and point are blanks."
  (save-excursion
    (skip-chars-backward " \t") 
    (bolp)))

(defun tuareg2-in-literal-p ()
  "Returns non-nil if point is inside an OCaml literal."
  (nth 3 (syntax-ppss)))

(defun tuareg2-in-comment-p ()
  "Returns non-nil if point is inside or right before an OCaml comment."
  (or (nth 4 (syntax-ppss))
      (looking-at "[ \t]*(\\*")))

(defun tuareg2-in-literal-or-comment-p ()
  "Returns non-nil if point is inside an OCaml literal or comment."
  (nth 8 (syntax-ppss)))

(defun tuareg2-beginning-of-literal-or-comment ()
  "Skips to the beginning of the current literal or comment (or buffer)."
  (interactive)
  (goto-char (or (nth 8 (syntax-ppss)) (point))))

(defun tuareg2-beginning-of-literal-or-comment-fast ()
  (goto-char (or (nth 8 (syntax-ppss)) (point-min))))

(defalias 'tuareg2-backward-up-list 'backward-up-list)

(defalias 'tuareg2-backward-up-list 'backward-up-list)

(defun tuareg2-false-=-p ()
  "Is the underlying `=' the first/second letter of an operator?"
  (or (memq (preceding-char) '(?: ?> ?< ?=))
      (char-equal ?= (char-after (1+ (point))))))

(defun tuareg2-at-phrase-break-p ()
  "Is the underlying `;' a phrase break?"
  (and (char-equal ?\; (following-char))
       (or (and (not (eobp))
                (char-equal ?\; (char-after (1+ (point)))))
           (char-equal ?\; (preceding-char)))))

;;----------------------------------------------------------------------------;;
;; Font lock                                                                  ;;
;;----------------------------------------------------------------------------;;

(defcustom tuareg2-font-lock-symbols nil
  "*Display fun and -> and such using symbols in fonts.
This may sound like a neat trick, but note that it can change the
alignment and can thus lead to surprises."
  :group 'tuareg2 :type 'boolean)

(defvar tuareg2-font-lock-symbols-alist
  (cond ((and (fboundp 'make-char) (fboundp 'charsetp) (charsetp 'symbol))
         `(("fun" . ,(make-char 'symbol 108))
           ("sqrt" . ,(make-char 'symbol 214))
           ("not" . ,(make-char 'symbol 216))
           ("&&" . ,(make-char 'symbol 217))
           ("or" . ,(make-char 'symbol 218))
           ("||" . ,(make-char 'symbol 218))
           ("*." . ,(make-char 'symbol 183))
           ("/." . ,(make-char 'symbol 184))
           ("<=" . ,(make-char 'symbol 163))
           ("<-" . ,(make-char 'symbol 172))
           ("->" . ,(make-char 'symbol 174))
           (">=" . ,(make-char 'symbol 179))
           ("<>" . ,(make-char 'symbol 185))
           ("==" . ,(make-char 'symbol 186))
           ("<=>" . ,(make-char 'symbol 219))
           (":=" . ,(make-char 'symbol 220))
           ("=>" . ,(make-char 'symbol 222))
           ("infinity" . ,(make-char 'symbol 165))
           ;; Some greek letters for type parameters.
           ("'a" . ,(make-char 'symbol 97))
           ("'b" . ,(make-char 'symbol 98))
           ("'c" . ,(make-char 'symbol 103)) ; sic! 99 is chi, 103 is gamma
           ("'d" . ,(make-char 'symbol 100))
           ("'e" . ,(make-char 'symbol 101))
           ("'f" . ,(make-char 'symbol 102))
           ("'i" . ,(make-char 'symbol 105))
           ("'k" . ,(make-char 'symbol 107))
           ("'m" . ,(make-char 'symbol 109))
           ("'n" . ,(make-char 'symbol 110))
           ("'o" . ,(make-char 'symbol 111))
           ("'p" . ,(make-char 'symbol 112))
           ("'r" . ,(make-char 'symbol 114))
           ("'s" . ,(make-char 'symbol 115))
           ("'t" . ,(make-char 'symbol 116))
           ("'x" . ,(make-char 'symbol 120))))
        ((fboundp 'decode-char) ;; or a unicode font.
         `(("fun" . ,(decode-char 'ucs 955))
           ("sqrt" . ,(decode-char 'ucs 8730))
           ("not" . ,(decode-char 'ucs 172))
           ("&&" . ,(decode-char 'ucs 8896))
           ("or" . ,(decode-char 'ucs 8897))
           ("||" . ,(decode-char 'ucs 8897))
           ("*." . ,(decode-char 'ucs 215))
           ("/." . ,(decode-char 'ucs 247))
           ("->" . ,(decode-char 'ucs 8594))
           ("<-" . ,(decode-char 'ucs 8592))
           ("<=" . ,(decode-char 'ucs 8804))
           (">=" . ,(decode-char 'ucs 8805))
           ("<>" . ,(decode-char 'ucs 8800))
           ("==" . ,(decode-char 'ucs 8801))
           ("<=>" . ,(decode-char 'ucs 8660))
           (":=" . ,(decode-char 'ucs 8656))
           ("infinity" . ,(decode-char 'ucs 8734))
           ;; Some greek letters for type parameters.
           ("'a" . ,(decode-char 'ucs 945))
           ("'b" . ,(decode-char 'ucs 946))
           ("'c" . ,(decode-char 'ucs 947))
           ("'d" . ,(decode-char 'ucs 948))
           ("'e" . ,(decode-char 'ucs 949))
           ("'f" . ,(decode-char 'ucs 966))
           ("'i" . ,(decode-char 'ucs 953))
           ("'k" . ,(decode-char 'ucs 954))
           ("'m" . ,(decode-char 'ucs 956))
           ("'n" . ,(decode-char 'ucs 957))
           ("'o" . ,(decode-char 'ucs 969))
           ("'p" . ,(decode-char 'ucs 960))
           ("'r" . ,(decode-char 'ucs 961))
           ("'s" . ,(decode-char 'ucs 963))
           ("'t" . ,(decode-char 'ucs 964))
           ("'x" . ,(decode-char 'ucs 958))))))

(defun tuareg2-font-lock-compose-symbol (alist)
  "Compose a sequence of ascii chars into a symbol.
Regexp match data 0 points to the chars."
  ;; Check that the chars should really be composed into a symbol.
  (let* ((mbegin (match-beginning 0))
         (mend (match-end 0))
         (syntax (char-syntax (char-after mbegin))))
    (if (or (eq (char-syntax (or (char-before mbegin) ?\ )) syntax)
            (eq (char-syntax (or (char-after mend) ?\ )) syntax)
            (memq (get-text-property mbegin 'face)
                  '(tuareg2-doc-face font-lock-string-face
                    font-lock-comment-face)))
        ;; No composition for you. Let's actually remove any composition
        ;;   we may have added earlier and which is now incorrect.
        (remove-text-properties mbegin mend '(composition))
      ;; That's a symbol alright, so add the composition.
      (compose-region mbegin mend (cdr (assoc (match-string 0) alist)))))
  ;; Return nil because we're not adding any face property.
  nil)

(defun tuareg2-font-lock-symbols-keywords ()
  (when (fboundp 'compose-region)
    (let ((alist nil))
      (dolist (x tuareg2-font-lock-symbols-alist)
        (when (and (if (fboundp 'char-displayable-p)
                       (char-displayable-p (cdr x))
                     t)
                   (not (assoc (car x) alist))) ; not yet in alist.
          (push x alist)))
      (when alist
        `((,(regexp-opt (mapcar 'car alist) t)
           (0 (tuareg2-font-lock-compose-symbol ',alist))))))))

(defvar tuareg2-doc-face 'font-lock-doc-face)

(defconst tuareg2-font-lock-syntactic-keywords
  ;; Char constants start with ' but ' can also appear in identifiers.
  ;; Beware not to match things like '*)hel' or '"hel' since the first '
  ;; might be inside a string or comment.
  '(("\\<\\('\\)\\([^'\\\n]\\|\\\\.[^\\'\n \")]*\\)\\('\\)"
     (1 '(7)) (3 '(7)))))

(defun tuareg2-font-lock-syntactic-face-function (state)
  (if (nth 3 state) font-lock-string-face
    (let ((start (nth 8 state)))
      (if (and (> (point-max) (+ start 2))
               (eq (char-after (+ start 2)) ?*)
               (not (eq (char-after (+ start 3)) ?*)))
          ;; This is a documentation comment
          tuareg2-doc-face
        font-lock-comment-face))))

;; Initially empty, set in `tuareg2-install-font-lock'
(defvar tuareg2-font-lock-keywords ()
  "Font-Lock patterns for Tuareg2 mode.")

(defconst tuareg2-font-lock-syntax
  `((?_ . "w") (?` . "."))
  "Syntax changes for Font-Lock.")

(defun tuareg2-install-font-lock ()
  (setq
   tuareg2-font-lock-keywords
   `(("\\<\\(external\\|open\\|include\\|rule\\|s\\(ig\\|truct\\)\\|module\\|functor\\|with[ \t\n]+\\(type\\|module\\)\\|val\\|type\\|method\\|virtual\\|constraint\\|class\\|in\\|inherit\\|initializer\\|let\\|rec\\|object\\|and\\|begin\\|end\\)\\>"
      0 tuareg2-font-lock-governing-face nil nil)
     ("\\<\\(false\\|true\\)\\>" 0 font-lock-constant-face nil nil)
     ("\\<\\(as\\|do\\(ne\\|wnto\\)?\\|else\\|for\\|if\\|mutable\\|new\\|p\\(arser\\|rivate\\)\\|t\\(hen\\|o\\|ry\\)\\|wh\\(en\\|ile\\)\\|match\\|with\\|lazy\\|exception\\|raise\\|failwith[f]?\\|exit\\|assert\\|fun\\(ction\\)?\\)\\>"
      0 font-lock-keyword-face nil nil)
     ("\\<method\\([ \t\n]+\\(private\\|virtual\\)\\)?\\>[ \t\n]*\\(\\(\\w\\|[_,?~.]\\)*\\)"
      3 font-lock-function-name-face keep nil)
     ("\\<\\(fun\\(ction\\)?\\)\\>[ \t\n]*\\(\\(\\w\\|[_ \t()*,]\\)+\\)"
      3 font-lock-variable-name-face keep nil)
     ( "\\<\\(open\\|\\(class\\([ \t\n]+type\\)?\\)\\([ \t\n]+virtual\\)?\\|inherit\\|include\\|module\\([ \t\n]+\\(type\\|rec\\)\\)?\\|type\\)\\>[ \t\n]*\\(['~?]*\\([_--->.* \t]\\|\\w\\|(['~?]*\\([_--->.,* \t]\\|\\w\\)*)\\)*\\)"
           7 font-lock-type-face keep nil)
     ("[^:>=]:[ \t\n]*\\(['~?]*\\([_--->.* \t]\\|\\w\\|(['~?]*\\([_--->.,* \t]\\|\\w\\)*)\\)*\\)"
      1 font-lock-type-face keep nil)
     ("\\<\\([A-Z]\\w*\\>\\)[ \t]*\\." 1 font-lock-type-face keep nil)
     ("\\<\\([?~]?[_[:alpha:]]\\w*\\)[ \t\n]*:[^:>=]"
      1 font-lock-variable-name-face keep nil)
     ("\\<exception\\>[ \t\n]*\\(\\<[_[:alpha:]]\\w*\\>\\)"
      1 font-lock-variable-name-face keep nil)
     ("^#\\w+\\>" 0 font-lock-preprocessor-face t nil)
     ,@(and tuareg2-font-lock-symbols
            (tuareg2-font-lock-symbols-keywords))))
  (setq font-lock-defaults
        (list
         'tuareg2-font-lock-keywords nil nil
         tuareg2-font-lock-syntax nil
         '(font-lock-syntactic-keywords
           . tuareg2-font-lock-syntactic-keywords)
         '(parse-sexp-lookup-properties
           . t)
         '(font-lock-syntactic-face-function
           . tuareg2-font-lock-syntactic-face-function))))

;;----------------------------------------------------------------------------;;
;; Abbrev table                                                               ;;
;;----------------------------------------------------------------------------;;

(defvar tuareg2-mode-abbrev-table ()
  "Abbrev table used for Tuareg2 mode buffers.")

(defun tuareg2-define-abbrev (keyword)
  (define-abbrev tuareg2-mode-abbrev-table keyword keyword 'tuareg2-abbrev-hook))

(if tuareg2-mode-abbrev-table ()
  (setq tuareg2-mode-abbrev-table (make-abbrev-table))
  (mapc 'tuareg2-define-abbrev
        '("module" "class" "functor" "object" "type" "val" "inherit"
          "include" "virtual" "constraint" "exception" "external" "open"
          "method" "and" "initializer" "to" "downto" "do" "done" "else"
          "begin" "end" "let" "in" "then" "with"))
  (setq abbrevs-changed nil))

;;----------------------------------------------------------------------------;;
;; Indentation                                                                ;;
;;----------------------------------------------------------------------------;;

(defconst tuareg2-no-more-code-this-line-regexp "[ \t]*\\((\\*\\|$\\)"
    "Regexp matching lines which have no more code:
 blanks + (maybe) comment start.")

(defun tuareg2-no-code-after (rex)
  (concat rex tuareg2-no-more-code-this-line-regexp))

(defconst tuareg2-no-code-this-line-regexp
  (concat "^" tuareg2-no-more-code-this-line-regexp))

(defun tuareg2-ro (&rest words) (concat "\\<" (regexp-opt words t) "\\>"))

(defconst tuareg2-extra-unindent-regexp
  (concat "\\(" (tuareg2-ro "with" "fun" "function" "parse")
          "\\|\\[" tuareg2-no-more-code-this-line-regexp "\\)")
  "Regexp for keywords needing extra indentation to compensate for case matches.")

(defun tuareg2-extra-unindent-regexp ()
  tuareg2-extra-unindent-regexp)

(defconst tuareg2-keyword-regexp
  (concat (tuareg2-ro 
           "and"
           "as"
           "assert"
           "begin"
           "class"
           "constraint"
           "do"
           "done"
           "downto"
           "else"
           "end"
           "exception"
           "external"
           "for"
           "fun"
           "function"
           "functor"
           "if"
           "in"
           "include"
           "inherit"
           "initializer"
           "lazy"
           "let"
           "match"
           "method"
           "module"
           "mutable"
           "new"
           "object"
           "of"
           "open"
           "or"
           "private"
           "rec"
           "sig"
           "struct"
           "then"
           "to"
           "true"
           "try"
           "type"
           "val"
           "virtual"
           "when"
           "while"
           "with"
           ;; infix
           "mod"
           "land"
           "lor"
           "lxor"
           "lsl"
           "lsr"
           "asr"
           )
          "\\|->\\|[;,|]")
  "Regexp for all recognized keywords.  See parsing/lexer.mll in the ocaml source.")

(defun tuareg2-keyword-regexp ()
  tuareg2-keyword-regexp)

(defconst tuareg2-match-pipe-kwop-regexp
  (concat (tuareg2-ro "and" "function" "type" "with" "parse" )
          "\\|[[({=]\\||[^!]")
  "Regexp for keywords supporting case match.")

(defun tuareg2-match-pipe-kwop-regexp ()
  tuareg2-match-pipe-kwop-regexp)

(defconst tuareg2-operator-regexp "[---+*/=<>@^&|]\\|:>\\|::\\|\\<\\(or\\|l\\(and\\|x?or\\|s[lr]\\)\\|as[lr]\\|mod\\)\\>"
  "Regexp for all operators.")

(defun tuareg2-operator-regexp ()
  tuareg2-operator-regexp)

(defconst tuareg2-matching-keyword-regexp
  (tuareg2-ro "and" "do" "done" "then" "else" "end" "in" "down" "downto")
  "Regexp matching OCaml keywords which act as end block delimiters.")

(defun tuareg2-matching-keyword-regexp ()
  tuareg2-matching-keyword-regexp)

(defconst tuareg2-matching-kwop-regexp
  (concat tuareg2-matching-keyword-regexp
          "\\|\\<with\\>\\|[|>]?\\]\\|>?}\\|[|)]\\|;;")
  "Regexp matching OCaml keywords or operators which act as end block
delimiters.")

(defun tuareg2-matching-kwop-regexp ()
  tuareg2-matching-kwop-regexp)

(defconst tuareg2-block-regexp
  (concat (tuareg2-ro "for" "while" "do" "if" "begin" "sig" "struct" "object")
          "\\|[][(){}]\\|\\*)"))

(defun tuareg2-block-regexp ()
  tuareg2-block-regexp)

(defconst tuareg2-find-kwop-regexp
  (concat tuareg2-matching-keyword-regexp "\\|" tuareg2-block-regexp))

(defun tuareg2-find-kwop-regexp ()
  tuareg2-find-kwop-regexp)

(defconst tuareg2-governing-phrase-regexp
  (tuareg2-ro "val" "type" "method" "module" "constraint" "class" "inherit"
             "initializer" "external" "exception" "open" "let" "object"
             "include")
  "Regexp matching tuareg2 phrase delimitors.")

(defun tuareg2-governing-phrase-regexp ()
  tuareg2-governing-phrase-regexp)

(defconst tuareg2-keyword-alist
  '(("module" . tuareg2-default-indent)
    ("class" . tuareg2-class-indent)
    ("sig" . tuareg2-sig-struct-indent)
    ("struct" . tuareg2-sig-struct-indent)
    ("method" . tuareg2-method-indent)
    ("object" . tuareg2-begin-indent)
    ("begin" . tuareg2-begin-indent)
    (".<" . tuareg2-begin-indent)
    ("for" . tuareg2-for-while-indent)
    ("while" . tuareg2-for-while-indent)
    ("do" . tuareg2-do-indent)
    ("val" . tuareg2-val-indent)
    ("fun" . tuareg2-fun-indent)
    ("if" . tuareg2-if-then-else-indent)
    ("then" . tuareg2-if-then-else-indent)
    ("else" . tuareg2-if-then-else-indent)
    ("let" . tuareg2-let-indent)
    ("match" . tuareg2-match-indent)
    ("try" . tuareg2-try-indent)
    ("rule" . tuareg2-rule-indent)

    ;; Case match keywords
    ("function" . tuareg2-function-indent)
    ("with" . tuareg2-with-indent)
    ("parse" . tuareg2-with-indent)
    ("automaton" . tuareg2-with-indent)
    ("present" . tuareg2-with-indent)
    ("type" . tuareg2-type-indent) ; sometimes, `type' acts like a case match

    ;; Assume default indentation for other keywords and operators
    )
  "Association list of indentation values based on governing keywords.")

(defconst tuareg2-leading-kwop-alist
  '(("|" . tuareg2-find-pipe-match)
    ("}" . tuareg2-find-match)
    (">}" . tuareg2-find-match)
    (">." . tuareg2-find-match)
    (")" . tuareg2-find-match)
    ("]" . tuareg2-find-match)
    ("|]" . tuareg2-find-match)
    (">]" . tuareg2-find-match)
    ("end" . tuareg2-find-match)
    ("done" . tuareg2-find-done-match)
    ("unless" . tuareg2-find-done-match)
    ("until" . tuareg2-find-done-match)
    ("every" . tuareg2-find-done-match)
    ("in" . tuareg2-find-in-match)
    ("where" . tuareg2-find-in-match)
    ("with" . tuareg2-find-with-match)
    ("else" . tuareg2-find-else-match)
    ("then" . tuareg2-find-then-match)
    ("do" . tuareg2-find-do-match)
    ("to" . tuareg2-find-match)
    ("downto" . tuareg2-find-match)
    ("and" . tuareg2-find-and-match))
  "Association list used in Tuareg2 mode for skipping back over nested blocks.")

(defun tuareg2-find-leading-kwop-match (kwop)
  (funcall (cdr (assoc kwop tuareg2-leading-kwop-alist))))

(defconst tuareg2-binding-regexp "\\(\\<and\\>\\|(*\\<let\\>\\)")

(defun tuareg2-assoc-indent (kwop &optional look-for-let-or-and)
  "Return relative indentation of the keyword given in argument."
  (let ((ind (or (symbol-value (cdr (assoc kwop tuareg2-keyword-alist)))
                 tuareg2-default-indent))
        (looking-let-or-and (and look-for-let-or-and
                                 (looking-at tuareg2-binding-regexp))))
    (if (string-match (tuareg2-extra-unindent-regexp) kwop)
        (- (if (and tuareg2-let-always-indent
                    looking-let-or-and (< ind tuareg2-let-indent))
               tuareg2-let-indent ind)
           tuareg2-pipe-extra-unindent)
      ind)))

(defun tuareg2-in-monadic-op-p (&optional pos)
  (unless pos (setq pos (point)))
  (and (char-equal ?> (char-before pos))
       (char-equal ?> (char-before (1- pos)))))

(defconst tuareg2-meaningful-word-regexp
  "[^ \t\n_[:alnum:]]\\|\\<\\(\\w\\|_\\)+\\>\\|\\*)")

(defun tuareg2-find-meaningful-word ()
  "Look back for a word, skipping comments and blanks.
Returns the actual text of the word, if found."
  (let ((found nil) (kwop nil) (pt (point)))
    (while (and (not found)
                (re-search-backward tuareg2-meaningful-word-regexp
                                    (point-min) t))
      (setq kwop (tuareg2-match-string 0))
      (cond ((and (or (string= kwop "|") (string= kwop "=") (string= kwop ">"))
                  (tuareg2-in-monadic-op-p))
             (backward-char 2)
             (setq kwop (concat ">>" kwop)))
            ((and (string= kwop ">") (char-equal ?- (char-before)))
             (backward-char)
             (setq kwop "->")))
      (when (= pt (point))
        (error "tuareg2-find-meaningful-word: inf loop at %d, kwop=%s" pt kwop))
      (setq pt (point))
      (if kwop
          (if (tuareg2-in-comment-p)
              (tuareg2-beginning-of-literal-or-comment-fast)
            (setq found t))
        (setq found t)))
    (if found kwop (goto-char (point-min)) nil)))

(defun tuareg2-make-find-kwop-regexp (kwop-regexp)
  "Make a custom indentation regexp."
  (concat (tuareg2-find-kwop-regexp) "\\|" kwop-regexp))

;; Static regexps
(defconst tuareg2-find-and-match-regexp
  (concat (tuareg2-ro "do" "done" "else" "end" "in" "then" "down" "downto"
                     "for" "while" "do" "if" "begin" "sig" "struct" "class"
                     "rule" "exception" "let" "in" "type" "val" "module")
          "\\|[][(){}]\\|\\*)"))
(defconst tuareg2-find-phrase-beginning-regexp
  (concat (tuareg2-ro "end" "type" "module" "sig" "struct" "class"
                     "exception" "open" "let")
          "\\|^#[ \t]*[a-z][_a-z]*\\>\\|;;"))
(defconst tuareg2-find-phrase-beginning-and-regexp
  (concat "\\<\\(and\\)\\>\\|" tuareg2-find-phrase-beginning-regexp))
(defconst tuareg2-back-to-paren-or-indentation-regexp
  "[][(){}]\\|\\.<\\|>\\.\\|\\*)\\|^[ \t]*\\(.\\|\n\\)")

;; Specific regexps for module/class detection
(defconst tuareg2-inside-module-or-class-opening
  (tuareg2-ro "struct" "sig" "object"))
(defconst tuareg2-inside-module-or-class-opening-full
  (concat tuareg2-inside-module-or-class-opening "\\|"
          (tuareg2-ro "module" "class")))
(defconst tuareg2-inside-module-or-class-regexp
  (concat tuareg2-matching-keyword-regexp "\\|"
          tuareg2-inside-module-or-class-opening))

(defconst tuareg2-find-comma-match-regexp
  (tuareg2-make-find-kwop-regexp
   (concat (tuareg2-ro "and" "match" "begin" "else" "exception" "then" "try"
                       "with" "or" "fun" "function" "let" "do")
           "\\|->\\|[[{(]")))

(defconst tuareg2-find-with-match-regexp
  (tuareg2-make-find-kwop-regexp
   (concat (tuareg2-ro "match" "try" "module" "begin" "with" "type")
           "\\|[[{(]")))

(defconst tuareg2-find-in-match-regexp
  ;;(tuareg2-make-find-kwop-regexp (tuareg2-ro "let" "open")))
  (tuareg2-make-find-kwop-regexp (tuareg2-ro "let")))

(defconst tuareg2-find-else-match-regexp
  (tuareg2-make-find-kwop-regexp ";"))

(defconst tuareg2-find-do-match-regexp
  (tuareg2-make-find-kwop-regexp "->"))

(defconst tuareg2-find-=-match-regexp
  (tuareg2-make-find-kwop-regexp
   (concat (tuareg2-ro "val" "let" "method" "module" "type" "class" "when"
                       "if" "in" "do")
           "\\|=")))

(defconst tuareg2-find-pipe-match-regexp
  (tuareg2-make-find-kwop-regexp (tuareg2-match-pipe-kwop-regexp)))

(defconst tuareg2-find-arrow-match-regexp
  (tuareg2-make-find-kwop-regexp
   (concat (tuareg2-ro "external" "type" "val" "method" "let" "with" "fun"
                       "function" "functor" "class")
           "\\|[|;]")))

(defconst tuareg2-find-semicolon-match-regexp
  (tuareg2-make-find-kwop-regexp
   (concat ";" tuareg2-no-more-code-this-line-regexp "\\|->\\|"
           (tuareg2-ro "let" "method" "with" "try" "initializer"))))

(defconst tuareg2-find-phrase-indentation-regexp
  (tuareg2-make-find-kwop-regexp
   (concat tuareg2-governing-phrase-regexp "\\|" (tuareg2-ro "and"))))

(defconst tuareg2-find-phrase-indentation-break-regexp
  (concat tuareg2-find-phrase-indentation-regexp "\\|;;"))

(defconst tuareg2-find-phrase-indentation-class-regexp
  (concat (tuareg2-matching-keyword-regexp) "\\|\\<class\\>"))

(defconst tuareg2-compute-argument-indent-regexp
  (tuareg2-make-find-kwop-regexp
   (concat (tuareg2-keyword-regexp) "\\|=")))

(defconst tuareg2-compute-normal-indent-regexp
  (concat tuareg2-compute-argument-indent-regexp "\\|^.[ \t]*"))

(defconst tuareg2-find-module-regexp
  (tuareg2-make-find-kwop-regexp "\\<module\\>"))

(defconst tuareg2-find-pipe-bang-match-regexp
  (concat tuareg2-find-comma-match-regexp "\\|="))

(defconst tuareg2-find-monadic-match-regexp
  (concat tuareg2-block-regexp "\\|\\([;=]\\)\\|\\(->\\)\\|"
          (tuareg2-ro "val" "let" "method" "module" "type" "class" "when"
                      "if" "in" "do" "done" "end")))

(defun tuareg2-strip-trailing-whitespace (string)
  (if (string-match "[ \t]*\\'" string)
      (substring string 0 (match-beginning 0))
    string))

(defun tuareg2-find-kwop-pos (kr do-not-skip-regexp may-terminate-early)
  "Look back for a keyword or operator matching KR (short for kwop regexp).
Skips blocks etc...

Ignore occurences inside literals and comments.
If found, return the actual text of the keyword or operator."
  (let ((found nil)
        (kwop nil) pos
        (kwop-regexp kr))
    (while (and (not found)
                (setq pos (re-search-backward kwop-regexp (point-min) t))
                (setq kwop (tuareg2-strip-trailing-whitespace
                            ;; for trailing blanks after a semicolon
                            (tuareg2-match-string 0))))
      (cond
       ((tuareg2-in-literal-or-comment-p)
        (tuareg2-beginning-of-literal-or-comment-fast))
       ((looking-at "[]})]")
        (tuareg2-backward-up-list))
       ((tuareg2-at-phrase-break-p)
        (setq found t))
       ((and do-not-skip-regexp (looking-at do-not-skip-regexp))
        (if (and (string= kwop "|") (char-equal ?| (preceding-char)))
            (backward-char)
          (setq found t)))
       ((looking-at (tuareg2-matching-keyword-regexp))
        (let ((mkwop (tuareg2-find-leading-kwop-match (tuareg2-match-string 0))))
          (when (and may-terminate-early (string-match kwop-regexp mkwop))
            (setq found t))))
       (t
        (setq found t))))
    (if found (list kwop pos) (goto-char (point-min)) nil)))

(defun tuareg2-find-kwop (kr &optional do-not-skip-regexp)
  (car (tuareg2-find-kwop-pos kr do-not-skip-regexp nil)))

(defun tuareg2-find-match ()
  (let ((kwop (tuareg2-find-kwop (tuareg2-find-kwop-regexp))))
    (when (string= kwop "then")
      (tuareg2-find-then-match)
      (tuareg2-find-match))
    kwop))

(defun tuareg2-find-comma-match ()
  (car (tuareg2-find-kwop-pos tuareg2-find-comma-match-regexp nil t)))

(defun tuareg2-find-pipe-bang-match ()
  (destructuring-bind (kwop pos)
      (tuareg2-find-kwop-pos tuareg2-find-pipe-bang-match-regexp nil t)
    ;; when matched "if ... then", kwop is "then" but point is at "if"
    (goto-char pos)   ; go back to kwop for tuareg2-indent-to-code
    (if (looking-at "\\[|") "[|" kwop)))

(defun tuareg2-monadic-operator-p (word)
  (and (or (string= ">>=" word) (string= ">>|" word) (string= ">>>" word))
       word))

(defun tuareg2-ignorable-arrow-p ()
  (save-excursion
    (or (tuareg2-monadic-operator-p (tuareg2-find-arrow-match))
        (looking-at (tuareg2-extra-unindent-regexp)))))

(defun tuareg2-find-monadic-match ()
  (let (kwop)
    (while (or (null kwop)
               (and (string= kwop "=") (tuareg2-in-monadic-op-p)))
      (when kwop (tuareg2-backward-char 2))
      (setq kwop (tuareg2-find-kwop tuareg2-find-monadic-match-regexp))
      (when (and (string= kwop "->") (tuareg2-ignorable-arrow-p))
        (setq kwop nil)))
    kwop))

(defun tuareg2-find-with-match ()
  (tuareg2-find-kwop tuareg2-find-with-match-regexp))

(defun tuareg2-find-in-match ()
  (let ((kwop (tuareg2-find-kwop tuareg2-find-in-match-regexp "\\<and\\>")))
    (cond
     ((string= kwop "and")
      (tuareg2-find-in-match))
     (t
      kwop))))

(defconst tuareg2-find-then-match-regexp
  (tuareg2-make-find-kwop-regexp "\\(->\\)"))

(defun tuareg2-find-then-kwop ()
  (tuareg2-find-kwop tuareg2-find-then-match-regexp))

(defun tuareg2-find-then-match ()
  (let ((kwop (tuareg2-find-then-kwop)))
    (cond ((string= kwop "if")
           (let ((back (point)))
             (tuareg2-back-to-paren-or-indentation)
             (if (looking-at "else[ \t]*\\((\\*.*\\*)\\)*[ \t]*if")
                 "else if"
               (goto-char back)
               kwop)))
          (t kwop))))

(defun tuareg2-find-then-else-match ()
  (let ((kwop (tuareg2-find-then-kwop)))
    (cond
     ((string= kwop "if")
      (let ((pos (point)))
        (if (and (not (tuareg2-in-indentation-p))
                 (string= "else" (tuareg2-find-meaningful-word)))
            "else"
          (goto-char pos)
          kwop)))
     (t
      kwop))))

(defun tuareg2-find-else-match ()
  (let ((kwop (tuareg2-find-kwop tuareg2-find-else-match-regexp
                                "\\<then\\>")))
    (cond
     ((string= kwop "then")
      (tuareg2-find-then-else-match))
     ((string= kwop ";")
      (tuareg2-find-semicolon-match)
      (tuareg2-find-else-match)))))

(defconst tuareg2-do-match-stop-regexp (tuareg2-ro "down" "downto"))

(defun tuareg2-find-do-match ()
  (let ((kwop (tuareg2-find-kwop tuareg2-find-do-match-regexp
                                tuareg2-do-match-stop-regexp)))
    (if (or (string= kwop "to") (string= kwop "downto"))
        (tuareg2-find-match)
      kwop)))

(defconst tuareg2-done-match-stop-regexp (tuareg2-ro "and" "do"))

(defun tuareg2-find-done-match ()
  (let ((kwop (tuareg2-find-kwop (tuareg2-find-kwop-regexp)
                                tuareg2-done-match-stop-regexp)))
    (cond
     ((string= kwop "and")
      (tuareg2-find-and-match))
     ((string= kwop "done")
      (tuareg2-find-done-match)
      (tuareg2-find-done-match))
     ((string= kwop "do")
      (tuareg2-find-do-match))
     (t
      kwop))))

(defun tuareg2-and-stop-regexp ()
  "\\<and\\>")
  
(defun tuareg2-find-and-match ()
  (let* ((kwop (tuareg2-find-kwop
                tuareg2-find-and-match-regexp
                (tuareg2-and-stop-regexp)))
         (old-point (point)))
    (cond
     ((or (string= kwop "type") (string= kwop "module"))
      (let ((kwop2 (tuareg2-find-meaningful-word)))
        (cond ((string= kwop2 "with")
               kwop2)
              ((string= kwop2 "and")
               (tuareg2-find-and-match))
              ((and (string= kwop "module")
                    (string= kwop2 "let"))
               kwop2)
              (t (goto-char old-point) kwop))))
     (t kwop))))

(defconst tuareg2-=-stop-regexp (concat (tuareg2-ro "and" "in") "\\|="))

(defun tuareg2-=-stop-regexp ()
  tuareg2-=-stop-regexp)

(defun tuareg2-find-=-match ()
  (let ((kwop (tuareg2-find-kwop
               tuareg2-find-=-match-regexp
               (tuareg2-=-stop-regexp))))
    (cond
     ((string= kwop "and")
      (tuareg2-find-and-match))
     ((and (string= kwop "=")
           (not (tuareg2-false-=-p)))
      (while (and (string= kwop "=")
                  (not (tuareg2-false-=-p)))
        (setq kwop (tuareg2-find-=-match)))
      kwop)
     (t kwop))))

(defconst tuareg2-if-when-regexp (tuareg2-ro "if" "when"))

(defun tuareg2-if-when-= ()
  (save-excursion
    (tuareg2-find-=-match)
    (looking-at tuareg2-if-when-regexp)))

(defconst tuareg2-captive-regexp
  (tuareg2-ro "let" "if" "when" "module" "type" "class"))

(defun tuareg2-captive-= ()
  (save-excursion
    (tuareg2-find-=-match)
    (looking-at tuareg2-captive-regexp)))

(defconst tuareg2-pipe-stop-regexp
  (concat (tuareg2-ro "and" "with") "\\||"))

(defun tuareg2-pipe-stop-regexp ()
  tuareg2-pipe-stop-regexp)

(defun tuareg2-find-pipe-match ()
  (let ((kwop
         (let ((k (tuareg2-find-kwop
                   tuareg2-find-pipe-match-regexp
                   (tuareg2-pipe-stop-regexp))))
           (if (and k (string-match "|[^!]" k))
               "|" k)))
        (old-point (point)))
    (cond
     ((string= kwop "and")
      (setq old-point (point))
      (setq kwop (tuareg2-find-and-match))
      (if (not (string= kwop "do"))
          (goto-char old-point)
        (setq kwop (tuareg2-find-arrow-match)))
      kwop)
     ((and (string= kwop "|")
           (looking-at "|[^|]")
           (tuareg2-in-indentation-p))
      kwop)
     ((string= kwop "|") (tuareg2-find-pipe-match))
     ((and (string= kwop "=")
           (or (looking-at (tuareg2-no-code-after "="))
               (tuareg2-false-=-p)
               (not (string= (save-excursion (tuareg2-find-=-match))
                             "type"))))
      (tuareg2-find-pipe-match))
     ((string= kwop "parse")
      (if (and (tuareg2-editing-ocamllex)
               (save-excursion
                 (string= (tuareg2-find-meaningful-word) "=")))
          kwop
        (tuareg2-find-pipe-match)))
     (t
      kwop))))

(defun tuareg2-find-arrow-match ()
  (let ((kwop (tuareg2-find-kwop tuareg2-find-arrow-match-regexp
                                "\\<with\\>")))
    (cond
     ((string= kwop "|")
      (if (tuareg2-in-indentation-p)
          kwop
        (progn (forward-char -1) (tuareg2-find-arrow-match))))
     ((string= kwop "fun")
      (let ((pos (point)))
        (or (tuareg2-monadic-operator-p (tuareg2-find-meaningful-word))
            (progn (goto-char pos) kwop))))
     ((not (string= kwop ":"))
      kwop)
     ;; If we get this far, we know we're looking at a colon.
     ((or (char-equal (char-before) ?:)
          (char-equal (char-after (1+ (point))) ?:)
          (char-equal (char-after (1+ (point))) ?>))
      (tuareg2-find-arrow-match))
     ;; Patch by T. Freeman
     (t
      (let ((oldpoint (point))
            (match (tuareg2-find-arrow-match)))
        (if (looking-at ":")
            match
          (progn
            ;; Go back to where we were before the recursive call.
            (goto-char oldpoint)
            kwop)))))))

(defconst tuareg2-semicolon-match-stop-regexp
  (tuareg2-ro "and" "do" "end" "in" "with"))

(defconst tuareg2-no-code-after-paren-regexp
  (tuareg2-no-code-after "[[{(][|<]?"))

(defun tuareg2-semicolon-indent-kwop-point (&optional leading-semi-colon)
  ;; return (kwop kwop-point indentation)
  (let ((kwop (tuareg2-find-kwop tuareg2-find-semicolon-match-regexp
                                tuareg2-semicolon-match-stop-regexp))
        (point (point)))
    ;; We don't need to find the keyword matching `and' since we know it's `let'!
    (list
     (cond
       ((string= kwop ";")
        (forward-line 1)
        (while (or (tuareg2-in-comment-p)
                   (looking-at tuareg2-no-code-this-line-regexp))
          (forward-line 1))
        (back-to-indentation)
        (current-column))
       ((and leading-semi-colon
             (looking-at "\\((\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
             (not (looking-at tuareg2-no-code-after-paren-regexp)))
        (current-column))
       ;; ((looking-at (tuareg2-no-code-after "\\((\\|\\[[<|]?\\|{<?\\)"))
       ;;  (+ (current-column) tuareg2-default-indent))
       ((looking-at (tuareg2-no-code-after "\\<begin\\>\\|\\((\\|\\[[<|]?\\|{<?\\)"))
        (if (tuareg2-in-indentation-p)
            (+ (current-column) tuareg2-default-indent)
          (tuareg2-indent-from-previous-kwop)))
       ((looking-at "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)") ; paren with subsequent text
        (tuareg2-search-forward-paren)
        (current-column))
       ((string= kwop "method")
        (+ (tuareg2-paren-or-indentation-column) tuareg2-method-indent))
       ((string= kwop "->")
        (if (save-excursion
              (tuareg2-find-arrow-match)
              (or (looking-at "\\<fun\\>\\||")
                  (looking-at (tuareg2-extra-unindent-regexp))))
            (tuareg2-paren-or-indentation-indent)
          (tuareg2-find-semicolon-match)))
       ((string= kwop "end")
        (tuareg2-find-match)
        (tuareg2-find-semicolon-match))
       ((string= kwop "in")
        (tuareg2-find-in-match)
        (+ (current-column) tuareg2-in-indent))
       ((string= kwop "where")
        (tuareg2-find-in-match)
        (+ (tuareg2-paren-or-indentation-column) tuareg2-in-indent))
       ((string= kwop "let")
        (+ (current-column) tuareg2-let-indent))
       ((string= kwop "try")
        (forward-char 3) (skip-syntax-forward " ")
        (current-column))
       (t (tuareg2-paren-or-indentation-indent)))
     kwop point)))

(defun tuareg2-find-semicolon-match (&optional leading-semi-colon)
  (car (tuareg2-semicolon-indent-kwop-point leading-semi-colon)))

(defmacro tuareg2-reset-and-kwop (kwop)
  `(when (and ,kwop (string= ,kwop "and"))
     (setq ,kwop (tuareg2-find-and-match))))

(defconst tuareg2-phrase-regexp-1 (tuareg2-ro "module" "type"))

(defconst tuareg2-phrase-regexp-2 (tuareg2-ro "and" "let" "module" "with"))

(defconst tuareg2-phrase-regexp-3
  (tuareg2-ro "and" "end" "every" "in" "with"))

(defconst tuareg2-false-type-regexp (tuareg2-ro "and" "class" "module" "with"))

(defun tuareg2-looking-at-false-type ()
  (save-excursion
    (tuareg2-find-meaningful-word)
    (looking-at tuareg2-false-type-regexp)))

(defun tuareg2-find-phrase-indentation (&optional phrase-break)
  (if (and (looking-at tuareg2-phrase-regexp-1) (> (point) (point-min))
           (save-excursion
             (tuareg2-find-meaningful-word)
             (looking-at tuareg2-phrase-regexp-2)))
      (progn
        (tuareg2-find-meaningful-word)
        (+ (current-column) tuareg2-default-indent))
    (let ((looking-at-and (looking-at "\\<and\\>"))
          (kwop (tuareg2-find-kwop
                 (if phrase-break
                     tuareg2-find-phrase-indentation-break-regexp
                   tuareg2-find-phrase-indentation-regexp)
                 tuareg2-phrase-regexp-3))
          (tmpkwop nil) (curr nil))
      (tuareg2-reset-and-kwop kwop)
      (cond ((not kwop) (current-column))
            ((string= kwop "every")
             (tuareg2-find-phrase-indentation phrase-break))
            ((string= kwop "end")
             (if (not (save-excursion
                        (setq tmpkwop (tuareg2-find-match))
                        (setq curr (point))
                        (string= tmpkwop "object")))
                 (progn
                   (tuareg2-find-match)
                   (tuareg2-find-phrase-indentation phrase-break))
               (tuareg2-find-kwop tuareg2-find-phrase-indentation-class-regexp)
               (current-column)))
            ((and (string= kwop "with")
                  (not (save-excursion
                         (setq tmpkwop (tuareg2-find-with-match))
                         (setq curr (point))
                         (string= tmpkwop "module"))))
             (goto-char curr)
             (tuareg2-find-phrase-indentation phrase-break))
            ((and (string= kwop "in")
                  (not (save-excursion
                         (setq tmpkwop (tuareg2-find-in-match))
                         (tuareg2-reset-and-kwop tmpkwop)
                         (setq curr (point))
                         (and (string= tmpkwop "let")
                              (not (tuareg2-looking-at-internal-let))))))
             (goto-char curr)
             (tuareg2-find-phrase-indentation phrase-break))
            ((tuareg2-at-phrase-break-p)
             (end-of-line)
             (tuareg2-skip-blank-and-comments)
             (current-column))
            ((string= kwop "let")
             (if (tuareg2-looking-at-internal-let)
                 (tuareg2-find-phrase-indentation phrase-break)
                 (current-column)))
            ((string= kwop "with")
             (current-column))
            ((string= kwop "end")
             (current-column))
            ((or (string= kwop "in") (string= kwop "where"))
             (tuareg2-find-in-match)
             (current-column))
            ((string= kwop "class")
             (tuareg2-paren-or-indentation-column))
            ((looking-at tuareg2-inside-module-or-class-opening)
             (+ (tuareg2-paren-or-indentation-column)
                (tuareg2-assoc-indent kwop)))
            ((or (string= kwop "type") (string= kwop "module"))
             (if (or (tuareg2-looking-at-false-type)
                     (tuareg2-looking-at-false-module))
                 (if looking-at-and
                     (current-column)
                   (if (string= "and" (tuareg2-find-meaningful-word))
                       (progn
                         (tuareg2-find-and-match)
                         (tuareg2-find-phrase-indentation phrase-break))
                     (tuareg2-find-phrase-indentation phrase-break)))
               (current-column)))
            ((looking-at "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*[^ \t\n]")
             (tuareg2-search-forward-paren)
             (current-column))
            ((string= kwop "open") ; compatible with Caml Light `#open'
             (tuareg2-paren-or-indentation-column))
            (t (current-column))))))

(defconst tuareg2-paren-or-indentation-stop-regexp
  (tuareg2-ro "and" "do" "in" "with"))

(defun tuareg2-back-to-paren-or-indentation ()
  "Search backwards for the first open paren in line, or skip to indentation.
Returns t iff skipped to indentation."
  (if (or (bolp) (tuareg2-in-indentation-p))
      (progn (back-to-indentation) t)
    (let ((kwop (tuareg2-find-kwop
                 tuareg2-back-to-paren-or-indentation-regexp
                 tuareg2-paren-or-indentation-stop-regexp))
          (retval))
      (when (string= kwop "with")
        (let ((with-point (point)))
          (setq kwop (tuareg2-find-with-match))
          (if (or (string= kwop "match") (string= kwop "try"))
              (tuareg2-find-kwop tuareg2-back-to-paren-or-indentation-regexp
                                "\\<and\\>")
            (setq kwop "with") (goto-char with-point))))
      (setq retval
            (cond
             ((string= kwop "with") nil)
             ((or (string= kwop "in") (string= kwop "do"))
              (tuareg2-in-indentation-p))
             (t (back-to-indentation) t)))
      (cond
    ;   ((looking-at "|[^|]")
    ;    (re-search-forward "|[^|][ \t]*") nil)
       ((or (string= kwop "in") (string= kwop "do"))
        (tuareg2-find-in-match)
        (tuareg2-back-to-paren-or-indentation)
        (if (looking-at "\\<\\(let\\|and\\)\\>")
            (forward-char tuareg2-in-indent)) nil)
       (t retval)))))

(defun tuareg2-paren-or-indentation-column ()
  (tuareg2-back-to-paren-or-indentation)
  (current-column))

(defun tuareg2-paren-or-indentation-indent ()
  (+ (tuareg2-paren-or-indentation-column) tuareg2-default-indent))

(defun tuareg2-search-forward-paren ()
  (re-search-forward "\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)[ \t]*"))

(defun tuareg2-add-default-indent (leading-operator)
  (if leading-operator 0 tuareg2-default-indent))

(defconst tuareg2-internal-let-regexp
  (concat "[[({;=]\\|"
           (tuareg2-ro "begin" "open" "if" "in" "do" "try" "then" "else"
                      "match" "while" "when")))

(defun tuareg2-looking-at-internal-let ()
  (save-excursion
    (tuareg2-find-meaningful-word)
    (and (not (tuareg2-at-phrase-break-p))
         (or (looking-at tuareg2-internal-let-regexp)
             (looking-at tuareg2-operator-regexp)))))

(defconst tuareg2-false-module-regexp (tuareg2-ro "and" "let" "with"))

(defun tuareg2-looking-at-false-module ()
  (save-excursion
    (tuareg2-find-meaningful-word)
    (looking-at tuareg2-false-module-regexp)))

(defun tuareg2-looking-at-false-sig-struct ()
  (save-excursion
    (tuareg2-find-module)
    (looking-at "\\<module\\>\\|(")))

(defun tuareg2-looking-at-in-let ()
  (save-excursion
    (string= (tuareg2-find-meaningful-word) "in")))

(defun tuareg2-find-module ()
  (tuareg2-find-kwop tuareg2-find-module-regexp))

(defun tuareg2-indent-from-previous-kwop ()
  (let* ((start-pos (point))
         (kwop (tuareg2-find-argument-kwop-non-blank t))
         (captive= (and (string= kwop "=") (tuareg2-captive-=)))
         (kwop-pos (point)))
    (forward-char (length kwop))
    (tuareg2-skip-blank-and-comments)
    (cond ((or (not captive=)
               (/= (point) start-pos)) ; code between paren and kwop
           (goto-char start-pos)
           (tuareg2-paren-or-indentation-indent))
          (t
           (goto-char kwop-pos)
           (when (string= kwop "=")
             (setq kwop (tuareg2-find-=-match)))
           (+ tuareg2-default-indent
              (if (assoc kwop tuareg2-leading-kwop-alist)
                  (tuareg2-compute-kwop-indent kwop)
                  (current-column)))))))

(defun tuareg2-find-colon-typespec (start-pos)
  (let* ((old-pos (point))
         (new-pos (search-forward ":" start-pos t)))
    (when new-pos
      (backward-char 1)
      (skip-syntax-backward " ")
      (skip-syntax-backward "w")
      (skip-syntax-backward " ")
      (let ((char (char-before)))
        (cond ((or (char-equal char ??) (char-equal char ?~))
               (goto-char old-pos) nil)
              (t (goto-char new-pos) t))))))

(defun tuareg2-indent-from-paren (leading-operator start-pos)
  (cond
   ((looking-at (tuareg2-no-code-after "\\(\\(\\.<\\|(\\|\\[[<|]?\\|{<?\\)\\)"))
    (cond ((tuareg2-in-indentation-p)
           (+ tuareg2-default-indent
              (current-column)))
          ((tuareg2-find-colon-typespec start-pos)
           (if (looking-at tuareg2-no-code-this-line-regexp)
               (tuareg2-paren-or-indentation-indent)
             (tuareg2-skip-blank-and-comments)
             (current-column)))
          (t (tuareg2-indent-from-previous-kwop))))
   ((looking-at "\\<begin\\>")
    (tuareg2-paren-or-indentation-indent))
   ((looking-at "([ \t]*\\(\\w\\)")
    (goto-char (match-beginning 1))
    (current-column))
   (t
    (+ (tuareg2-add-default-indent leading-operator)
       (current-column)))))

(defun tuareg2-skip-to-next-form (old-point)
  (while (and (not (looking-at tuareg2-no-more-code-this-line-regexp))
              (< (point) old-point)) ; do not go beyond old-point
    (forward-sexp 1))
  (tuareg2-skip-blank-and-comments)
  (tuareg2-back-to-paren-or-indentation))

(defun tuareg2-find-argument-kwop (leading-operator)
  (tuareg2-find-kwop (if leading-operator
                      tuareg2-compute-argument-indent-regexp
                      tuareg2-compute-normal-indent-regexp)
                    (tuareg2-keyword-regexp)))

(defun tuareg2-find-argument-kwop-clean (leading-operator)
  (let (kwop)
    (while (or (progn (setq kwop (tuareg2-find-argument-kwop leading-operator))
                      (tuareg2-reset-and-kwop kwop)
                      nil)
               (and (string= kwop "=") (tuareg2-false-=-p))
               (and (looking-at tuareg2-no-code-this-line-regexp)
                    (not (= (point) (point-min))))))
    kwop))

(defun tuareg2-find-argument-kwop-non-blank (leading-operator)
  (let ((kwop "") (point (1+ (point))))
    (while (and (> point (point)) (string= "" kwop))
      (setq point (point)
            kwop (tuareg2-find-argument-kwop-clean leading-operator)))
    kwop))

(defun tuareg2-compute-argument-indent (leading-operator)
  (let* ((old-point (line-beginning-position))
         (kwop (tuareg2-find-argument-kwop-non-blank leading-operator))
         (match-end-point (+ (point) (length kwop)))) ; match-end is invalid!
    (cond
     ((and (string= kwop "->")
           (not (looking-at (tuareg2-no-code-after "->"))))
      (let (matching-kwop matching-pos)
        (save-excursion
          (setq matching-kwop (tuareg2-find-arrow-match))
          (setq matching-pos (point)))
        (cond
         ((string= matching-kwop ":")
          (goto-char matching-pos)
          (tuareg2-find-arrow-match) ; matching `val' or `let'
          (+ (current-column) tuareg2-val-indent))
         ((or (string= matching-kwop "val") (string= matching-kwop "let"))
          (+ (current-column) tuareg2-val-indent))
         ((string= matching-kwop "|")
          (goto-char matching-pos)
          (+ (tuareg2-add-default-indent leading-operator)
             (current-column)
             (- tuareg2-pipe-extra-unindent)
             tuareg2-default-indent))
         (t
          (+ (tuareg2-paren-or-indentation-column)
             (tuareg2-add-default-indent leading-operator))))))
     ((string= kwop "fun")
      (+ (tuareg2-paren-or-indentation-column)
         (tuareg2-add-default-indent leading-operator)
         (tuareg2-assoc-indent kwop)))
     ((<= old-point (point))
      (+ (tuareg2-add-default-indent leading-operator)
         (current-column)))
     (t
      (goto-char match-end-point) ; skip kwop == (forward-char (length kwop))
      (tuareg2-skip-to-next-form old-point)
      (+ (tuareg2-add-default-indent
          (if (save-excursion (goto-char match-end-point)
                              (looking-at tuareg2-no-more-code-this-line-regexp))
              (or leading-operator (string= kwop "{")
                  (looking-at (tuareg2-no-code-after "[[:upper:]].*\\.")))
            (not (looking-at tuareg2-operator-regexp))))
         (current-column))))))

(defun tuareg2-compute-arrow-indent ()
  (let (kwop pos)
    (save-excursion (setq kwop (tuareg2-find-arrow-match) pos (point)))
    (cond ((string= kwop "|")
           (tuareg2-find-arrow-match)
           (+ (current-column) tuareg2-default-indent))
          ((or (string= kwop "val")
               (string= kwop "let"))
           (goto-char pos)
           (+ (current-column) tuareg2-val-indent))
          ((string= kwop "type")
           (goto-char pos)
           (+ (current-column) tuareg2-type-indent
              tuareg2-default-indent))
          ((string= kwop "(")
           (goto-char pos)
           (tuareg2-indent-after-next-char))
          ((or (string= kwop "{")
               (string= kwop ";"))
           (if (and (looking-at "->")
                    (search-backward ":" pos t))
               (tuareg2-indent-after-next-char)
             (tuareg2-back-to-paren-or-indentation)
             (current-column)))
          ((tuareg2-monadic-operator-p kwop)
           (destructuring-bind (indent kwop _point)
               (tuareg2-semicolon-indent-kwop-point)
             (- indent
                (if (string= kwop "in")
                    tuareg2-in-indent 0))))
          (t (tuareg2-paren-or-indentation-indent)))))

(defun tuareg2-compute-keyword-indent (kwop leading-operator start-pos)
  (cond ((string= kwop ";")
         (if (looking-at (tuareg2-no-code-after ";"))
             (let* ((pos (point)) (indent (tuareg2-find-semicolon-match)))
               (if (looking-at tuareg2-phrase-regexp-1)
                   (progn
                     (goto-char start-pos)
                     (if (search-backward ":" pos t)
                         (tuareg2-indent-after-next-char)
                       indent))
                 indent))
           (tuareg2-paren-or-indentation-indent)))
        ((string= kwop ",")
         (if (looking-at (tuareg2-no-code-after ","))
             (let ((mkwop (tuareg2-find-comma-match)))
               (cond ((or (string= mkwop "[")
                          (string= mkwop "{")
                          (string= mkwop "("))
                      (forward-char 1) (skip-syntax-forward " ")
                      (current-column))
                     ((looking-at "[[{(]\\|\\.<")
                      (tuareg2-indent-from-paren t start-pos))
                     ((or (and (looking-at "[<|]")
                               (char-equal ?\[ (preceding-char)))
                          (and (looking-at "<")
                               (char-equal ?\{ (preceding-char))))
                      (tuareg2-backward-char)
                      (tuareg2-indent-from-paren t start-pos))
                     ((and (looking-at "\\<let\\>") (string= mkwop "in"))
                      (+ (current-column) tuareg2-in-indent))
                     (t (+ (tuareg2-paren-or-indentation-column)
                           (tuareg2-assoc-indent mkwop)))))
           (tuareg2-paren-or-indentation-indent)))
        ((looking-at "\\<begin\\>\\|->")
         (if (looking-at (tuareg2-no-code-after "\\(\\<begin\\>\\|->\\)"))
             (tuareg2-indent-from-paren leading-operator start-pos)
           (+ tuareg2-default-indent
              (tuareg2-indent-from-paren leading-operator start-pos))))
        ((or (string= kwop "let") (string= kwop "and"))
         (tuareg2-back-to-paren-or-indentation)
         (+ (tuareg2-paren-or-indentation-indent)
            (tuareg2-assoc-indent kwop t)))
        ((string= kwop "with")
         (if (save-excursion
               (let ((tmpkwop (tuareg2-find-with-match)))
                 (or (string= tmpkwop "module")
                     (string= tmpkwop "{"))))
             (tuareg2-paren-or-indentation-indent)
           (+ (tuareg2-paren-or-indentation-column)
              (* 2 tuareg2-default-indent) ; assume a missing first "|"
              (tuareg2-assoc-indent kwop t))))
        ((string-match "\\<\\(fun\\|of\\)\\>" kwop)
         (+ (tuareg2-paren-or-indentation-column)
            (tuareg2-add-default-indent leading-operator)
            (tuareg2-assoc-indent kwop t)))
        ((string-match (tuareg2-extra-unindent-regexp) kwop)
         (+ (tuareg2-paren-or-indentation-column)
            (tuareg2-assoc-indent kwop t)))
        ((string= kwop "in")
         (when (looking-at (tuareg2-no-code-after "\\<in\\>"))
           (tuareg2-find-in-match))
         (+ (current-column)
            tuareg2-in-indent))
        ((string-match (tuareg2-matching-kwop-regexp) kwop)
         (tuareg2-find-leading-kwop-match kwop)
         (if (tuareg2-in-indentation-p)
             (+ (current-column)
                (tuareg2-assoc-indent kwop t))
           (tuareg2-back-to-paren-or-indentation)
           (+ (tuareg2-paren-or-indentation-indent)
              (tuareg2-assoc-indent kwop t))))
        ((string= kwop "try")
         (forward-char 3)
         (if (looking-at tuareg2-no-more-code-this-line-regexp)
             (+ (current-column) -3 tuareg2-default-indent)
           (skip-syntax-forward " ")
           (+ (current-column) tuareg2-default-indent)))
        (t (+ (if (tuareg2-in-indentation-p)
                  (current-column)
                (tuareg2-paren-or-indentation-indent))
              (tuareg2-assoc-indent kwop t)))))

(defconst tuareg2-=-indent-regexp-1
  (tuareg2-ro "val" "let" "method" "module" "class" "when" "for" "if" "do"))

(defun tuareg2-compute-=-indent (start-pos)
  (let ((current-column-module-type nil) (kwop1 (tuareg2-find-=-match))
        (next-pos (point)))
    (+ (save-excursion
         (tuareg2-reset-and-kwop kwop1)
         (cond ((string= kwop1 "type")
                (tuareg2-find-meaningful-word)
                (cond ((looking-at "\\<module\\>")
                       (setq current-column-module-type (current-column))
                       tuareg2-default-indent)
                      ((looking-at "\\<\\(with\\|and\\)\\>")
                       (tuareg2-find-with-match)
                       (setq current-column-module-type (current-column))
                       tuareg2-default-indent)
                      (t (goto-char start-pos)
                         (beginning-of-line)
                         (+ (tuareg2-add-default-indent
                             (looking-at "[ \t]*[\[|]"))
                            tuareg2-type-indent))))
               ((looking-at tuareg2-=-indent-regexp-1)
                (let ((matched-string (tuareg2-match-string 0)))
                  (setq current-column-module-type (current-column))
                  (tuareg2-assoc-indent matched-string)))
               ((looking-at "\\<object\\>")
                (tuareg2-back-to-paren-or-indentation)
                (setq current-column-module-type (current-column))
                (+ (tuareg2-assoc-indent "object")
                   tuareg2-default-indent))
               ((looking-at tuareg2-no-code-after-paren-regexp)
                (setq current-column-module-type
                      (tuareg2-indent-from-paren nil next-pos))
                tuareg2-default-indent)
               (t (setq current-column-module-type
                        (tuareg2-paren-or-indentation-indent))
                  tuareg2-default-indent)))
       (or current-column-module-type
           (current-column)))))

(defun tuareg2-indent-after-next-char ()
  (forward-char 1)
  (tuareg2-skip-blank-and-comments)
  (current-column))

(defconst tuareg2-definitions-regexp
  (tuareg2-ro "and" "val" "type" "module" "class" "exception" "let")
  "Regexp matching definition phrases.")

(defun tuareg2-compute-normal-indent ()
  (let ((leading-operator (looking-at tuareg2-operator-regexp)))
    (beginning-of-line)
    (save-excursion
      (let ((start-pos (point))
            (kwop (tuareg2-find-argument-kwop-clean leading-operator)))
        (cond
          ((not kwop) (current-column))
          ((tuareg2-at-phrase-break-p)
           (tuareg2-find-phrase-indentation t))
          ((and (string= kwop "|") (not (char-equal ?\[ (preceding-char))))
           (tuareg2-backward-char)
           (+ (tuareg2-paren-or-indentation-indent)
              (tuareg2-add-default-indent leading-operator)))
          ((or (looking-at "[[{(]")
               (and (looking-at "[<|]")
                    (char-equal ?\[ (preceding-char))
                    (progn (tuareg2-backward-char) t))
               (and (looking-at "<")
                    (char-equal ?\{ (preceding-char))
                    (progn (tuareg2-backward-char) t)))
           (cond ((looking-at "{ *[A-Z]")
                  (forward-char 1) (skip-syntax-forward " ")
                  (current-column))
                 ((looking-at (tuareg2-no-code-after "[[{(][<|]?"))
                  (tuareg2-indent-from-paren leading-operator start-pos))
                 ((and leading-operator (string= kwop "("))
                  (tuareg2-indent-after-next-char))
                 (t (+ tuareg2-default-indent
                       (tuareg2-indent-from-paren leading-operator start-pos)))))
          ((looking-at "\\.<")
           (if (looking-at (tuareg2-no-code-after "\\.<"))
               (tuareg2-indent-from-paren leading-operator start-pos)
             (+ tuareg2-default-indent
                (tuareg2-indent-from-paren leading-operator start-pos))))
          ((looking-at "->")
           (tuareg2-compute-arrow-indent))
          ((looking-at (tuareg2-keyword-regexp))
           (tuareg2-compute-keyword-indent kwop leading-operator start-pos))
          ((and (string= kwop "=") (not (tuareg2-false-=-p))
                (or (null leading-operator)
                    ;; defining "=", not testing for equality
                    (string-match tuareg2-definitions-regexp
                                  (save-excursion
                                    (tuareg2-find-argument-kwop-clean t)))))
           (tuareg2-compute-=-indent start-pos))
          (nil 0)
          (t (tuareg2-compute-argument-indent leading-operator)))))))

(defun tuareg2-compute-pipe-indent (matching-kwop old-point)
  (cond
    ((string= matching-kwop "|")
     (tuareg2-back-to-paren-or-indentation)
     (current-column))
    ((and (string= matching-kwop "=")
          (not (tuareg2-false-=-p)))
     (re-search-forward "=[ \t]*")
     (current-column))
    ((and matching-kwop
          (looking-at (tuareg2-match-pipe-kwop-regexp)))
     (when (looking-at (tuareg2-extra-unindent-regexp))
       (tuareg2-back-to-paren-or-indentation))
     (+ (tuareg2-assoc-indent matching-kwop t)
        (tuareg2-add-default-indent (not (looking-at "|")))
        (current-column)
        (if (or (string= matching-kwop "type")
                (string= matching-kwop "["))
            0
            tuareg2-pipe-extra-unindent)))
    (t
     (goto-char old-point)
     (tuareg2-compute-normal-indent))))

(defun tuareg2-compute-paren-indent (paren-match-p old-point)
  (unless paren-match-p
    (tuareg2-search-forward-paren))
  (let ((looking-at-paren (char-equal ?\( (char-after))) (start-pos (point)))
    (when (or looking-at-paren
              (looking-at (tuareg2-no-code-after "\\(\{\\(.*with[ \t]*\\([[:upper:]].*\\.\\)?\\)?\\|\\[\\)")))
      (if (or (tuareg2-in-indentation-p)
              (save-excursion (string= ":" (tuareg2-find-meaningful-word))))
          (tuareg2-back-to-paren-or-indentation)
        (tuareg2-indent-from-previous-kwop))
      (when looking-at-paren
        (skip-chars-forward "( \t" start-pos))
      (while (and (looking-at "[([{]")
                  (> (scan-sexps (point) 1)
                     (save-excursion (goto-char old-point)
                                     (line-end-position))))
        (forward-char 1)
        (skip-syntax-forward " "))))
  (current-column))

(defun tuareg2-compute-kwop-indent-general (kwop matching-kwop)
  (let* ((looking-at-matching (looking-at matching-kwop))
         (extra-unindent        ; non-paren code before matching-kwop
          (unless (save-excursion
                    (skip-chars-backward "( \t" (line-beginning-position))
                    (bolp))
            (tuareg2-back-to-paren-or-indentation)
            t)))
    (+ (current-column)
       (tuareg2-add-default-indent
        (if extra-unindent
            (or (string= matching-kwop "struct")
                (string= matching-kwop "object")
                (string= matching-kwop "with")
                (string= kwop "end"))
            (or (not (string= kwop "then"))
                looking-at-matching))))))

(defun tuareg2-compute-kwop-indent (kwop)
  (when (string= kwop "rec")
    (setq kwop "and"))
  (let* ((old-point (point))
         (paren-match-p (looking-at "[|>]?[]})]\\|>\\."))
         (real-pipe (looking-at "|\\([^|]\\|$\\)"))
         (matching-kwop (tuareg2-find-leading-kwop-match kwop)))
    (cond ((string= kwop "|")
           (if real-pipe
               (tuareg2-compute-pipe-indent matching-kwop old-point)
             (goto-char old-point)
             (tuareg2-compute-normal-indent)))
          ((looking-at "[[{(][<|]?\\|\\.<")
           (tuareg2-compute-paren-indent paren-match-p old-point))
          ((string= kwop "with")
           (when (string= matching-kwop "type")
             (setq old-point (point)
                   matching-kwop (tuareg2-find-meaningful-word)))
           (while (string= matching-kwop "with")
             (tuareg2-find-with-match)
             (setq matching-kwop (tuareg2-find-leading-kwop-match kwop)))
           (cond ((or (string= matching-kwop "module")
                      (string= matching-kwop "struct"))
                  (tuareg2-paren-or-indentation-indent))
                 ((or (string= matching-kwop "try")
                      (string= matching-kwop "match"))
                  (tuareg2-compute-kwop-indent-general kwop matching-kwop))
                 (t (goto-char old-point)
                    (tuareg2-compute-kwop-indent-general kwop matching-kwop))))
          ((or (and (string= kwop "and")
                    (string= matching-kwop "reset")))
           (if (tuareg2-in-indentation-p)
               (current-column)
             (tuareg2-paren-or-indentation-column)))
          ((string= kwop "in")
           (+ (current-column)
              (tuareg2-add-default-indent (string= matching-kwop "let"))))
          ((not (string= kwop "and")) ; pretty general case
           (tuareg2-compute-kwop-indent-general kwop matching-kwop))
          ((string= matching-kwop "with")
           (current-column))
          (t (tuareg2-paren-or-indentation-column)))))

(defun tuareg2-indent-to-code (beg-pos match)
  (unless (and (string= match "(")
               (search-forward "->" beg-pos t))
    (forward-char (length match)))
  (tuareg2-skip-blank-and-comments)
  (current-column))

;;----------------------------------------------------------------------------;;
;; Syntax table                                                               ;;
;;----------------------------------------------------------------------------;;

(defvar tuareg2-mode-syntax-table
  (let ((st (make-syntax-table)))
    (modify-syntax-entry ?_ "_" st)
    (modify-syntax-entry ?? ". p" st)
    (modify-syntax-entry ?~ ". p" st)
    (modify-syntax-entry ?: "." st)
    ;; FIXME: Should be "_" rather than "w"!
    (modify-syntax-entry ?' "w" st) ; ' is part of identifiers (for primes).
    (modify-syntax-entry ?\" "\"" st) ; " is a string delimiter
    (modify-syntax-entry ?\\ "\\" st)
    (modify-syntax-entry ?*  ". 23" st)
    (modify-syntax-entry ?\( "()1n" st)
    (modify-syntax-entry ?\) ")(4n" st)
    st)
  "Syntax table in use in Tuareg2 mode buffers.")

(defmacro tuareg2-with-internal-syntax (&rest body)
  `(progn
     ;; Switch to a modified internal syntax.
     (modify-syntax-entry ?. "w" tuareg2-mode-syntax-table)
     (modify-syntax-entry ?_ "w" tuareg2-mode-syntax-table)
     (unwind-protect (progn ,@body)
       ;; Switch back to the interactive syntax.
       (modify-syntax-entry ?. "." tuareg2-mode-syntax-table)
       (modify-syntax-entry ?_ "_" tuareg2-mode-syntax-table))))

(defun tuareg2-indent-command (&optional from-leading-star)
  "Indent the current line in Tuareg2 mode.

Compute new indentation based on OCaml syntax."
  (interactive "*")
  (unless from-leading-star
    (tuareg2-auto-fill-insert-leading-star))
  (let ((case-fold-search nil))
   (tuareg2-with-internal-syntax
    (save-excursion
      (back-to-indentation)
      (indent-line-to (max 0 (tuareg2-compute-indent))))
    (when (tuareg2-in-indentation-p) (back-to-indentation)))))

(defconst tuareg2-sig-struct-regexp (tuareg2-ro "sig" "struct"))

(defconst tuareg2-top-level-command-regexp
  (concat "#" (tuareg2-ro "open" "load" "use")))

(defun tuareg2-compute-indent ()
  (save-excursion
    (cond
     ((tuareg2-in-comment-p)
      (cond
       ((looking-at "(\\*")
        (if tuareg2-indent-leading-comments
            (save-excursion
              (tuareg2-skip-blank-and-comments)
              (back-to-indentation)
              (current-column))
          (current-column)))
       ((looking-at "\\*\\**)")
        (tuareg2-beginning-of-literal-or-comment-fast)
        (if (tuareg2-leading-star-p)
            (+ (current-column)
               (if (save-excursion
                     (forward-line 1)
                     (back-to-indentation)
                     (looking-at "*")) 1
                 tuareg2-comment-end-extra-indent))
          (+ (current-column) tuareg2-comment-end-extra-indent)))
       (tuareg2-indent-comments
        (let ((star (and (tuareg2-leading-star-p)
                         (looking-at "\\*"))))
          (tuareg2-beginning-of-literal-or-comment-fast)
          (if star (re-search-forward "(") (re-search-forward "(\\*+[ \t]*"))
          (current-column)))
       (t (current-column))))
     ((tuareg2-in-literal-p)
      (current-column))
     ((or (looking-at "\\<let\\>") (looking-at "\\<open\\>"))
      (if (tuareg2-looking-at-internal-let)
          (if (tuareg2-looking-at-in-let)
              (progn
                (tuareg2-find-meaningful-word)
                (tuareg2-find-in-match)
                (current-column))
            (tuareg2-compute-normal-indent))
        (tuareg2-find-phrase-indentation)))
     ((or (looking-at tuareg2-governing-phrase-regexp)
          (looking-at ";;"))
      (tuareg2-find-phrase-indentation))
     ((and tuareg2-sig-struct-align (looking-at tuareg2-sig-struct-regexp))
      (if (string= (tuareg2-find-module) "module")
          (current-column)
        (tuareg2-paren-or-indentation-indent)))
     ((looking-at ";")
      (tuareg2-find-semicolon-match t))
     ((looking-at "|!")
      (tuareg2-indent-to-code (line-beginning-position)
                             (tuareg2-find-pipe-bang-match)))
     ((looking-at ">>[=>|]")
      (tuareg2-indent-to-code (line-beginning-position)
                             (tuareg2-find-monadic-match)))
     ((or (looking-at "%\\|;;")
          (looking-at tuareg2-top-level-command-regexp))
      0)
     ((or (looking-at (tuareg2-matching-kwop-regexp))
          (looking-at "\\<rec\\>"))
      (tuareg2-compute-kwop-indent (tuareg2-match-string 0)))
     (t (tuareg2-compute-normal-indent)))))

(defun tuareg2-split-string ()
  "Called whenever a line is broken inside an OCaml string literal."
  (insert-before-markers "\\ ")
  (tuareg2-backward-char))

(defadvice newline-and-indent (around
                               tuareg2-newline-and-indent
                               activate)
  "Handle multi-line strings in Tuareg2 mode."
  (let ((hooked (and (eq major-mode 'tuareg2-mode) (tuareg2-in-literal-p)))
        (split-mark))
    (when hooked
      (setq split-mark (set-marker (make-marker) (point)))
      (tuareg2-split-string))
    ad-do-it
    (when hooked
      (goto-char split-mark)
      (set-marker split-mark nil))))

(defun tuareg2-abbrev-hook ()
  "If inserting a leading keyword at beginning of line, reindent the line."
  (unless (tuareg2-in-literal-or-comment-p)
    (let* ((bol (line-beginning-position))
           (kw (save-excursion
                 (and (re-search-backward "^[ \t]*\\(\\w\\|_\\)+\\=" bol t)
                      (tuareg2-match-string 1)))))
      (when kw
        (insert " ")
        (indent-according-to-mode)
        (backward-delete-char-untabify 1)))))

(defun tuareg2-skip-to-end-of-phrase ()
  (let ((old-point (point)))
    (when (and (string= (tuareg2-find-meaningful-word) ";")
               (char-equal (preceding-char) ?\;))
      (setq old-point (1- (point))))
    (goto-char old-point)
    (let ((kwop (tuareg2-find-meaningful-word)))
      (goto-char (+ (point) (length kwop))))))

(defun tuareg2-skip-blank-and-comments ()
  (skip-syntax-forward " ")
  (while (and (not (eobp)) (tuareg2-in-comment-p)
              (search-forward "*)" nil t))
    (skip-syntax-forward " ")))

(defun tuareg2-skip-back-blank-and-comments ()
  (skip-syntax-backward " ")
  (while (save-excursion (tuareg2-backward-char)
                         (and (> (point) (point-min)) (tuareg2-in-comment-p)))
    (tuareg2-backward-char)
    (tuareg2-beginning-of-literal-or-comment) (skip-syntax-backward " ")))

(defun tuareg2-find-phrase-beginning (&optional stop-at-and)
  "Find `real' phrase beginning and return point."
  (beginning-of-line)
  (tuareg2-skip-blank-and-comments)
  (end-of-line)
  (tuareg2-skip-to-end-of-phrase)
  (let ((old-point (point)) (pt (point)))
    (if stop-at-and
        (tuareg2-find-kwop tuareg2-find-phrase-beginning-and-regexp "and")
      (tuareg2-find-kwop tuareg2-find-phrase-beginning-regexp))
    (while (and (> (point) (point-min)) (< (point) old-point)
                (or (not (looking-at tuareg2-find-phrase-beginning-and-regexp))
                    (and (looking-at "\\<let\\>")
                         (tuareg2-looking-at-internal-let))
                    (and (looking-at "\\<and\\>")
                         (save-excursion
                           (tuareg2-find-and-match)
                           (tuareg2-looking-at-internal-let)))
                    (and (looking-at "\\<module\\>")
                         (tuareg2-looking-at-false-module))
                    (and (looking-at tuareg2-sig-struct-regexp)
                         (tuareg2-looking-at-false-sig-struct))
                    (and (looking-at "\\<type\\>")
                         (tuareg2-looking-at-false-type))))
      (when (= pt (point))
        (error "tuareg2-find-phrase-beginning: inf loop at %d" pt))
      (setq pt (point))
      (if (looking-at "\\<end\\>")
          (tuareg2-find-match)
        (unless (bolp) (tuareg2-backward-char))
        (setq old-point (point))
        (if stop-at-and
            (tuareg2-find-kwop tuareg2-find-phrase-beginning-and-regexp "and")
          (tuareg2-find-kwop tuareg2-find-phrase-beginning-regexp))))
    (when (tuareg2-at-phrase-break-p)
      (end-of-line) (tuareg2-skip-blank-and-comments))
    (back-to-indentation)
    (point)))

(defun tuareg2-search-forward-end ()
  (let ((begin (point)) (current -1) (found) (move t))
    (while (and move (> (point) current))
      (if (re-search-forward "\\<end\\>" (point-max) t)
          (let ((stop (point)) (kwop))
            (unless (tuareg2-in-literal-or-comment-p)
              (save-excursion
                (tuareg2-backward-char 3)
                (setq kwop (tuareg2-find-match))
                (cond
                 ((string= kwop "object")
                  (tuareg2-find-phrase-beginning))
                 ((and (looking-at tuareg2-sig-struct-regexp)
                       (tuareg2-looking-at-false-sig-struct))
                  (tuareg2-find-phrase-beginning)))
                (cond
                 ((or
                   (> (point) begin)
                   (and
                    (string= kwop "sig")
                    (looking-at "[ \t\n]*\\(\\<with\\>[ \t\n]*\\<type\\>\\|=\\)")))
                  (if (> (point) current)
                      (progn
                        (setq current (point))
                        (goto-char stop))
                    (setq found nil move nil)))
                 (t (setq found t move nil))))))
        (setq found nil move nil)))
    found))

(defun tuareg2-inside-module-or-class-find-kwop ()
  (let ((kwop (tuareg2-find-kwop tuareg2-inside-module-or-class-regexp
                                "\\<\\(and\\|end\\)\\>")))
    (tuareg2-reset-and-kwop kwop)
    (when (string= kwop "with") (setq kwop nil))
    (if (string= kwop "end")
        (progn
          (tuareg2-find-match)
          (tuareg2-find-kwop tuareg2-inside-module-or-class-regexp)
          (tuareg2-inside-module-or-class-find-kwop))
      kwop)))

(defun tuareg2-inside-module-or-class-p ()
  (let ((begin) (end) (and-end) (and-iter t) (kwop t))
    (save-excursion
      (when (looking-at "\\<and\\>")
        (tuareg2-find-and-match))
      (setq begin (point))
      (unless (or (and (looking-at "\\<class\\>")
                       (save-excursion
                         (re-search-forward "\\<object\\>"
                                            (point-max) t)
                         (tuareg2-find-phrase-beginning)
                         (> (point) begin)))
                  (and (looking-at "\\<module\\>")
                       (save-excursion
                         (re-search-forward tuareg2-sig-struct-regexp
                                            (point-max) t)
                         (tuareg2-find-phrase-beginning)
                         (> (point) begin))))
        (unless (looking-at tuareg2-inside-module-or-class-opening-full)
          (setq kwop (tuareg2-inside-module-or-class-find-kwop)))
        (when kwop
          (setq begin (point))
          (when (tuareg2-search-forward-end)
            (tuareg2-backward-char 3)
            (when (looking-at "\\<end\\>")
              (tuareg2-forward-char 3)
              (setq end (point))
              (setq and-end (point))
              (tuareg2-skip-blank-and-comments)
              (while (and and-iter (looking-at "\\<and\\>"))
                (setq and-end (point))
                (when (tuareg2-search-forward-end)
                  (tuareg2-backward-char 3)
                  (when (looking-at "\\<end\\>")
                    (tuareg2-forward-char 3)
                    (setq and-end (point))
                    (tuareg2-skip-blank-and-comments)))
                (when (<= (point) and-end)
                  (setq and-iter nil)))
              (list begin end and-end))))))))

(defun tuareg2-move-inside-module-or-class-opening ()
  "Go to the beginning of the enclosing module or class.

Notice that white-lines (or comments) located immediately before a
module/class are considered enclosed in this module/class."
  (interactive)
  (let* ((old-point (point))
         (kwop (tuareg2-inside-module-or-class-find-kwop)))
    (unless kwop
      (goto-char old-point))
    (tuareg2-find-phrase-beginning)))

(defun tuareg2-discover-phrase (&optional quiet stop-at-and)
  (end-of-line)
  (let ((end (point)) (case-fold-search nil))
   (tuareg2-with-internal-syntax
    (tuareg2-find-phrase-beginning stop-at-and)
    (when (> (point) end) (setq end (point)))
    (save-excursion
      (let ((begin (point)) (cpt 0) (lines-left 0) (stop)
            (inside-module-or-class (tuareg2-inside-module-or-class-p))
            (looking-block
             (looking-at tuareg2-inside-module-or-class-opening-full)))
        (if (and looking-block inside-module-or-class)
            (progn
              (setq begin (nth 0 inside-module-or-class))
              (setq end (nth 2 inside-module-or-class))
              (goto-char end))
          (if inside-module-or-class
              (progn
                (setq stop (save-excursion
                             (goto-char (nth 1 inside-module-or-class))
                             (line-beginning-position)))
                (if (< stop end) (setq stop (point-max))))
            (setq stop (point-max)))
          (save-restriction
            (goto-char end)
            (while (and (= lines-left 0)
                        (or (not inside-module-or-class) (< (point) stop))
                        (<= (save-excursion
                              (tuareg2-find-phrase-beginning stop-at-and)) end))
              (unless quiet
                (setq cpt (1+ cpt))
                (when (= 8 cpt)
                  (message "Looking for enclosing phrase...")))
              (setq end (point))
              (tuareg2-skip-to-end-of-phrase)
              (narrow-to-region (line-beginning-position) (point-max))
              (goto-char end)
              (setq lines-left (forward-line 1)))))
        (when (>= cpt 8) (message "Looking for enclosing phrase... done."))
        (save-excursion (tuareg2-skip-blank-and-comments) (setq end (point)))
        (tuareg2-skip-back-blank-and-comments)
        (list begin (point) end))))))

(defun tuareg2-mark-phrase ()
  "Put mark at end of this OCaml phrase, point at beginning.
The OCaml phrase is the phrase just before the point."
  (interactive)
  (let ((pair (tuareg2-discover-phrase)))
    (goto-char (nth 1 pair)) (push-mark (nth 0 pair) t t)))

(defun tuareg2-next-phrase (&optional quiet stop-at-and)
  "Skip to the beginning of the next phrase."
  (interactive "i")
  (goto-char (save-excursion
               (nth 2 (tuareg2-discover-phrase quiet stop-at-and))))
  (cond
   ((looking-at "\\<end\\>")
    (tuareg2-next-phrase quiet stop-at-and))
   ((looking-at ")")
    (forward-char 1)
    (tuareg2-skip-blank-and-comments))
   ((looking-at ";;")
    (forward-char 2)
    (tuareg2-skip-blank-and-comments))))

(defun tuareg2-previous-phrase ()
  "Skip to the beginning of the previous phrase."
  (interactive)
  (beginning-of-line)
  (tuareg2-skip-to-end-of-phrase)
  (tuareg2-discover-phrase))

(defun tuareg2-indent-phrase ()
  "Depending of the context: justify and indent a comment,
or indent all lines in the current phrase."
  (interactive)
  (save-excursion
    (back-to-indentation)
    (if (tuareg2-in-comment-p)
        (let* ((cobpoint (save-excursion
                           (tuareg2-beginning-of-literal-or-comment)
                           (point)))
               (begpoint (save-excursion
                           (while (and (> (point) cobpoint)
                                       (tuareg2-in-comment-p)
                                       (not (looking-at "^[ \t]*$")))
                             (forward-line -1))
                           (max cobpoint (point))))
               (coepoint (save-excursion
                           (while (tuareg2-in-comment-p)
                             (re-search-forward "\\*)" nil 'end))
                           (point)))
               (endpoint (save-excursion
                           (re-search-forward "^[ \t]*$" coepoint 'end)
                           (line-beginning-position 2)))
               (leading-star (tuareg2-leading-star-p)))
          (goto-char begpoint)
          (while (and leading-star
                      (< (point) endpoint)
                      (not (looking-at "^[ \t]*$")))
            (forward-line 1)
            (back-to-indentation)
            (when (looking-at "\\*\\**\\([^)]\\|$\\)")
              (delete-char 1)
              (setq endpoint (1- endpoint))))
          (goto-char (min (point) endpoint))
          (fill-region begpoint endpoint)
          (re-search-forward "\\*)" nil 'end)
          (setq endpoint (point))
          (when leading-star
            (goto-char begpoint)
            (forward-line 1)
            (if (< (point) endpoint)
                (tuareg2-auto-fill-insert-leading-star t)))
          (indent-region begpoint endpoint nil))
      (let ((pair (tuareg2-discover-phrase)))
        (indent-region (nth 0 pair) (nth 1 pair) nil)))))

;;----------------------------------------------------------------------------;;
;; Keymap                                                                     ;;
;;----------------------------------------------------------------------------;;

(defvar tuareg2-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\M-q" 'tuareg2-indent-phrase)
    (define-key map "\C-c\C-q" 'tuareg2-indent-phrase)
    (define-key map "\M-\C-\\" 'indent-region)
    (define-key map "\C-c\C-a" 'tuareg2-find-alternate-file)
    (define-key map "\C-c\C-c" 'compile)
    (define-key map "\C-xnd" 'tuareg2-narrow-to-phrase)
    (define-key map "\M-\C-x" 'tuareg2-eval-phrase)
    (define-key map "\C-x\C-e" 'tuareg2-eval-phrase)
    (define-key map "\C-c\C-e" 'tuareg2-eval-phrase)
    (define-key map "\C-c\C-r" 'tuareg2-eval-region)
    (define-key map "\C-c\C-b" 'tuareg2-eval-buffer)
    (define-key map "\C-c\C-s" 'tuareg2-run-ocaml)
    (define-key map "\C-c\C-i" 'tuareg2-interrupt-ocaml)
    (define-key map "\C-c\C-k" 'tuareg2-kill-ocaml)
    (define-key map "\C-c\C-n" 'tuareg2-next-phrase)
    (define-key map "\C-c\C-p" 'tuareg2-previous-phrase)
    (define-key map [(backspace)] 'backward-delete-char-untabify)
    (define-key map [(control c) (home)] 'tuareg2-move-inside-module-or-class-opening)
    (define-key map [(control c) (control down)] 'tuareg2-next-phrase)
    (define-key map [(control c) (control up)] 'tuareg2-previous-phrase)
    (define-key map [(meta control down)]  'tuareg2-next-phrase)
    (define-key map [(meta control up)] 'tuareg2-previous-phrase)
    (define-key map [(meta control n)]  'tuareg2-next-phrase)
    (define-key map [(meta control p)] 'tuareg2-previous-phrase)
    (define-key map [(meta control h)] 'tuareg2-mark-phrase)
    (define-key map "\C-c`" 'tuareg2-interactive-next-error-source)
    (define-key map "\C-c?" 'tuareg2-interactive-next-error-source)
    (define-key map "\C-c.c" 'tuareg2-insert-class-form)
    (define-key map "\C-c.b" 'tuareg2-insert-begin-form)
    (define-key map "\C-c.f" 'tuareg2-insert-for-form)
    (define-key map "\C-c.w" 'tuareg2-insert-while-form)
    (define-key map "\C-c.i" 'tuareg2-insert-if-form)
    (define-key map "\C-c.l" 'tuareg2-insert-let-form)
    (define-key map "\C-c.m" 'tuareg2-insert-match-form)
    (define-key map "\C-c.t" 'tuareg2-insert-try-form)
    map)
  "Keymap used in Tuareg2 mode.")

(defun tuareg2-complete (arg)
  "Completes qualified ocaml identifiers."
  (interactive "p")
  (modify-syntax-entry ?_ "w" tuareg2-mode-syntax-table)
  (caml-complete arg)
  (modify-syntax-entry ?_ "_" tuareg2-mode-syntax-table))

;;----------------------------------------------------------------------------;;
;; Misc                                                                       ;;
;;----------------------------------------------------------------------------;;

(defun tuareg2-find-alternate-file ()
  "Switch Implementation/Interface."
  (interactive)
  (let ((name (buffer-file-name)))
    (when (string-match "\\`\\(.*\\)\\.ml\\(i\\)?\\'" name)
      (find-file (concat (tuareg2-match-string 1 name)
                         (if (match-beginning 2) ".ml" ".mli"))))))

;;----------------------------------------------------------------------------;;
;; Major mode                                                                 ;;
;;----------------------------------------------------------------------------;;

(defun tuareg2-mode ()
  "Major mode for editing OCaml code.

Dedicated to GNU Emacs, version 23 and higher. Provides
automatic indentation and compilation interface. Performs font/color
highlighting using Font-Lock. It is designed for OCaml but handles
Caml Light as well.

Report bugs, remarks and questions to Albert.Cohen@prism.uvsq.fr.

The Font-Lock minor-mode is used according to your customization
options.

You have better byte-compile tuareg2.el.

For customization purposes, you should use `tuareg2-mode-hook'
\(run for every file) or `tuareg2-load-hook' (run once) and not patch
the mode itself. You should add to your configuration file something like:
  (add-hook 'tuareg2-mode-hook
            (lambda ()
               ... ; your customization code
            ))
For example you can change the indentation of some keywords, the
`electric' flags, Font-Lock colors... Every customizable variable is
documented, use `C-h-v' or look at the mode's source code.

For the best indentation experience, some elementary rules must be followed.
  - Because the `function' keyword has a special indentation (to handle
    case matches) use the `fun' keyword when no case match is performed.
  - In OCaml, `;;' is no longer necessary for correct indentation,
    except before top level phrases not introduced by `type', `val', `let'
    etc. (i.e., phrases used for their side-effects or to be executed
    in a top level.)
  - Long sequences of `and's may slow down indentation slightly, since
    some computations (few) require to go back to the beginning of the
    sequence. Some very long nested blocks may also lead to slow
    processing of `end's, `else's, `done's...
  - Multiline strings are handled properly, but you may prefer string
    concatenation `^' to break long strings (the C-j keystroke can help).
  - Comment indentation is often a matter of taste and context, yet
    sophisticated heuristics provide reasonable indentation in most cases.
    When inserting a comment right before the code it refers to, it is
    generally expected that this comment will be aligned with the folowing
    code; to enforce this, leave a blank line before the comment.

Known bugs:
  - When writting a line with mixed code and comments, avoid putting
    comments at the beginning or middle of the text. More precisely,
    writing comments immediately after `=' or parentheses then writing
    some more code on the line leads to indentation errors. You may write
    `let x (* blah *) = blah' but should avoid `let x = (* blah *) blah'.

Short cuts for the Tuareg2 mode:
\\{tuareg2-mode-map}

Short cuts for interactions with the REPL:
\\{tuareg2-interactive-mode-map}"
  (interactive)
  (kill-all-local-variables)
  (setq major-mode 'tuareg2-mode)
  (setq mode-name "Tuareg2")
  (use-local-map tuareg2-mode-map)
  (set-syntax-table tuareg2-mode-syntax-table)
  (setq local-abbrev-table tuareg2-mode-abbrev-table)
  (make-local-variable 'paragraph-start)
  (setq paragraph-start (concat "^[ \t]*$\\|\\*)$\\|" page-delimiter))
  (make-local-variable 'paragraph-separate)
  (setq paragraph-separate paragraph-start)
  (make-local-variable 'require-final-newline)
  (setq require-final-newline mode-require-final-newline)
  (make-local-variable 'comment-start)
  (setq comment-start "(* ")
  (make-local-variable 'comment-end)
  (setq comment-end " *)")
  (make-local-variable 'comment-column)
  (setq comment-column 40)
  (make-local-variable 'comment-start-skip)
  (setq comment-start-skip "(\\*+[ \t]*")
  (make-local-variable 'comment-multi-line)
  (setq comment-multi-line t)
  (make-local-variable 'parse-sexp-ignore-comments)
  (setq parse-sexp-ignore-comments nil)
  (make-local-variable 'indent-line-function)
  (setq indent-line-function 'tuareg2-indent-command)
  (make-local-variable 'normal-auto-fill-function)
  (setq normal-auto-fill-function 'tuareg2-auto-fill-function)

  ;; Hooks for tuareg2-mode, use them for tuareg2-mode configuration
  (tuareg2-install-font-lock)
  (run-hooks 'tuareg2-mode-hook)
  (message nil))

;;----------------------------------------------------------------------------;;
;; Hooks                                                                      ;;
;;----------------------------------------------------------------------------;;

(defvar tuareg2-load-hook nil
  "This hook is run when Tuareg2 is loaded in. It is a good place to put
key-bindings or hack Font-Lock keywords...")

(run-hooks 'tuareg2-load-hook)

;;----------------------------------------------------------------------------;;
;; End                                                                        ;;
;;----------------------------------------------------------------------------;;

(provide 'tuareg2)

