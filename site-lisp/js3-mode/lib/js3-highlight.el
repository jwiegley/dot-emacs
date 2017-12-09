;;; js3-highlight.el --- JavaScript syntax coloring support

;;; Code:


(defsubst js3-set-face (beg end face &optional record)
  "Fontify a region.  If RECORD is non-nil, record for later."
  (when (plusp js3-highlight-level)
    (setq beg (min (point-max) beg)
          beg (max (point-min) beg)
          end (min (point-max) end)
          end (max (point-min) end))
    (if record
        (push (list beg end face) js3-mode-fontifications)
      (put-text-property beg end 'font-lock-face face))))

(defsubst js3-set-kid-face (pos kid len face)
  "Set-face on a child node.
POS is absolute buffer position of parent.
KID is the child node.
LEN is the length to fontify.
FACE is the face to fontify with."
  (js3-set-face (+ pos (js3-node-pos kid))
                (+ pos (js3-node-pos kid) (js3-node-len kid))
                face))

(defsubst js3-fontify-kwd (start length)
  (js3-set-face start (+ start length) 'font-lock-keyword-face))

(defsubst js3-clear-face (beg end)
  (remove-text-properties beg end '(font-lock-face nil
						   help-echo nil
						   point-entered nil
						   c-in-sws nil)))

(defconst js3-ecma-global-props
  (concat "^"
          (regexp-opt
           '("Infinity" "NaN" "undefined" "arguments") t)
          "$")
  "Value properties of the Ecma-262 Global Object.
Shown at or above `js3-highlight-level' 2.")

;; might want to add the name "arguments" to this list?
(defconst js3-ecma-object-props
  (concat "^"
          (regexp-opt
           '("prototype" "__proto__" "__parent__") t)
          "$")
  "Value properties of the Ecma-262 Object constructor.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-global-funcs
  (concat
   "^"
   (regexp-opt
    '("decodeURI" "decodeURIComponent" "encodeURI" "encodeURIComponent"
      "eval" "isFinite" "isNaN" "parseFloat" "parseInt") t)
   "$")
  "Function properties of the Ecma-262 Global object.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-number-props
  (concat "^"
          (regexp-opt '("MAX_VALUE" "MIN_VALUE" "NaN"
                        "NEGATIVE_INFINITY"
                        "POSITIVE_INFINITY") t)
          "$")
  "Properties of the Ecma-262 Number constructor.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-date-props "^\\(parse\\|UTC\\)$"
  "Properties of the Ecma-262 Date constructor.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-math-props
  (concat "^"
          (regexp-opt
           '("E" "LN10" "LN2" "LOG2E" "LOG10E" "PI" "SQRT1_2" "SQRT2")
           t)
          "$")
  "Properties of the Ecma-262 Math object.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-math-funcs
  (concat "^"
          (regexp-opt
           '("abs" "acos" "asin" "atan" "atan2" "ceil" "cos" "exp" "floor"
             "log" "max" "min" "pow" "random" "round" "sin" "sqrt" "tan") t)
          "$")
  "Function properties of the Ecma-262 Math object.
Shown at or above `js3-highlight-level' 2.")

(defconst js3-ecma-function-props
  (concat
   "^"
   (regexp-opt
    '(;; properties of the Object prototype object
      "hasOwnProperty" "isPrototypeOf" "propertyIsEnumerable"
      "toLocaleString" "toString" "valueOf"
      ;; properties of the Function prototype object
      "apply" "call"
      ;; properties of the Array prototype object
      "concat" "join" "pop" "push" "reverse" "shift" "slice" "sort"
      "splice" "unshift"
      ;; properties of the String prototype object
      "charAt" "charCodeAt" "fromCharCode" "indexOf" "lastIndexOf"
      "localeCompare" "match" "replace" "search" "split" "substring"
      "toLocaleLowerCase" "toLocaleUpperCase" "toLowerCase"
      "toUpperCase"
      ;; properties of the Number prototype object
      "toExponential" "toFixed" "toPrecision"
      ;; properties of the Date prototype object
      "getDate" "getDay" "getFullYear" "getHours" "getMilliseconds"
      "getMinutes" "getMonth" "getSeconds" "getTime"
      "getTimezoneOffset" "getUTCDate" "getUTCDay" "getUTCFullYear"
      "getUTCHours" "getUTCMilliseconds" "getUTCMinutes" "getUTCMonth"
      "getUTCSeconds" "setDate" "setFullYear" "setHours"
      "setMilliseconds" "setMinutes" "setMonth" "setSeconds" "setTime"
      "setUTCDate" "setUTCFullYear" "setUTCHours" "setUTCMilliseconds"
      "setUTCMinutes" "setUTCMonth" "setUTCSeconds" "toDateString"
      "toLocaleDateString" "toLocaleString" "toLocaleTimeString"
      "toTimeString" "toUTCString"
      ;; properties of the RegExp prototype object
      "exec" "test"
      ;; SpiderMonkey/Rhino extensions, versions 1.5+
      "toSource" "__defineGetter__" "__defineSetter__"
      "__lookupGetter__" "__lookupSetter__" "__noSuchMethod__"
      "every" "filter" "forEach" "lastIndexOf" "map" "some")
    t)
   "$")
  "Built-in functions defined by Ecma-262 and SpiderMonkey extensions.
Shown at or above `js3-highlight-level' 3.")

(defsubst js3-parse-highlight-prop-get (parent target prop call-p)
  (let ((target-name (and target
                          (js3-name-node-p target)
                          (js3-name-node-name target)))
        (prop-name (if prop (js3-name-node-name prop)))
        (level1 (>= js3-highlight-level 1))
        (level2 (>= js3-highlight-level 2))
        (level3 (>= js3-highlight-level 3))
        pos
        face)
    (when level2
      (if call-p
          (cond
           ((and target prop)
            (cond
             ((and level3 (string-match js3-ecma-function-props prop-name))
              (setq face 'font-lock-builtin-face))
             ((and target-name prop)
              (cond
               ((string= target-name "Date")
                (if (string-match js3-ecma-date-props prop-name)
                    (setq face 'font-lock-builtin-face)))
               ((string= target-name "Math")
                (if (string-match js3-ecma-math-funcs prop-name)
                    (setq face 'font-lock-builtin-face)))))))
           (prop
            (if (string-match js3-ecma-global-funcs prop-name)
                (setq face 'font-lock-builtin-face))))
        (cond
         ((and target prop)
          (cond
           ((string= target-name "Number")
            (if (string-match js3-ecma-number-props prop-name)
                (setq face 'font-lock-constant-face)))
           ((string= target-name "Math")
            (if (string-match js3-ecma-math-props prop-name)
                (setq face 'font-lock-constant-face)))))
         (prop
          (if (string-match js3-ecma-object-props prop-name)
              (setq face 'font-lock-constant-face)))))
      (when face
        (js3-set-face (setq pos (+ (js3-node-pos parent) ; absolute
                                   (js3-node-pos prop))) ; relative
                      (+ pos (js3-node-len prop))
                      face)))))

(defun js3-parse-highlight-member-expr-node (node)
  "Perform syntax highlighting of EcmaScript built-in properties.
The variable `js3-highlight-level' governs this highighting."
  (let (face target prop name pos end parent call-p callee)
    (cond
     ;; case 1:  simple name, e.g. foo
     ((js3-name-node-p node)
      (setq name (js3-name-node-name node))
      ;; possible for name to be nil in rare cases - saw it when
      ;; running js3-mode on an elisp buffer.  Might as well try to
      ;; make it so js3-mode never barfs.
      (when name
        (setq face (if (string-match js3-ecma-global-props name)
                       'font-lock-constant-face))
        (when face
          (setq pos (js3-node-pos node)
                end (+ pos (js3-node-len node)))
          (js3-set-face pos end face))))
     ;; case 2:  property access or function call
     ((or (js3-prop-get-node-p node)
          ;; highlight function call if expr is a prop-get node
          ;; or a plain name (i.e. unqualified function call)
          (and (setq call-p (js3-call-node-p node))
               (setq callee (js3-call-node-target node)) ; separate setq!
               (or (js3-prop-get-node-p callee)
                   (js3-name-node-p callee))))
      (setq parent node
            node (if call-p callee node))
      (if (and call-p (js3-name-node-p callee))
          (setq prop callee)
        (setq target (js3-prop-get-node-left node)
              prop (js3-prop-get-node-right node)))
      (cond
       ((js3-name-node-p target)
        (if (js3-name-node-p prop)
            ;; case 2a:  simple target, simple prop name, e.g. foo.bar
            (js3-parse-highlight-prop-get parent target prop call-p)
          ;; case 2b:  simple target, complex name, e.g. foo.x[y]
          (js3-parse-highlight-prop-get parent target nil call-p)))
       ((js3-name-node-p prop)
        ;; case 2c:  complex target, simple name, e.g. x[y].bar
        (js3-parse-highlight-prop-get parent target prop call-p)))))))

(defun js3-parse-highlight-member-expr-fn-name (expr)
  "Highlight the `baz' in function foo.bar.baz(args) {...}.
This is experimental Rhino syntax.  EXPR is the foo.bar.baz member expr.
We currently only handle the case where the last component is a prop-get
of a simple name.  Called before EXPR has a parent node."
  (let (pos
        (name (and (js3-prop-get-node-p expr)
                   (js3-prop-get-node-right expr))))
    (when (js3-name-node-p name)
      (js3-set-face (setq pos (+ (js3-node-pos expr)  ; parent is absolute
                                 (js3-node-pos name)))
                    (+ pos (js3-node-len name))
                    'font-lock-function-name-face
                    'record))))

;; source:  http://jsdoc.sourceforge.net/
;; Note - this syntax is for Google's enhanced jsdoc parser that
;; allows type specifications, and needs work before entering the wild.

(defconst js3-jsdoc-param-tag-regexp
  (concat "^\\s-*\\*+\\s-*\\(@"
          "\\(?:param\\|argument\\)"
          "\\)"
          "\\s-*\\({[^}]+}\\)?"         ; optional type
          "\\s-*\\([a-zA-Z0-9_$]+\\)?"  ; name
          "\\>")
  "Matches jsdoc tags with optional type and optional param name.")

(defconst js3-jsdoc-typed-tag-regexp
  (concat "^\\s-*\\*+\\s-*\\(@\\(?:"
          (regexp-opt
           '("enum"
             "extends"
             "field"
             "id"
             "implements"
             "lends"
             "mods"
             "requires"
             "return"
             "returns"
             "throw"
             "throws"))
          "\\)\\)\\s-*\\({[^}]+}\\)?")
  "Matches jsdoc tags with optional type.")

(defconst js3-jsdoc-arg-tag-regexp
  (concat "^\\s-*\\*+\\s-*\\(@\\(?:"
          (regexp-opt
           '("alias"
             "augments"
             "borrows"
             "bug"
             "base"
             "config"
             "default"
             "define"
             "exception"
             "function"
             "member"
             "memberOf"
             "name"
             "namespace"
             "property"
             "since"
             "suppress"
             "this"
             "throws"
             "type"
             "version"))
          "\\)\\)\\s-+\\([^ \t]+\\)")
  "Matches jsdoc tags with a single argument.")

(defconst js3-jsdoc-empty-tag-regexp
  (concat "^\\s-*\\*+\\s-*\\(@\\(?:"
          (regexp-opt
           '("addon"
             "author"
             "class"
             "const"
             "constant"
             "constructor"
             "constructs"
             "deprecated"
             "desc"
             "description"
             "event"
             "example"
             "exec"
             "export"
             "fileoverview"
             "final"
             "function"
             "hidden"
             "ignore"
             "implicitCast"
             "inheritDoc"
             "inner"
             "interface"
             "license"
             "noalias"
             "noshadow"
             "notypecheck"
             "override"
             "owner"
             "preserve"
             "preserveTry"
             "private"
             "protected"
             "public"
             "static"
             "supported"
             ))
          "\\)\\)\\s-*")
  "Matches empty jsdoc tags.")

(defconst js3-jsdoc-link-tag-regexp
  "{\\(@\\(?:link\\|code\\)\\)\\s-+\\([^#}\n]+\\)\\(#.+\\)?}"
  "Matches a jsdoc link or code tag.")

(defconst js3-jsdoc-see-tag-regexp
  "^\\s-*\\*+\\s-*\\(@see\\)\\s-+\\([^#}\n]+\\)\\(#.+\\)?"
  "Matches a jsdoc @see tag.")

(defconst js3-jsdoc-html-tag-regexp
  "\\(</?\\)\\([a-zA-Z]+\\)\\s-*\\(/?>\\)"
  "Matches a simple (no attributes) html start- or end-tag.")

(defsubst js3-jsdoc-highlight-helper ()
  (js3-set-face (match-beginning 1)
                (match-end 1)
                'js3-jsdoc-tag-face)
  (if (match-beginning 2)
      (if (save-excursion
            (goto-char (match-beginning 2))
            (= (char-after) ?{))
          (js3-set-face (1+ (match-beginning 2))
                        (1- (match-end 2))
                        'js3-jsdoc-type-face)
        (js3-set-face (match-beginning 2)
                      (match-end 2)
                      'js3-jsdoc-value-face)))
  (if (match-beginning 3)
      (js3-set-face (match-beginning 3)
                    (match-end 3)
                    'js3-jsdoc-value-face)))

(defun js3-highlight-jsdoc (ast)
  "Highlight doc comment tags."
  (let ((comments (js3-ast-root-comments ast))
        beg end)
    (save-excursion
      (dolist (node comments)
        (when (eq (js3-comment-node-format node) 'jsdoc)
          (setq beg (js3-node-abs-pos node)
                end (+ beg (js3-node-len node)))
          (save-restriction
            (narrow-to-region beg end)
            (dolist (re (list js3-jsdoc-param-tag-regexp
                              js3-jsdoc-typed-tag-regexp
                              js3-jsdoc-arg-tag-regexp
                              js3-jsdoc-link-tag-regexp
                              js3-jsdoc-see-tag-regexp
                              js3-jsdoc-empty-tag-regexp))
              (goto-char beg)
              (while (re-search-forward re nil t)
                (js3-jsdoc-highlight-helper)))
            ;; simple highlighting for html tags
            (goto-char beg)
            (while (re-search-forward js3-jsdoc-html-tag-regexp nil t)
              (js3-set-face (match-beginning 1)
                            (match-end 1)
                            'js3-jsdoc-html-tag-delimiter-face)
              (js3-set-face (match-beginning 2)
                            (match-end 2)
                            'js3-jsdoc-html-tag-name-face)
              (js3-set-face (match-beginning 3)
                            (match-end 3)
                            'js3-jsdoc-html-tag-delimiter-face))))))))

(defun js3-highlight-assign-targets (node left right)
  "Highlight function properties and external variables."
  (let (leftpos end name)
    ;; highlight vars and props assigned function values
    (when (js3-function-node-p right)
      (cond
       ;; var foo = function() {...}
       ((js3-name-node-p left)
        (setq name left))
       ;; foo.bar.baz = function() {...}
       ((and (js3-prop-get-node-p left)
             (js3-name-node-p (js3-prop-get-node-right left)))
        (setq name (js3-prop-get-node-right left))))
      (when name
        (js3-set-face (setq leftpos (js3-node-abs-pos name))
                      (+ leftpos (js3-node-len name))
                      'font-lock-function-name-face
                      'record)))))

(defun js3-record-name-node (node)
  "Saves NODE to `js3-recorded-identifiers' to check for undeclared variables
later. NODE must be a name node."
  (let (leftpos end)
    (push (list node js3-current-scope
                (setq leftpos (js3-node-abs-pos node))
                (setq end (+ leftpos (js3-node-len node))))
          js3-recorded-identifiers)))

(defun js3-highlight-undeclared-vars ()
  "After entire parse is finished, look for undeclared variable references.
We have to wait until entire buffer is parsed, since JavaScript permits var
decls to occur after they're used.

If any undeclared var name is in `js3-externs' or `js3-additional-externs',
it is considered declared."
  (let (name)
    (dolist (entry js3-recorded-identifiers)
      (destructuring-bind (name-node scope pos end) entry
                          (setq name (js3-name-node-name name-node))
                          (unless (or (member name js3-global-externs)
                                      (member name js3-default-externs)
                                      (member name js3-additional-externs)
				      (member name js3-declared-globals)
                                      (js3-get-defining-scope scope name))
                            (js3-set-face pos end 'js3-external-variable-face 'record)
                            (js3-record-text-property pos end 'help-echo "Undeclared variable")
                            (js3-record-text-property pos end 'point-entered 'js3-echo-help))))
    (setq js3-recorded-identifiers nil)))

(provide 'js3-highlight)

;;; js3-highlight.el ends here
