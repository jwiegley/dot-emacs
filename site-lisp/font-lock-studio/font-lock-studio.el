;;; font-lock-studio.el --- interactive debugger for Font Lock keywords.

;; Copyright (C) 2013-2017 Anders Lindgren

;; Author: Anders Lindgren
;; Keywords: faces, tools
;; Created: 2013-12-07
;; Version: 0.0.7
;; URL: https://github.com/Lindydancer/font-lock-studio
;; Package-Requires: ((emacs "24.3"))

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

;;; Commentary:

;; Interactive debugger for font-lock keywords (Emacs syntax
;; highlighting rules).
;;
;; Font Lock Studio lets you *single-step* Font Lock keywords --
;; matchers, highlights, and anchored rules, so that you can see what
;; happens when a buffer is fontified. You can set *breakpoints* on or
;; inside rules and *run* until one has been hit. When inside a rule,
;; matches are *visualized* using a palette of background colors. The
;; *explainer* can describe a rule in plain-text English. Tight
;; integration with *Edebug* allows you to step into Lisp expressions
;; that are part of the Font Lock keywords.

;; Usage:
;;
;; When using the debugger, an *interface buffer* is displayed, it
;; contains all the keywords and is used for navigation and
;; visalization of match data.
;;
;; When Font Lock Studio is started, comments and strings are
;; pre-colored, as they are part of the earlier *syntactic phase*
;; (which isn't supported by Font Lock Studio).
;;
;; Start the debugger by typing `M-x font-lock-studio RET'. Press `?'
;; or see the menu for available commands.
;;
;; Why use a debugger?:
;;
;; You might be the author of Font Lock keywords for a major more, you
;; might simply want to add your own personal highlighting rules, or
;; you simply would like to know more about how Font Lock keywords
;; work.
;;
;; Regardless of your background and ambition, there is a world of
;; difference between simply reading Font Lock keywords and being able
;; to step through the rules and exactly see what they do. In fact, as
;; part of writing Font Lock Studio, I learned some new Font Lock
;; tricks from various major modes -- despite having 15+ years of
;; experience with Font Lock.

;; Example:
;;
;; For a buffer using `html-mode', the interface buffer looks the
;; following. Other major modes typically have more and more complex
;; rules. The arrow on the left indicates the current active location.
;; A corresponding arrow in the source buffer is placed at the current
;; search location.
;;
;;
;;             ========================
;;             === Font Lock Studio ===
;;             ========================
;;         --------------------------------------------------
;;     =>  "<\\([!?][_:[:alpha:]][-_.:[:alnum:]]*\\)"
;;           (1 font-lock-keyword-face)
;;         --------------------------------------------------
;;         "</?\\([_[:alpha:]][-_.[:alnum:]]*\\)\\(?::\\([_:[:alpha:]]
;;         [-_.:[:alnum:]]*\\)\\)?"
;;           (1
;;            (if
;;                (match-end 2)
;;                sgml-namespace-face font-lock-function-name-face))
;;           (2 font-lock-function-name-face nil t)
;;         --------------------------------------------------
;;         "\\(?:^\\|[ \t]\\)\\([_[:alpha:]][-_.[:alnum:]]*\\)\\(?::
;;         \\([_:[:alpha:]][-_.:[:alnum:]]*\\)\\)?=[\"']"
;;           (1
;;            (if
;;                (match-end 2)
;;                sgml-namespace-face font-lock-variable-name-face))
;;           (2 font-lock-variable-name-face nil t)
;;         --------------------------------------------------
;;         "[&%][_:[:alpha:]][-_.:[:alnum:]]*;?"
;;           (0 font-lock-variable-name-face)
;;         --------------------------------------------------
;;         "<\\(b\\(?:ig\\|link\\)\\|cite\\|em\\|h[1-6]\\|rev\\|s\\(?:
;;         mall\\|trong\\)\\|t\\(?:itle\\|t\\)\\|var\\|[bisu]\\)
;;         \\([ \t][^>]*\\)?>\\([^<]+\\)</\\1>"
;;           (3
;;            (cdr
;;             (assoc-string
;;              (match-string 1)
;;              sgml-tag-face-alist t))
;;            prepend)
;;         ==================================================
;;         Public state:
;;           Debug on error     : YES
;;           Debug on quit      : YES
;;           Explain rules      : YES
;;           Show compiled code : NO
;;
;; Press space to single step through all the keywords. "n" will go
;; the the next keyword, "b" will set a breakpoint, "g" will run to
;; the end (or to the next breakpoint) and "q" will quit.
;;
;; In the following screenshot, you will see the debugger in action.
;; The user has stepped into the last rule (for the second out of
;; three times) -- the matches are visualized in the regexp, in the
;; source buffer and in the highlight rule. In addition, *auto
;; explainer* is active so the rule is described in english.
;; Furthermore, the red text means a *breakpoint* is set, in this case
;; on a highlight rule, which is part of a Font Lock keyword rule.
;;
;; ![See doc/demo.png for screenshot of Font Lock Studio](doc/demo.png)

;; Features:
;;
;; Stepping:
;;
;; You can single *step into*, *over*, and *out* of Font Lock
;; keywords. *Anchored* rules are fully supported. In addition, you
;; can *run* to the end or to the next breakpoint.
;;
;; Breakpoints:
;;
;; You can set breakpoints on part of the keyword, like the matcher
;; (e.g. the regexp), a highlight rule, or inside an anchored highlight
;; rule.
;;
;; If you want to step or run without stopping on breakpoints, prefix
;; the command with `C-u'.
;;
;; Note that in an anchored rule, you can set a breakpoints either on
;; the entire rule or on an individual part. In the former case, only
;; the outer parentheses are highlighted.
;;
;; Match Data Visualization:
;;
;; After the *matcher* of a keyword or anchored highlight has been
;; executed, the match data (whatever the search found) is visualized
;; using background colors in the source buffer, in the regexp, and
;; over the corresponding highlight rule or rules. If part of a regexp
;; or a highlight didn't match, it is not colored, this can for
;; example happen when the postfix regexp operator `?' is used.
;;
;; Note that an inner match group gets precedence over an outer group.
;; This can lead to situations where a highlight rule gets a color
;; that doesn't appear in the regexp or in the source buffer. For
;; example, the matcher "\\(abc\\)" will be colored with the color for
;; match 1, while the higlight rule `(0 a-face)' gets the color for
;; match 0.
;;
;; Normalized keywords:
;;
;; The keywords presented in the interface have been normalized. For
;; example, instead of
;;
;;      ("xyz" . font-lock-type-face)
;;
;; the keyword
;;
;;       ("xyz" (0 font-lock-type-face))
;;
;; is shown. See `font-lock-studio-normalize-keywords' for details.
;;
;; Explainer:
;;
;; The *explainer* echoes a human-readble description of the current
;; part of the Font Lock keywords. This help you to understand that
;; all those `nil':s and `t':s in the rules actually mean.
;;
;; When using the *auto explainer*, Font Lock Studio echoes the
;; explanation after each command.
;;
;; Edebug -- the Emacs Lisp debugger:
;;
;; Tight integration with Edebug allows you to single-step expressions
;; embedded in the keywords in the interface buffer, and it allows you
;; to instrument called functions for debugging in their source file.
;;
;; Follow mode awareness:
;;
;; The search location in the source buffer is visualized by an
;; overlay arrow and by updating the point. If the source buffer is
;; visible in multiple side-by-side windows and Follow mode is
;; enabled, the search location will be shown in a suitable windows to
;; minimize scrolling.

;; Tips and trix:
;;
;; The "Hanging Emacs" problem:
;;
;; Traditionally, if you use a function as a matcher and that function
;; doesn't return -- Emacs hangs and all you can do is to kill it and
;; restart. (I know from personal experience that it's not uncommon
;; for functions that parse text to hang -- for example, when you have
;; forgotten to check for the end-of-buffer.) When using font-lock
;; studio, you can simply press `C-q' to exit.
;;
;; If you have a source file that hangs Emacs when loaded, first
;; disable font-lock using `M-x global-font-lock-mode RET' before
;; loading the file, and finally launch Font-Lock studio.
;;
;; `cc-mode' keywords:
;;
;; The keywords provided by major modes like `c-mode', `objc-mode',
;; `cpp-mode' that are based on `cc-mode' contain *byte-compiled*
;; font-lock keywords, which are unreadable and undebugable. To use
;; corresponding keywords with *uncompiled* code, copy the file
;; `cc-fonts.el', replace explicit calls to `byte-compile' with `eval'
;; and issue `M-x eval-buffer RET'.

;; Implementation overview:
;;
;; State-machine fontification engine:
;;
;; Font Lock Studio provides it's own fontification engine, designed
;; to for things needed by a debugger such as single-stepping and
;; breakpoints. This fontification engine lacks a lot of features of
;; the real font-lock fontification engine, such as the speed and the
;; ability to refontify when the buffer is modified.
;;
;; The fontification engine can be used without an interface buffer.
;;
;; Regexp decomposer:
;;
;; In order for to visualize the groups in regexp:s that corresponds
;; to matches, they must be located. This requires a non-trivial
;; *regexp parser*.

;; Other Font Lock Tools:
;;
;; This package is part of a suite of font-lock tools.  The other
;; tools in the suite are:
;;
;;
;; Font Lock Profiler:
;;
;; A profiler for font-lock keywords.  This package measures time and
;; counts the number of times each part of a font-lock keyword is
;; used.  For matchers, it counts the total number and the number of
;; successful matches.
;;
;; The result is presented in table that can be sorted by count or
;; time.  The table can be expanded to include each part of the
;; font-lock keyword.
;;
;; In addition, this package can generate a log of all font-lock
;; events.  This can be used to verify font-lock implementations,
;; concretely, this is used for back-to-back tests of the real
;; font-lock engine and Font Lock Studio, an interactive debugger for
;; font-lock keywords.
;;
;;
;; Highlight Refontification:
;;
;; Minor mode that visualizes how font-lock refontifies a buffer.
;; This is useful when developing or debugging font-lock keywords,
;; especially for keywords that span multiple lines.
;;
;; The background of the buffer is painted in a rainbow of colors,
;; where each band in the rainbow represent a region of the buffer
;; that has been refontified.  When the buffer is modified, the
;; rainbow is updated.
;;
;;
;; Faceup:
;;
;; Emacs is capable of highlighting buffers based on language-specific
;; `font-lock' rules. This package makes it possible to perform
;; regression test for packages that provide font-lock rules.
;;
;; The underlying idea is to convert text with highlights ("faces")
;; into a plain text representation using the Faceup markup
;; language. This language is semi-human readable, for example:
;;
;;     «k:this» is a keyword
;;
;; By comparing the current highlight with a highlight performed with
;; stable versions of a package, it's possible to automatically find
;; problems that otherwise would have been hard to spot.
;;
;; This package is designed to be used in conjunction with Ert, the
;; standard Emacs regression test system.
;;
;; The Faceup markup language is a generic markup language, regression
;; testing is merely one way to use it.
;;
;;
;; Font Lock Regression Suite:
;;
;; A collection of example source files for a large number of
;; programming languages, with ERT tests to ensure that syntax
;; highlighting does not accidentally change.
;;
;; For each source file, font-lock reference files are provided for
;; various Emacs versions.  The reference files contains a plain-text
;; representation of source file with syntax highlighting, using the
;; format "faceup".
;;
;; Of course, the collection source file can be used for other kinds
;; of testing, not limited to font-lock regression testing.

;;; Code:

;; ----------------------------------------
;; Note: Everything above "Code" will be part of the GitHub README.md
;; file.

;; Naming convention:
;;
;; Source buffer    -- the buffer being fontified.
;;
;; Interface buffer -- the buffer containing the debugger interface.
;;
;; Control buffer   -- a buffer holding information about the
;;                     fontification using buffer-local variables,
;;                     typically the interface buffer. However, the
;;                     fontification engine can be used by itself, in
;;                     which case this can be any buffer including a
;;                     temporary buffer and the source buffer itself.

;; Known Problems:
;;
;; - Sometimes, the interface buffer is not displayed. (Could it be
;;   that it is first shown, then it tries to show the source buffer
;;   and it reuses the same window?)

;; Open issues:
;;
;; - Is C-u really a good idea for non-stop? It doesn't show up in the
;;   menu and C-h m. Maybe do something like "s" steps and "S" steps
;;   nonstop. (Note: There is no shifted space.)
;;
;; - A hidden compiled matched in an anchored rule without pre, post,
;;   and matcher (which is illegal, by the way) is rendered "(;;
;;   Compiled code (hidden))". This doesn't look that good as the
;;   closing parenthesis is drawn at the end of the comment. For now,
;;   I guess we can live with it. (See C mode for an example.)
;;
;; - Replace "predicate" with "form", to makes it easier to call.
;;   However, keeping the lambda construct makes it clearer that that
;;   it's a callback.
;;
;; - Maybe rename `font-lock-studio-fontify-step' to avoid confusion
;;   with the normal step commands. However, I need a good name,
;;   "tick-state-machine"?

;; Future ideas:
;;
;; - Support for debugging the "syntactic" font-lock phase.
;;
;; - Collect statistics, including timing information.
;;
;; - Disable rules. (Could use the same mechanism used by
;;   breakpoints.)
;;
;; - Breakpoints in source buffer.
;;
;; - Save and restore breakpoints.
;;
;; - Visualize when a keyword has been normalized.
;;
;; - Customize support.
;;
;; - Print code better (indented, font-locked, lambda and parameter
;;   list on the same line).
;;
;; - bind debug-on-error and debug-on-quit temporarily (like edebug does).

;; Random notes:
;;
;; Note on the syntax: Inside a backtick-lambda, "abc" is the value of
;; the expression "abc" at the time the lambda is called, and ",abc"
;; is the current value.
;;
;; Interface buffer:
;;
;; After each command, the interface buffer is erased and filled with
;; new content using a *renderer*. Or, rather, that is how it is
;; intended to work. However, when doing so, windows displaying the
;; buffer drop their start position. Instead, when the interface
;; buffer is drawn, it replaces the existing content line-by-line.
;;

;; ----------------------------------------
;; Byte-compile support
;;

(eval-when-compile
  ;; Note, in modern Emacs version, cl-lib should be used. However,
  ;; it's not available (without using extra packages) in older Emacs
  ;; versions.
  (require 'cl)                         ; For `assert'.
  (defvar follow-mode))

(declare-function follow-post-command-hook "follow.el")
(declare-function edebug-instrument-function "edebug.el")
(declare-function edebug-read-and-maybe-wrap-form "edebug.el")


;; ----------------------------------------
;; Variables
;;

;; --------------------
;; Public variables
;;

(defvar font-lock-studio-color-list-light '("chartreuse1"
                                            "tan1"
                                            "PaleTurquoise2"
                                            "gold1"
                                            "grey85"
                                            "OliveDrab2"
                                            "Yellow")
  "*List of light colors suitable for match data visualization.")


(defvar font-lock-studio-color-list-medium '("Cyan"
                                             "Orange"
                                             "OliveDrab3"
                                             "grey75"
                                             "yellow3"
                                             "orchid1")
  "*List of medium colors suitable for match data visualization.")


(defvar font-lock-studio-color-list-dark '("DeepSkyBlue"
                                           "chocolate"
                                           "Green"
                                           "grey65"
                                           "gold3"
                                           "orchid3")
  "*List of dark colors suitable for match data visualization.")


(defvar font-lock-studio-color-scheme 'light-to-dark
  "*The preferred colors used for match data visualization.

This can be one of:

     `dark-to-light'  -- Start with light colors, end with dark.
     `light-to-dark'  -- Start with dark colors, end with light.
     `light'          -- Light colors.
     `medium'         -- Medium colors.
     `dark'           -- Dark colors.")


(defvar font-lock-studio-color-list
  (cond ((eq font-lock-studio-color-scheme 'dark-to-light)
         (append font-lock-studio-color-list-dark
                 font-lock-studio-color-list-medium
                 font-lock-studio-color-list-light))
        ((eq font-lock-studio-color-scheme 'light-to-dark)
         (append font-lock-studio-color-list-light
                 font-lock-studio-color-list-medium
                 font-lock-studio-color-list-dark))
        ((eq font-lock-studio-color-scheme 'light)
         font-lock-studio-color-list-light)
        ((eq font-lock-studio-color-scheme 'medium)
         font-lock-studio-color-list-medium)
        ((eq font-lock-studio-color-scheme 'dark)
         font-lock-studio-color-list-dark)
        (t
         (error "Unexpected color scheme")))
  "*List of colors used to visualize matches in control and source buffers.")


(defvar font-lock-studio-anchored-search-region-face 'region
  "*Face used to visualize the anchored search region.

Normally, the region is between the point and the end of the
line. However, if the pre-match form returns a position (greater
than the point), this is used as the end of the region.")

;; Note: This is the value of the *variable* `font-lock-warning-face',
;; not the actual face, as this respects user-configuration.
(defvar font-lock-studio-breakpoint-face font-lock-warning-face
  "Face used to visualize breakpoints in the interface buffer.

This can be a symbol representing the actual face or a face or a
property list suitable for the `face' special property.")


(defvar font-lock-studio-auto-explain t
  "*When non-nil, a human-readable explanation is echoed after each command.

The explanation is only echoed if no other message is present.

See also `font-lock-studio-toggle-auto-explain'.")


(defvar font-lock-studio-major-mode-alias
  '((c-mode cpp-mode objc-mode))
  "*List of major modes considered equal.

When setting a breakpoint in a buffer, the breakpoint will also
be set for buffers considered aliases, provided they have an
identical font-lock keyword.

Each element is a list of major modes. The first element in the
list is used as key in `font-lock-studio-major-mode-breakpoints-alist'.")


(defvar font-lock-studio-show-compiled-code nil
  "*When nil, compiled code is not shown in Font Lock Studio.

See also `font-lock-studio-toggle-show-compiled-code'.")


(defvar font-lock-studio-show-public-state t
  "*When non-nil, show public state variables in Font Lock Studio.

See also `font-lock-studio-toggle-show-public-state'")


(defvar font-lock-studio-show-internal-state nil
  "*When non-nil, show internal state variables in Font Lock Studio.

See also `font-lock-studio-toggle-show-internal-state'")


;; --------------------
;; Internal variables
;;

;; ----------
;; Persistent variables
;;

;; The following represent the current state in the fontification
;; state machine.

;; Implementation note: Since keywords can be modified between
;; sessions, the keyword number can't be used here. Instead, the full
;; keyword is saved.
(defvar font-lock-studio-major-mode-breakpoints-alist nil
  "Alist from major mode to list of breakpoints.

Each breakpoint is on the form:

    (FULLKWRD COUNT)
    (FULLKWRD COUNT HIGHLIGHT)
    (FULLKWRD COUNT HIGHLIGHT ANCHOR-STATE)

Above, FULLKWRD is the full keyword (compared using `equal'),
COUNT is the N:th occurrence of the keyword (typically 1),
HIGHLIGHT is a number, and ANCHOR-STATE a number or one of
`:pre', `:matcher', or `:post'.")


;; ----------
;; Fontification engine
;;

(defvar font-lock-studio-buffer nil
  "The source buffer Font Lock Studio is associated with.")


(defvar font-lock-studio-region nil
  "The region, as a pair of markers, that Font Lock Studio was applied to.")


(defvar font-lock-studio-keywords nil
  "Normalized Font-Lock keywords of the source buffer.")


(defvar font-lock-studio-case-fold-search nil
  "Non-nil means search is case-insensitive.

This corresponds to `font-lock--case-fold-search' of the srouce buffer.")


(defvar font-lock-studio-multiline nil
  "Non-nil means support multiline keywords.

This corresponds to `font-lock-multiline' of the source buffer.")


;; TODO: Replace :done with nil?
(defvar font-lock-studio-keyword-number nil
  "The keyword number currently active, or :done.")


(defvar font-lock-studio-highlight-number nil
  "The highlight number in the current keyword, or nil.")


(defvar font-lock-studio-anchored-state nil
  "Where we are in a anchored match.


It can take on the following values:

  nil       -- Not at anchored rule, or before stepping into one.
  :pre      -- Before the pre-match form should be evaluated.
  :matcher  -- Before searching for a match
  NUMBER    -- the next highlight number to fontify.
  :post     -- After matcher failed, but before the post-match-form.")


(defvar font-lock-studio-fontify-breakpoints '()
  "Breakpoints in the current Font Lock Studio session.

Elements on one of the forms:

    (KWRD)
    (KWRD HIGHLIGHT)
    (KWRD HIGHLIGHT ANCHOR-STATE)

Above, KWRD and HIGHLIGHT are numbers and ANCHOR-STATE a number or
one of `:pre', `:matcher', or `:post'.")


(defvar font-lock-studio-point nil
  "Current search point in the source buffer.")


(defvar font-lock-studio-anchored-limit nil
  "The search limit of the current anchored rule.

This is typically the end of the current line, but can be
overridden by the pre-match form.")


(defvar font-lock-studio-keyword-match-data nil
  "Currently active match data.")


(defvar font-lock-studio-keyword-match-data-saved nil
  "The match data of the keyword, saved during an anchored highlight rule.")


(defvar font-lock-studio-original-font-lock-mode nil
  "Non-nil if `font-lock-mode' should be restored in the source buffer.")


(defvar font-lock-studio-edebug-active nil
  "Non-nil when Edebug should debug expressions in the interface buffer.")


(defvar font-lock-studio-edebug-expression-point nil
  "Point in the interface buffer where a debuggable form is located.

When Edebug is used, this form is used instead of the actual form
in the font-lock keywords. The effect is that Edebug can be used
directly in the interface buffer.")


;; ----------
;; Interface buffer
;;

(defvar font-lock-studio-window-configuration nil
  "The window configuration at the time Font-Lock studio was stated.")


(defvar font-lock-studio-overlays '()
  "List of active overlays in the source buffer.")


;; ------------------------------------------------------------


;;;###autoload
(defun font-lock-studio (&optional arg)
  "Interactively debug the font-lock keywords of the current buffer.

With \\[universal-argument] prefix, create a new, unique, interface buffer."
  (interactive "P")
  (font-lock-studio-region (point-min) (point-max) arg))


;;;###autoload
(defun font-lock-studio-region (beg end &optional arg)
  "Interactively debug the font-lock keywords in the region.

With \\[universal-argument] prefix, create a new, unique, interface buffer."
  (interactive "rP")
  (let ((name "*Font Lock Studio*"))
    (if arg
        (setq name (generate-new-buffer-name name)))
    (let ((interface-buffer (get-buffer-create name))
          (orig-buffer (current-buffer)))
      ;; Exit existing session.
      (with-current-buffer interface-buffer
        (font-lock-studio-finish))
      ;; Start new session.
      (font-lock-set-defaults)
      (let ((keywords font-lock-keywords))
        (with-current-buffer interface-buffer
          (font-lock-studio-mode)
          (set (make-local-variable 'font-lock-studio-window-configuration)
               (current-window-configuration))
          (make-local-variable 'font-lock-studio-overlays)
          (make-local-variable 'overlay-arrow-position)
          (font-lock-studio-fontify-start orig-buffer beg end)
          (font-lock-studio-fontify-restart)
          (select-window (display-buffer interface-buffer))
          (font-lock-studio-render)
          (font-lock-studio-show-source))))))


(defun font-lock-studio-finish ()
  "Restore the source buffer to it's original state.

Used when restarting and when the interface buffer is killed."
  (when (and font-lock-studio-buffer
             (buffer-live-p font-lock-studio-buffer))
    (font-lock-studio-remove-source-overlays)
    (with-current-buffer font-lock-studio-buffer
      (when overlay-arrow-position
        (move-marker overlay-arrow-position nil)
        (setq overlay-arrow-position nil)))
    (font-lock-studio-fontify-done)))


(eval-when-compile
  ;; Same as used by font-lock.el
  ;; We use this to preserve or protect things when modifying text properties.
  (defmacro font-lock-studio-save-buffer-state (&rest body)
    "Eval BODY, silencing modifications and inhibiting hooks."
    (declare (indent 0) (debug t))
    `(let ((inhibit-point-motion-hooks t))
       (with-silent-modifications
         ,@body))))


;; ------------------------------------------------------------
;; The interface buffer.
;;


;; --------------------
;; The major mode.
;;

(define-derived-mode font-lock-studio-mode special-mode "Font-Lock-Studio"
  "Major mode for the Font Lock Studio interface buffer.
\\{font-lock-studio-mode-map}"
  (add-hook 'kill-buffer-hook 'font-lock-studio-finish t t))


;; --------------------
;; Keymap and menu.
;;

(let ((map font-lock-studio-mode-map))
  (define-key map " " 'font-lock-studio-step-into)

  (define-key map "E" 'font-lock-studio-step-into-and-debug)
  (define-key map "I" 'font-lock-studio-instrument-matcher)
  (define-key map "M" 'font-lock-studio-show-match-data)

  (define-key map "l" 'font-lock-studio-update-interface-buffer)
  (define-key map "e" 'font-lock-studio-eval-in-source-buffer)

  (define-key map "m" 'font-lock-studio-step-keyword-match)
  (define-key map "n" 'font-lock-studio-next-keyword)
  (define-key map "o" 'font-lock-studio-step-out)
  (define-key map "q" 'font-lock-studio-quit)
  (define-key map "s" 'font-lock-studio-step-over)
  (define-key map "w" 'font-lock-studio-display-source)
  (define-key map "x" 'font-lock-studio-explain-state-at-point)
  (define-key map "k" 'font-lock-studio-goto-keyword-at-point)
  (define-key map "a" 'font-lock-studio-restart)
  (define-key map "g" 'font-lock-studio-run)

  ;; Skip commands.
  (define-key map "in" 'font-lock-studio-skip-to-next-keyword)
  (define-key map "io" 'font-lock-studio-skip-out)
  (define-key map "is" 'font-lock-studio-skip-over)

  ;; Breakpoints
  (define-key map "b" 'font-lock-studio-set-breakpoint)
  (define-key map "u" 'font-lock-studio-unset-breakpoint)

  ;; Toggle commands.
  (define-key map "ti" 'font-lock-studio-toggle-show-internal-state)
  (define-key map "tp" 'font-lock-studio-toggle-show-public-state)

  (define-key map "tc" 'font-lock-studio-toggle-show-compiled-code)

  (define-key map "tx" 'font-lock-studio-toggle-auto-explain)

  (define-key map "te" 'font-lock-studio-toggle-debug-on-error)
  (define-key map "tq" 'font-lock-studio-toggle-debug-on-quit)
  )


(defvar font-lock-studio-mode-menus
  '("Font Lock Studio"
    ["Step Into"                   font-lock-studio-step-into]
    ["Step Over"                   font-lock-studio-step-over]
    ["Step Out"                    font-lock-studio-step-out]
    ["Next Keyword"                font-lock-studio-next-keyword]
    ["Step Keyword Match"          font-lock-studio-step-keyword-match]
    ["Run"                         font-lock-studio-run]
    ["Restart"                     font-lock-studio-restart]
    "----"
    ["Eval in Source"              font-lock-studio-eval-in-source-buffer]
    ["Step Into and Debug"         font-lock-studio-step-into-and-debug]
    ["Instrument Matcher"          font-lock-studio-instrument-matcher]
    "----"
    ["Skip to Next Keyword"        font-lock-studio-skip-to-next-keyword]
    ["Skip Out"                    font-lock-studio-skip-out]
    ["Skip Over"                   font-lock-studio-skip-over]
    "----"
    ["Set Breakpoint"              font-lock-studio-set-breakpoint]
    ["Unset Breakpoint"            font-lock-studio-unset-breakpoint]
    "----"
    ["Show Internal State"         font-lock-studio-toggle-show-internal-state
     :style toggle         :selected      font-lock-studio-show-internal-state]
    ["Show Public State"           font-lock-studio-toggle-show-public-state
     :style toggle         :selected      font-lock-studio-show-public-state]
    ["Show Compiled Code"          font-lock-studio-toggle-show-compiled-code
     :style toggle         :selected      font-lock-studio-show-compiled-code]
    ["Auto Explain"                font-lock-studio-toggle-auto-explain
     :style toggle         :selected      font-lock-studio-auto-explain]
    ["Debug on Error"              font-lock-studio-toggle-debug-on-error
     :style toggle         :selected                       debug-on-error]
    ["Debug on Quit"               font-lock-studio-toggle-debug-on-quit
     :style toggle         :selected                       debug-on-quit]
    "----"
    ["Explain State at Point"      font-lock-studio-explain-state-at-point]
    ["Display Source"              font-lock-studio-display-source]
    ["Show Match Data"             font-lock-studio-show-match-data]
    ["Update Interface Buffer"     font-lock-studio-update-interface-buffer]
    ["Quit"                        font-lock-studio-quit]
    ))


(easy-menu-define
  font-lock-studio-menu font-lock-studio-mode-map
  "Font Lock Studio menus" font-lock-studio-mode-menus)


;; --------------------
;; Renderer -- Fills the interface buffer with content.
;;


;; ----------
;; TAB prettyfier -- prints TAB characters as \t.

(defmacro font-lock-studio-with-clean-output-to-string (&rest body)
  "Eval BODY like `progn', collect, clean, and return output as string.

Tab characters are emitted as \\t. Binds `indent-tabs-mode' to
nil to ensure that indentation doesn't contain tab characters."
  `(let ((indent-tabs-mode nil))
     (replace-regexp-in-string
      "\t" "\\t"
      (with-output-to-string
        ,@body)
      t t)))


;; ----------
;; "Inserter" that reuse existing content.
;;
;; The `font-lock-studio-render' function is written so that it
;; appears as though it clears the buffer and inserts new content.
;; However, if it should neively do so, things like window starts
;; would no long work. Instead, this checks if the buffer already
;; happened to contain what is inserted, and if so, reuse the existing
;; text by simply copying text properties to it.
;;
;; Clearly, this is optimized for the case when the same content is
;; written to the buffer over and over again, which is the case here.

(defvar font-lock-studio-insert-accumulated ""
  "Accumulated inserted text, for asserting correctness.")


(defvar font-lock-studio-insert-debug-overlay nil)

;; Even though this package should work with old Emacs versions, the
;; intention is that modern names should be used. In this case,
;; however, the modern name is `cl-position' (from cl-lib) and the old
;; `position' (from cl). Unfortunately, there is no way to write the
;; code so that it works in both worlds, hence this function.

(defun font-lock-studio-position (item seq)
  "Find the first occurrence of ITEM in SEQ.
Return the index of the matching item, or nil if not found."
  (let ((count 0)
        (len (length seq))
        (res nil))
    (while (< count len)
      (if (eq item (aref seq count))
          (progn
            (setq res count)
            (setq len 0))               ; Break the loop
        (setq count (+ count 1))))
    res))

(defun font-lock-studio-insert (s)
  "Insert (or replace) text at point like `insert'.

If there is text at point, reusing it rather than inserting new
to ensure that visible windows aren't redisplayed."
  (setq font-lock-studio-insert-accumulated
        (concat font-lock-studio-insert-accumulated s))
  (while (not (equal s ""))
    (let* ((end-pos (font-lock-studio-position ?\n s))
           (line (if end-pos
                     (substring s 0 (+ end-pos 1))
                   s))
           (len (length line))
           (buf-end-pos (+ (point) len)))
      (if end-pos
          (setq s (substring s (+ end-pos 1)))
        (setq s ""))
      (if (and (<= buf-end-pos
                   (point-max))
               (equal line (buffer-substring (point) buf-end-pos)))
          ;; Exact match, copy text properties.
          (let ((prop-change-pos 0)
                next-prop-change-pos)
            (while (not (eq prop-change-pos len))
              (setq next-prop-change-pos
                    (next-property-change prop-change-pos line))
              (unless next-prop-change-pos
                (setq next-prop-change-pos len))
              (set-text-properties (+ (point) prop-change-pos)
                                   (+ (point) next-prop-change-pos)
                                   (text-properties-at prop-change-pos line))
              (setq prop-change-pos next-prop-change-pos))
            (if font-lock-studio-insert-debug-overlay
                (let ((overlay (make-overlay (point) buf-end-pos)))
                  (overlay-put overlay
                               'face
                               'region)))
            (goto-char buf-end-pos))
        ;; Not exact match, insert line by line.
        (if end-pos
            (delete-region (point) (save-excursion
                                     (forward-line)
                                     (point))))
        (insert line)))))


(defun font-lock-studio-render ()
  "Draw the Font Lock Studio interface buffer.

In the source buffer, match data is visalized and the anchored
rule search limit is shown."
  (font-lock-studio-remove-source-overlays)
  (let ((buffer-read-only nil))
    ;; ------------------------------
    ;; The code is written so that it looks like it fills an empty
    ;; buffer with content. However, the old content is kept in the
    ;; buffer and replaced as text is inserted. Without this, windows
    ;; displaying the interface buffer would lose their window start
    ;; position, among other things.
    (goto-char (point-min))
    (setq font-lock-studio-insert-accumulated "")
    (set-text-properties (point-min) (point-max) '())
    (dolist (o (overlays-in (point-min) (point-max)))
      (delete-overlay o))
    ;; ------------------------------
    (setq font-lock-studio-edebug-expression-point nil)
    ;; ------------------------------
    ;; Fill the buffer with new content.
    (font-lock-studio-insert "    ========================\n")
    (font-lock-studio-insert "    === Font Lock Studio ===\n")
    (font-lock-studio-insert "    ========================\n")
    ;; --------------------
    ;; Keywords
    (let ((keyword-number 0)
          (p nil))                      ; The final point location
      (if (and (numberp font-lock-studio-keyword-number)
               (numberp font-lock-studio-highlight-number))
          (font-lock-studio-visualize-match-data))
      (dolist (kw font-lock-studio-keywords)
        ;; --------------------
        ;; One keyword
        (font-lock-studio-insert
         "--------------------------------------------------\n")
        ;; ----------
        ;; Matcher (regexp or function)
        (let ((s (point)))
          (if (eq keyword-number font-lock-studio-keyword-number)
              (setq p (point)))
          (font-lock-studio-render-matcher
           (car kw)
           ;; Visualize.
           (and (eq keyword-number font-lock-studio-keyword-number)
                font-lock-studio-highlight-number
                ;; Note: Match data of keyword matcher is active when
                ;; anchored matcher, pre-, and post-match forms are
                ;; evaluated.
                (not (numberp font-lock-studio-anchored-state)))
           ;; Set expression point.
           (and (eq keyword-number font-lock-studio-keyword-number)
                (not font-lock-studio-highlight-number)))
          (font-lock-studio-render-state-information
           s (point) keyword-number)
          (font-lock-studio-insert "\n"))
        ;; ----------
        ;; Highlights
        (let ((highlight-number 0)
              is-current-base-highlight)
          (dolist (highlight (cdr kw))
            (setq is-current-base-highlight
                  (and
                   (eq keyword-number font-lock-studio-keyword-number)
                   (eq highlight-number font-lock-studio-highlight-number)))
            (if (numberp (car highlight))
                ;; ----------
                ;; Normal highlight rule.
                (let ((s (point)))
                  (when is-current-base-highlight
                    (setq p (point)))
                  (font-lock-studio-insert "  ")
                  (font-lock-studio-render-highlight
                   highlight
                   (and
                    (eq keyword-number font-lock-studio-keyword-number)
                    (numberp font-lock-studio-highlight-number)
                    (not (numberp font-lock-studio-anchored-state)))
                   is-current-base-highlight
                   "  ")
                  (font-lock-studio-render-state-information
                   s (point) keyword-number highlight-number)
                  (font-lock-studio-insert "\n"))
              ;; ----------
              ;; Anchored highlight rule.
              (if (and is-current-base-highlight
                       (null font-lock-studio-anchored-state))
                  (setq p (point)))
              (let ((s (point)))
                (font-lock-studio-insert "  (")
                (font-lock-studio-render-state-information
                 s (point) keyword-number highlight-number))
              (let ((anchored-part-list '(:matcher :pre :post 0))
                    anchored-part)
                (dolist (part highlight)
                  (let ((is-current-anchored-part nil)
                        (s (point)))
                    (if anchored-part-list
                        (setq anchored-part (pop anchored-part-list))
                      (setq anchored-part (+ 1 anchored-part)))
                    (unless (eq anchored-part :matcher)
                      (font-lock-studio-insert "\n"))
                    (when (and is-current-base-highlight
                               (eq anchored-part
                                   font-lock-studio-anchored-state))
                      (setq is-current-anchored-part t)
                      (unless (memq anchored-part '(:pre :post))
                        (when (< font-lock-studio-point
                                 font-lock-studio-anchored-limit)
                          (let ((overlay (make-overlay
                                          font-lock-studio-point
                                          font-lock-studio-anchored-limit
                                          font-lock-studio-buffer)))
                            (overlay-put
                             overlay
                             'face
                             font-lock-studio-anchored-search-region-face)
                            (push overlay font-lock-studio-overlays)))))
                    (unless (eq anchored-part :matcher)
                      (font-lock-studio-insert "   "))
                    (when is-current-anchored-part
                      (setq p (point)))
                    (let ((highlight
                           (and is-current-base-highlight
                                (numberp
                                 font-lock-studio-anchored-state))))
                      (cond ((eq anchored-part :matcher)
                             (font-lock-studio-render-matcher
                              part highlight is-current-anchored-part "   "))
                            ((memq anchored-part '(:pre :post))
                             (if is-current-anchored-part
                                 (setq font-lock-studio-edebug-expression-point
                                       (point)))
                             (font-lock-studio-insert-expr part "   " t))
                            ((numberp anchored-part)
                             (font-lock-studio-render-highlight
                              part highlight is-current-anchored-part "   "))
                            (t
                             (error "Unexpected anchored part"))))
                    (font-lock-studio-render-state-information
                     s (point)
                     keyword-number highlight-number anchored-part))))
              (let ((s (point)))
                (font-lock-studio-insert ")\n")
                (font-lock-studio-render-state-information
                 s (point) keyword-number highlight-number)))
            (setq highlight-number (+ 1 highlight-number))))
        (setq keyword-number (+ 1 keyword-number)))
      ;; --------------------
      ;; Point position at end of keywords.
      (unless p
        (setq p (point)))
      ;; --------------------
      ;; Print public state
      (when font-lock-studio-show-public-state
        (font-lock-studio-insert
         "==================================================\n")
        (font-lock-studio-insert "Public state:\n")
        (font-lock-studio-insert-bool "  Debug on error     : "
                                      debug-on-error)
        (font-lock-studio-insert-bool "  Debug on quit      : "
                                      debug-on-quit)
        (font-lock-studio-insert-bool "  Explain rules      : "
                                      font-lock-studio-auto-explain)
        (font-lock-studio-insert-bool "  Show compiled code : "
                                      font-lock-studio-show-compiled-code))
      ;; Print internal state
      (when font-lock-studio-show-internal-state
        (font-lock-studio-insert
         "==================================================\n")
        (font-lock-studio-insert "Internal state:\n")
        (font-lock-studio-insert (format "  Keyword number         : %s\n"
                                         font-lock-studio-keyword-number))
        (font-lock-studio-insert (format "  Highlight number       : %s\n"
                                         font-lock-studio-highlight-number))
        (font-lock-studio-insert (format "  Anchored state         : %s\n"
                                         font-lock-studio-anchored-state))
        (font-lock-studio-insert (format "  Anchored limit         : %s\n"
                                         font-lock-studio-anchored-limit))
        (font-lock-studio-insert (format "  Point                  : %s\n"
                                         (if (markerp font-lock-studio-point)
                                             (marker-position
                                              font-lock-studio-point)
                                           font-lock-studio-point)))
        (font-lock-studio-insert (format "  Edebug expression point: %s\n"
                        font-lock-studio-edebug-expression-point))
        (font-lock-studio-insert "  Match data             :\n")
        (font-lock-studio-insert (font-lock-studio-format-match-data
                 font-lock-studio-keyword-match-data))
        (font-lock-studio-insert "\n")
        (font-lock-studio-insert "  Match data (saved)     :\n")
        (font-lock-studio-insert (font-lock-studio-format-match-data
                 font-lock-studio-keyword-match-data-saved))
        (font-lock-studio-insert "\n")
        (font-lock-studio-insert "  Breakpoints:\n")
        (font-lock-studio-insert
         (pp-to-string font-lock-studio-fontify-breakpoints))
        (font-lock-studio-insert "\n")
        (font-lock-studio-insert "  All breakpoints:\n")
        (font-lock-studio-insert
         (pp-to-string font-lock-studio-major-mode-breakpoints-alist))
        (font-lock-studio-insert "\n"))
      ;; --------------------
      ;; Remove any remaining text of the original buffer.
      (delete-region (point) (point-max))
      (assert (equal font-lock-studio-insert-accumulated
                     (buffer-substring (point-min) (point-max))))
      ;; --------------------
      ;; Move point and draw the fringe arrow in interface buffer.
      (goto-char p)
      (if (not (eq font-lock-studio-keyword-number :done))
          (if overlay-arrow-position
              (move-marker overlay-arrow-position (line-beginning-position))
            (set (make-local-variable 'overlay-arrow-position)
                 (copy-marker (line-beginning-position))))
        (when overlay-arrow-position
          (move-marker overlay-arrow-position nil)
          (setq overlay-arrow-position nil)))
      ;; --------------------
      ;; Echo a description of the current rule.
      (if (and font-lock-studio-auto-explain
               (not (let ((msg (current-message)))
                      (and msg
                           (not (equal msg "Garbage collecting...done"))))))
          (let ((msg (font-lock-studio-explain-state-at-point)))
            (if msg
                (message msg))))))
  (set-buffer-modified-p nil))


(defun font-lock-studio-render-highlight (highlight
                                          visualize
                                          save-expression-point
                                          prefix)
  "Insert HIGHLIGHT into interface buffer.

If VISUALIZE is non-nil, and there is a corresponding match,
color the inserted text accordingly.

See `font-lock-studio-insert-highlight' for SAVE-EXPRESSION-POINT
and `font-lock-studio-insert-expr' for PREFIX."
  (let ((start (point)))
    (font-lock-studio-insert-highlight
     highlight prefix t save-expression-point)
    (if (and visualize
             (nth (* 2 (car highlight)) font-lock-studio-keyword-match-data))
        (let ((overlay (make-overlay
                        start
                        (point))))
          (overlay-put
           overlay
           'face
           (list :background
                 (nth (mod (car highlight)
                           (length font-lock-studio-color-list))
                      font-lock-studio-color-list)))))))


(defun font-lock-studio-insert-highlight (highlight prefix &optional in-line
                                                    save-expression-point)
  "Insert HIGHLIGHT into buffer.

See `font-lock-studio-insert-expr' for PREFIX and IN-LINE.

If SAVE-EXPRESSION-POINT is non-nil, set
`font-lock-studio-edebug-expression-point' to the point where the
facename form is."
  (let ((beg (point)))
    (font-lock-studio-insert-expr highlight prefix in-line)
    (if save-expression-point
        (save-excursion
          (goto-char beg)
          (forward-comment 1)         ; Skip whitespace
          (forward-char)              ; Skip opening parenthesis
          (forward-sexp)              ; Skip highlight number
          (forward-comment 1)         ; Skip whitespace
          (setq font-lock-studio-edebug-expression-point (point))))))


(defun font-lock-studio-render-matcher (matcher
                                        visualize
                                        save-expression-point
                                        &optional prefix)
  "Insert MATCHER into interface buffer.

If VISUALIZE is non-nil, and there is a corresponding match, color
the inserted text.

If SAVE-EXPRESSION-POINT is non-nil, store the point so the
expression can be retrieved when debugging with Edebug.

See `font-lock-studio-insert-expr' for PREFIX."
  (unless prefix
    (setq prefix ""))
  (cond ((and (stringp matcher)
              visualize)
         (font-lock-studio-insert (font-lock-studio-visualize-regexp
                                   matcher
                                   font-lock-studio-keyword-match-data)))
        ((and (byte-code-function-p matcher)
              (not font-lock-studio-show-compiled-code))
         (font-lock-studio-insert ";; Compiled code (hidden)"))
        ((stringp matcher)
         (font-lock-studio-insert
          (font-lock-studio-with-clean-output-to-string
           (prin1 matcher))))
        (t
         (if save-expression-point
             (setq font-lock-studio-edebug-expression-point (point)))
         (font-lock-studio-insert-expr matcher prefix t))))


(defun font-lock-studio-insert-expr (expr prefix &optional in-line)
  "Pretty-print EXPR and insert it into buffer.

For each line, insert PREFIX before each line. If IN-LINE is
non-nil, don't do this on the first line."
  (let ((indented-expr
         (replace-regexp-in-string
          "\n\\(.\\)" (concat "\n" prefix "\\1")
          (font-lock-studio-with-clean-output-to-string
           (pp expr)))))
    ;; Strip trailing newline
    (if (eq (elt indented-expr (- (length indented-expr) 1)) ?\n)
        (setq indented-expr (substring indented-expr 0 -1)))
    (unless in-line
      (font-lock-studio-insert prefix))
    (font-lock-studio-insert indented-expr)))


(defun font-lock-studio-render-state-information (beg
                                                  end
                                                  keyword
                                                  &optional
                                                  highlight
                                                  anchored)
  "Add state information to text between BEG and END in the interface buffer.

KEYWORD, HIGHLIGHT, and ANCHORED corresponds to
`font-lock-studio-keyword-number',
`font-lock-studio-highlight-number', and
`font-lock-studio-anchored-state', respectively.

State information is stored using the text property
`font-lock-studio-state'.

In addition, if there is a breakpoint associated with the state,
color the text according to `font-lock-studio-breakpoint-face'."
  (let ((state '()))
    (if anchored
        (push anchored state))
    (if highlight
        (push highlight state))
    (push keyword state)
    (put-text-property beg end 'font-lock-studio-state state)
    (if (member state font-lock-studio-fontify-breakpoints)
        ;; Note: If plain `put-text-property' is used, breakpoint
        ;; information will overwrite regexp match visualizations.
        (font-lock-append-text-property
         beg end 'face font-lock-studio-breakpoint-face))))


(defun font-lock-studio-insert-bool (str value)
  "Helper function for printing the boolean values.

STR is a description of the boolean flag and VALUE is the value."
  (font-lock-studio-insert str)
  (font-lock-studio-insert (if value "YES" "NO"))
  (font-lock-studio-insert "\n"))


(defun font-lock-studio-remove-source-overlays ()
  "Remove all Font-Lock studio related overlays in the source buffer."
  (dolist (overlay font-lock-studio-overlays)
    (delete-overlay overlay))
  (setq font-lock-studio-overlays '()))


(defun font-lock-studio-show-source ()
  "Show source with point and overlay arrow at current search position."
  (if (eq font-lock-studio-keyword-number :done)
      ;; ----------
      ;; No more rules, clear the overlay arrow.
      (with-current-buffer font-lock-studio-buffer
        (when overlay-arrow-position
          (move-marker overlay-arrow-position nil)
          (setq overlay-arrow-position nil)))
    ;; ----------
    (let ((source-pos font-lock-studio-point)
          (win (get-buffer-window font-lock-studio-buffer)))
      ;; Show source buffer.
      (if (and win
               (with-current-buffer font-lock-studio-buffer
                 (and (boundp 'follow-mode)
                      follow-mode)))
          ;; Note: follow-mode is typically only active for buffer in
          ;; the selected window. There is no good way to ensure that
          ;; other buffers becomes aligned. This is a somewhat clumsy
          ;; way to accomplish this -- may we wish for a more polished
          ;; interface in the future?
          (let ((owin (selected-window)))
            (select-window win)
            (goto-char source-pos)
            (follow-post-command-hook)
            ;; Here, the windows are aligned, and the selected
            ;; window contains the location `source-pos'.
            ;; However, the window point is (unfortunately)
            ;; not set to it.
            (set-window-point (selected-window) source-pos)
            (select-window owin))
        (let ((win (display-buffer font-lock-studio-buffer)))
          (set-window-point win source-pos)))
      ;; Show the overlay arrow and move point.
      (with-current-buffer font-lock-studio-buffer
        (goto-char source-pos)
        (let ((beg (line-beginning-position)))
          (if overlay-arrow-position
              (move-marker overlay-arrow-position beg)
            (set (make-local-variable 'overlay-arrow-position)
                 (copy-marker beg))))))))


;; --------------------
;; Explainer
;;

(defun font-lock-studio-explain-state (state)
  "A natural language explanation of STATE.

The state is on the form (KEYWORD [HIGHLIGHT [ANCHORED]]).

Return a string suitable to be applied to `message', or nil."
  (let* ((keyword-number   (nth 0 state))
         (highlight-number (nth 1 state))
         (anchored-state   (nth 2 state))
         (kw (nth keyword-number font-lock-studio-keywords)))
    (if (not highlight-number)
        (concat "Keyword with "
                (font-lock-studio-explain-matcher
                 (car kw))
                " matcher")
      (let* ((highlight-list (cdr kw))
             (highlight (nth highlight-number highlight-list)))
        (if (numberp (car highlight))
            (concat
             "Highlight: "
             (font-lock-studio-explain-highlight highlight))
          (cond ((eq anchored-state :pre)
                 "Pre-match form of anchored highlight")
                ((eq anchored-state :post)
                 "Post-match form of anchored highlight")
                ((eq anchored-state :matcher)
                 (concat "Anchored highlight with "
                         (font-lock-studio-explain-matcher (car highlight))
                         " matcher"))
                ((numberp anchored-state)
                 (concat "Highlight inside anchored highlight, "
                         (font-lock-studio-explain-highlight
                          (nth (+ anchored-state 3)
                               highlight))))
                (t
                 "Anchored highlight")))))))


(defun font-lock-studio-explain-highlight (highlight)
  "An explanation of HIGHLIGHT.

Return a string suitable to be applied to `message'."
  (mapconcat 'identity
             (cons (font-lock-studio-explain-highlight-highlight highlight)
                   (font-lock-studio-explain-highlight-options highlight))
             " "))


(defun font-lock-studio-explain-highlight-highlight (highlight)
  "An explanation of the HIGHLIGHT field of HIGHLIGHT.
Return a list of sentences.

See `font-lock-keywords' for details."
  (assert (numberp (car highlight)))
  (with-current-buffer font-lock-studio-buffer
    (let ((face (nth 1 highlight)))
      (cond ((symbolp face)
             (if (boundp face)
                 (format "Face `%s' (via variable `%s')."
                         (symbol-value face)
                         face)
               (format
                "\
Face should come from variable `%s', which is unbound (missing quote?)."
                face)))
            ((and (consp face)
                  (eq (car face) 'quote)
                  (consp (cdr face))
                  (eq (cdr (cdr face)) nil)
                  (symbolp (car (cdr face))))
             (format "`%s' face." (car (cdr face))))
            (t
             "Face is decided by expression.")))))


(defun font-lock-studio-explain-highlight-options (highlight)
  "Explain the OVERRIDE and LAXMATCH flags of HIGHLIGHT.
Return a list of sentences.

See `font-lock-keywords' for details."
  (let ((override (nth 2 highlight))
        (laxmatch (nth 3 highlight))
        (res '()))
    (cond ((eq override t)
           (push "Existing fontification is overwritten." res))
          ((eq override 'keep)
           (push "Parts not already fontified are highlighted." res))
          ((eq override 'prepend)
           (push "Fontification is merged, new takes precedence." res))
          ((eq override 'append)
           (push "Fontification is merged, existing takes precedence." res))
          ((eq override nil)
           ;; Print nothing.
           )
          (t
           (push (format "Illegal OVERRIDE flag `%s'." override) res)))
    (if laxmatch
        (push "No error if match not found." res))
    (reverse res)))


(defun font-lock-studio-explain-matcher (matcher)
  "Categorize MATCHER."
  (cond ((stringp matcher)
         "regexp")
        ((symbolp matcher)
         "function name")
        ((byte-code-function-p matcher)
         "compiled code")
        ((functionp matcher)
         "code-based")
        (t
         "unknown")))


;; --------------------
;; Visualization of match-data
;;

(defun font-lock-studio-flatten-match-data (md0)
  "Split match data MD0 into a non-overlapping sequence of ranges.
Return list of (GROUP BEG END)."
  ;; Figure out what parts should be visualized. It is assumed that
  ;; later ranged are placed in top of earlier, if they overlap.
  ;;
  ;; (Note: Code does not assume that the ranges are properly nested,
  ;; as the match data can be synthesized by search functions.)
  (let (;; List of (COUNT BEG END), where no BEG END ranges overlap.
        (ranges '())
        (md md0)
        (count 0))
    (while md
      (let ((beg (pop md))
            (end (pop md)))
        (when (and beg end)
          (let ((new-ranges '()))
            (dolist (r ranges)
              (let ((old-beg (nth 1 r))
                    (old-end (nth 2 r)))
                (cond
                 ;; No overlap
                 ((or (<= old-end beg)
                      (>= old-beg end))
                  (push r new-ranges))
                 ;; Full overlap, drop the old range.
                 ((and (<= beg old-beg)
                       (>= end old-end))
                  ;; Do nothing...
                  )
                 ;; Old range is split in the middle.
                 ;;
                 ;; |------------| old
                 ;;    |------|    new
                 ((and (< old-beg beg)
                       (< end old-end))
                  (push (list (nth 0 r) old-beg beg)     new-ranges)
                  (push (list (nth 0 r) end     old-end) new-ranges))
                 ;; Beginning of old range is overlapped.
                 ;;
                 ;;     |------| old
                 ;; |------|     new
                 ((and (<= beg old-beg)
                       (< old-beg end))
                  (push (list (nth 0 r) end old-end) new-ranges))
                 ;; End of old range is overlapped.
                 ;;
                 ;; |------|     old
                 ;;     |------| new
                 ((and (< beg old-end)
                       (<= old-end end))
                  (push (list (nth 0 r) old-beg beg) new-ranges))
                 (t
                  (error "This should not happen: %s" md0)))))
            (push (list count beg end) new-ranges)
            (setq ranges (nreverse new-ranges)))))
      (setq count (+ 1 count)))
    ranges))


(defun font-lock-studio-visualize-match-data ()
  "Visualize match data in source buffer."
  (let ((ranges (font-lock-studio-flatten-match-data
                 font-lock-studio-keyword-match-data)))
    (dolist (r ranges)
      (let ((group (nth 0 r))
            (beg   (nth 1 r))
            (end   (nth 2 r)))
        (when (and (or (not (markerp beg))
                       (eq (marker-buffer beg) font-lock-studio-buffer))
                   (or (not (markerp end))
                       (eq (marker-buffer end) font-lock-studio-buffer)))
          (let ((overlay (make-overlay
                          beg
                          end
                          font-lock-studio-buffer)))
            (overlay-put
             overlay
             'face
             (list :background
                   (nth (mod group
                             (length font-lock-studio-color-list))
                        font-lock-studio-color-list)))
            (push overlay font-lock-studio-overlays)))))))


(defun font-lock-studio-visualize-regexp (regexp md &optional all)
  "Return a fontified string of the printed representation of REGEXP.

A group is colored if there is a corresponding match in MD or of
ALL is non-nil. The group is colored according
`font-lock-studio-color-list'."
  ;; Wrapper around `font-lock-studio-visualize-regexp0', asserting
  ;; that the return value is sound.
  (let ((res (font-lock-studio-visualize-regexp0 regexp md all))
        (prx (font-lock-studio-with-clean-output-to-string
              (prin1 regexp))))
    ;; Note: `equal' ignored text properties.
    (assert (equal prx res))
    res))


(defun font-lock-studio-visualize-regexp0 (regexp md &optional all)
  "Return a fontified string of the printed representation of REGEXP.

A group is colored if there is a corresponding match in MD or of
ALL is non-nil. The group is colored according
`font-lock-studio-color-list'."
  (let ((groups (font-lock-studio-find-groups-in-regexp regexp))
        (group-number 0)
        (res ""))
    (let ((flat-list (font-lock-studio-flatten-match-data groups))
          (index 0))
      (setq flat-list (sort flat-list
                            (lambda (x y) (< (nth 1 x) (nth 1 y)))))
      (dolist (element flat-list)
        (let ((group (nth 0 element))
              (beg   (nth 1 element))
              (end   (nth 2 element)))
          (when (or all
                    (elt md (* 2 group)))
            (when (< index beg)
              (setq res (concat res
                                (substring
                                 (font-lock-studio-with-clean-output-to-string
                                  (prin1 (substring regexp index beg)))
                                 1 -1)))
              (setq index beg))
            (when (< beg end)
              (let ((s (substring
                        (font-lock-studio-with-clean-output-to-string
                         (prin1 (substring regexp beg end)))
                        1 -1)))
                (set-text-properties
                 0 (length s)
                 (list 'face
                       (list :background
                             (nth (mod group
                                       (length font-lock-studio-color-list))
                                  font-lock-studio-color-list)))
                 s)
                (setq res (concat res s))
                (setq index end))))))
      ;; Note: If the match data is correctly formed, i.e. when
      ;; element 0 corresponds to the full string, this isn't needed.
      (if (< index (length regexp))
          (setq res (concat res
                            (substring
                             (font-lock-studio-with-clean-output-to-string
                              (prin1 (substring regexp index)))
                             1 -1)))))
    (concat "\"" res "\"")))


;; --------------------
;; Regexp parser for finding groups
;;

(defvar font-lock-studio-find-groups-in-regexp--regexp nil)
(defvar font-lock-studio-find-groups-in-regexp--index nil)

(defun font-lock-studio-find-groups-in-regexp--peek-char (&optional extra)
  "Return character without consuming it, or nil if at the end.

If EXTRA nil, the next character is used. Otherwise the character
EXTRA positions after the next is used."
  (unless extra
    (setq extra 0))
  (let ((index (+ font-lock-studio-find-groups-in-regexp--index extra)))
    (if (< index (length font-lock-studio-find-groups-in-regexp--regexp))
        (elt font-lock-studio-find-groups-in-regexp--regexp index)
      nil)))


(defun font-lock-studio-find-groups-in-regexp--get-char (&optional error-hint)
  "Consume and return the next character.

The signal `invalid-regexp' is raised if there are no more
characters. ERROR-HINT is a printable object used to present the
user with a more informative error message."
  (if (equal font-lock-studio-find-groups-in-regexp--index
             (length font-lock-studio-find-groups-in-regexp--regexp))
      (signal 'invalid-regexp
              (if error-hint
                  (format "End of regexp reached while looking for %s"
                          error-hint)
                "End of regexp reached")))
  (prog1 (font-lock-studio-find-groups-in-regexp--peek-char)
    (setq font-lock-studio-find-groups-in-regexp--index
          (+ 1 font-lock-studio-find-groups-in-regexp--index))))


(defun font-lock-studio-find-groups-in-regexp--consume-if (char)
  "Consume the next character if it is CHAR."
  (if (eq (font-lock-studio-find-groups-in-regexp--peek-char) char)
      (font-lock-studio-find-groups-in-regexp--get-char)))


(defun font-lock-studio-find-groups-in-regexp--looking-at (regexp
                                                           &optional group)
  "If text in matched string match REGEXP, return end index.
If GROUP is non-nil, return end of that group instead."
  (if (string-match regexp
                    (substring font-lock-studio-find-groups-in-regexp--regexp
                               font-lock-studio-find-groups-in-regexp--index))
      (+ (match-end (or group 0))
         font-lock-studio-find-groups-in-regexp--index)
    nil))


(defun font-lock-studio-find-groups-in-regexp--consume-regexp (regexp)
  "Consume text matching REGEXP, if present at parse point.
Return non-nil if any text was consumed."
  (let ((idx (font-lock-studio-find-groups-in-regexp--looking-at regexp)))
    (if idx
        (setq font-lock-studio-find-groups-in-regexp--index idx))
    idx))


(defun font-lock-studio-find-groups-in-regexp--consume-character-class ()
  "Consume a character class, like [:alpha:], if present at parse point.
Return non-nil if any text was consumed."
  (font-lock-studio-find-groups-in-regexp--consume-regexp "^\\[:[a-z]+:\\]"))


(defun font-lock-studio-find-groups-in-regexp (re)
  "Find the groups in the regexp RE.

Return list on the same form as `match-data', but with positions
corresponding to the location of the groups in the regexp.

Signals an `invalid-regexp' error when applied to a broken regexp."
  (setq font-lock-studio-find-groups-in-regexp--index 0)
  (setq font-lock-studio-find-groups-in-regexp--regexp re)
  (let ((res (list (list 0 0 (length re)))) ; List of (group beg end):s
        (open-groups '())
        (group-number 1)
        char)
    (while (< font-lock-studio-find-groups-in-regexp--index (length re))
      (setq char (font-lock-studio-find-groups-in-regexp--get-char))
      (cond
       ;; ----------
       ;; Character classes
       ;;
       ((eq char ?\[ )
        (font-lock-studio-find-groups-in-regexp--consume-if ?^)
        (font-lock-studio-find-groups-in-regexp--consume-if ?\])
        (font-lock-studio-find-groups-in-regexp--consume-if ?-)
        (while
            (or
             (font-lock-studio-find-groups-in-regexp--consume-character-class)
             (not
              (eq (font-lock-studio-find-groups-in-regexp--get-char)
                  ?\])))))
       ;; ----------
       ;; Escaped character
       ;;
       ((eq char ?\\)
        (let ((next-char
               (font-lock-studio-find-groups-in-regexp--get-char)))
          (cond
           ;; ----------
           ;; Open group
           ((eq next-char ?\( )
            ;; Check for "\\(?:abc\\)" and "\\(?NNN:abc\\)"
            (let ((prefix-idx
                   (font-lock-studio-find-groups-in-regexp--looking-at
                    "^\\?\\([0-9]+\\)?:"))
                  (this-group-number group-number)
                  (shy nil))
              (when prefix-idx
                (if (match-beginning 1)
                    ;; Numbered group -- "\\(?NNN:abc\\)"
                    (setq
                     this-group-number
                     (string-to-number
                      (match-string
                       1
                       ;; Hack, to compensate for implementation in
                       ;; "-looking-at".
                       (substring
                        font-lock-studio-find-groups-in-regexp--regexp
                        font-lock-studio-find-groups-in-regexp--index))))
                  ;; Shy group -- "\\(?:abc\\)"
                  (setq shy t)))
              (push (list
                     (if shy
                         nil
                       this-group-number)
                     (- font-lock-studio-find-groups-in-regexp--index 2))
                    open-groups)
              (if prefix-idx
                  (setq font-lock-studio-find-groups-in-regexp--index
                        prefix-idx))
              (unless shy
                (cond ((> this-group-number group-number)
                       (setq group-number (+ this-group-number 1)))
                      ((< this-group-number group-number)
                       ;; Do nothing
                       )
                      (t
                       (setq group-number (+ 1 group-number)))))))
           ;; ----------
           ;; Close group
           ((eq next-char ?\) )
            (if (eq open-groups '())
                (signal 'invalid-regexp "Too many \\)"))
            (font-lock-studio-find-groups-in-regexp--consume-if ??)
            (font-lock-studio-find-groups-in-regexp--consume-if ?+)
            (font-lock-studio-find-groups-in-regexp--consume-if ?*)
            ;; Note: In addition to the correct matches, this will
            ;; also match "\{\}", we can live with this.
            (font-lock-studio-find-groups-in-regexp--consume-regexp
             "^\\\\{[0-9]*\\(,[0-9]*\\)?\\\\}")
            (let ((x (pop open-groups)))
              (when (car x)
                ;; Build up the list in reverse.
                (push
                 (list (nth 0 x)
                       (nth 1 x)
                       font-lock-studio-find-groups-in-regexp--index)
                 res))))
           ;; ----------
           ;; Any other escaped character.
           (t
            ;;
            ))))))
    (unless (eq open-groups '())
      (signal 'invalid-regexp "Missing \\)"))
    ;; Create a match-data compatible return value.
    (let ((real-res (make-list (* 2 group-number) nil)))
      (dolist (element (reverse res))
        (let ((num (nth 0 element))
              (beg (nth 1 element))
              (end (nth 2 element)))
          (setcar (nthcdr (* 2 num)       real-res) beg)
          (setcar (nthcdr (+ (* 2 num) 1) real-res) end)))
      real-res)))


;; ------------------------------------------------------------
;; Commands
;;

;; --------------------
;; Helper macros
;;

(defmacro font-lock-studio-command-wrapper (&rest body)
  "Evaluate BODY like `progn' and redraw the interface buffer.

Issue an error when not in an interface buffer."
  `(if (eq major-mode 'font-lock-studio-mode)
       (prog1
           (progn
             ,@body)
         (font-lock-studio-render))
     (user-error "Must be executed in a Font Lock Studio interface buffer")))


(defmacro font-lock-studio-command-wrapper-show-source (&rest body)
  "Evaluate BODY like `progn', redraw the interface buffer ans show source."
  `(progn (font-lock-studio-command-wrapper
           ,@body)
          (font-lock-studio-show-source)))


(defmacro font-lock-studio-command-wrapper-step (&rest body)
  "Evaluate BODY like `progn', redraw the interface buffer and show source.

This is intended to be used by step and run commands.

An error is issued if there are no more keywords to fontify.

The value of BODY is expected to be t for normal termination,
nil when all keywords were fontified, and `breakpoint' when a
breakpoint was reached. A suitable message is displayed."
  (let ((res-var (make-symbol "--res--")))
    `(if (eq font-lock-studio-keyword-number :done)
         (user-error "No more keywords")
       (font-lock-studio-command-wrapper-show-source
        (let ((,res-var (progn ,@body)))
          (cond ((eq ,res-var t))
                ((eq ,res-var nil)
                 (message "Reached the end"))
                ((eq ,res-var 'breakpoint)
                 (message "Stopped on breakpoint"))
                (t
                 (message "Unexpected return value")))
          ,res-var)))))


(defmacro font-lock-studio-command-wrapper-save-excursion (&rest body)
  "Evaluate BODY like `progn', redraw the interface, don't move the cursor."
  ;; Note: Can't use `save-excursion' as it uses markers, which does
  ;; not work as the interface buffer is erased and re-rendered.
  (let ((the-point-var (make-symbol "--the-point--")))
    `(let ((,the-point-var (point)))
       (prog1
           (font-lock-studio-command-wrapper ,@body)
         (goto-char ,the-point-var)))))


;; --------------------
;; Generic commands
;;

(defun font-lock-studio-update-interface-buffer ()
  "Redraw the Font Lock Studio buffer."
  (interactive)
  (font-lock-studio-command-wrapper-save-excursion))


(defun font-lock-studio-restart ()
  "Restart the Font Lock Studio session."
  (interactive)
  (font-lock-studio-command-wrapper-show-source
   (let ((beg (car font-lock-studio-region))
         (end (cdr font-lock-studio-region)))
     (with-current-buffer font-lock-studio-buffer
       (font-lock-unfontify-region beg end)))
   (font-lock-studio-fontify-restart)))


(defun font-lock-studio-quit (&optional arg)
  "Quit the Font Lock Studio session.

With \\[universal-argument] prefix, don't kill the interface buffer."
  (interactive "P")
  (set-window-configuration font-lock-studio-window-configuration)
  (if (not arg)
      (kill-buffer (current-buffer))
    ;; TODO: Really "show-source"?
    (font-lock-studio-command-wrapper-show-source
     (font-lock-studio-finish)
     (setq font-lock-studio-keyword-number :done)
     (setq font-lock-studio-highlight-number nil)
     (setq font-lock-studio-anchored-state nil))))


(defun font-lock-studio-display-source ()
  "Show the source buffer and the current search location within it."
  (interactive)
  (font-lock-studio-command-wrapper-show-source))


(defun font-lock-studio-goto-keyword-at-point ()
  "Set the keyword at the cursor to be active."
  (interactive)
  (font-lock-studio-command-wrapper-show-source
   (let ((state (get-text-property (point) 'font-lock-studio-state)))
     (if state
         (let ((keyword-number (nth 0 state)))
           (font-lock-studio-fontify-set-keyword keyword-number))
       (user-error "No keyword here.")))))


;; Note: Does not use `font-lock-studio-command-wrapper', since this
;; is called from inside `font-lock-studio-render'. Besides, it's safe
;; to call this from outside the interface buffer, in which case it
;; does nothing.
(defun font-lock-studio-explain-state-at-point ()
  "Echo an explanation of the font-lock keyword part under the cursor."
  (interactive)
  (let ((state (get-text-property (point) 'font-lock-studio-state)))
    (if state
        (message (font-lock-studio-explain-state state)))))


(defun font-lock-studio-explain-current-state ()
  "Echo an explanation of the current font-lock keyword part."
  (interactive)
  (let ((state (font-lock-studio-fontify-get-current-state)))
    (if state
        (message (font-lock-studio-explain-state state)))))


;; --------------------
;; Run and step commands and equivalent skip commands.
;;

;; ----------
;; Run
;;

(defun font-lock-studio-run (&optional nonstop)
  "Fontify all that is left.

With \\[universal-argument] prefix, don't stop on breakpoints."
  (interactive "P")
  (font-lock-studio-command-wrapper-step
   (font-lock-studio-fontify-step-while #'(lambda () t) nonstop)))


;; ----------
;; Next keyword
;;

(defun font-lock-studio-next-keyword (&optional nonstop)
  "Finish current keyword and go to next.

With \\[universal-argument] prefix, don't stop on breakpoints."
  (interactive "P")
  (font-lock-studio-command-wrapper-step
   (font-lock-studio-fontify-step-while
    `(lambda () (eq font-lock-studio-keyword-number
                    ,font-lock-studio-keyword-number))
    nonstop)))


(defun font-lock-studio-skip-to-next-keyword ()
  "Go to next keyword without finishing the current."
  (interactive)
  (font-lock-studio-command-wrapper-step
   (font-lock-studio-fontify-set-next-keyword)
   (not (eq font-lock-studio-keyword-number :done))))


;; ----------
;; Step over
;;

(defun font-lock-studio-step-over (&optional nonstop)
  "Single step keywords, highlights, and parts of anchored highlights.

With \\[universal-argument] prefix, don't stop on breakpoints."
  (interactive "P")
  (font-lock-studio-command-wrapper-step
   (cond ((eq font-lock-studio-keyword-number :done)
          (message "All done"))
         (font-lock-studio-anchored-state
          (font-lock-studio-fontify-step-do-while
           #'(lambda () nil)
           nonstop))
         (font-lock-studio-highlight-number
          (font-lock-studio-fontify-step-do-while
           `(lambda () (eq font-lock-studio-highlight-number
                           ,font-lock-studio-highlight-number))
           nonstop))
         (t
          (font-lock-studio-fontify-step-do-while
           `(lambda () (eq font-lock-studio-keyword-number
                           ,font-lock-studio-keyword-number))
           nonstop)))))


(defun font-lock-studio-skip-over ()
  "Skip keywords, highlights, and parts of anchored highlights."
  (interactive)
  (font-lock-studio-command-wrapper-step
   (cond (font-lock-studio-anchored-state
          (font-lock-studio-fontify-set-next-anchored-state))
         (font-lock-studio-highlight-number
          (font-lock-studio-fontify-set-next-highlight))
         (t
          (font-lock-studio-fontify-set-next-keyword)))
   (not (eq font-lock-studio-keyword-number :done))))


;; ----------
;; Step into
;;

(defun font-lock-studio-step-into ()
  "Single step into keywords, highlights, and parts of anchored highlights."
  (interactive)
  (font-lock-studio-command-wrapper-step
   (font-lock-studio-fontify-step-do-while #'(lambda () nil))))


(defun font-lock-studio-step-into-and-debug ()
  "Like `font-lock-studio-step-into' but use Edebug to step into expressions."
  (interactive)
  (let ((font-lock-studio-edebug-active t))
    (font-lock-studio-step-into)))


;; ----------
;; Step out
;;

(defun font-lock-studio-step-out (&optional nonstop)
  "Step out of the current context.

When in a highlight of an anchored keyword, go to the matcher of
the anchored highlight.

When in a highlight, to the the matcher of the keyword.

With \\[universal-argument] prefix, don't stop on breakpoints."
  (interactive "P")
  (font-lock-studio-command-wrapper-step
   (cond (font-lock-studio-anchored-state
          (font-lock-studio-fontify-step-do-while
           `(lambda () (eq font-lock-studio-highlight-number
                           ,font-lock-studio-highlight-number))
           nonstop))
         (font-lock-studio-highlight-number
          (font-lock-studio-fontify-step-do-while
           `(lambda () font-lock-studio-highlight-number)
           nonstop))
         (t
          ;; "Step out" -> "Next keyword".
          (font-lock-studio-fontify-step-do-while
           `(lambda () (eq font-lock-studio-keyword-number
                           ,font-lock-studio-keyword-number))
           nonstop)))))


(defun font-lock-studio-skip-out ()
  "Skip out of the current context."
  (interactive)
  (font-lock-studio-command-wrapper-step
   (cond (font-lock-studio-anchored-state
          (while font-lock-studio-anchored-state
            (font-lock-studio-fontify-set-next-anchored-state)))
         (font-lock-studio-highlight-number
          (while (font-lock-studio-fontify-set-next-highlight)))
         (t
          ;; "Step out" -> "Next keyword".
          (font-lock-studio-fontify-set-next-keyword)))
   (not (eq font-lock-studio-keyword-number :done))))


;; ----------
;; Step one keyword match

(defun font-lock-studio-step-keyword-match (&optional nonstop)
  "Step one match of the current font-lock keyword.

With \\[universal-argument] prefix, don't stop on breakpoints."
  (interactive "P")
  (font-lock-studio-command-wrapper-step
   (font-lock-studio-fontify-step-do-while
    `(lambda () (and (eq font-lock-studio-keyword-number
                         ,font-lock-studio-keyword-number)
                     font-lock-studio-highlight-number))
    nonstop)))


;; ----------
;; Breakpoints
;;

(defun font-lock-studio-set-breakpoint ()
  "Set a breakpoint."
  (interactive)
  (font-lock-studio-command-wrapper-save-excursion
   (let ((state (get-text-property (point) 'font-lock-studio-state)))
     (if state
         (let* ((big-state (font-lock-studio-fontify-state-to-big-state state))
                (mode (font-lock-studio-fontify-major-mode-alias))
                (pair (assq mode
                            font-lock-studio-major-mode-breakpoints-alist)))
           (unless pair
             (setq pair (cons mode '()))
             (add-to-list 'font-lock-studio-major-mode-breakpoints-alist pair))
           ;; Here, PAIR is modified.
           (unless (member big-state (cdr pair))
             (setcdr pair (cons big-state (cdr pair))))
           (font-lock-studio-fontify-update-breakpoints)
           (message "Breakpoint set"))
       (user-error "Can't set breakpoint here")))))


(defun font-lock-studio-unset-breakpoint ()
  "Unset a breakpoint."
  (interactive)
  (font-lock-studio-command-wrapper-save-excursion
   (let ((state (get-text-property (point) 'font-lock-studio-state)))
     (if state
         (let* ((big-state (font-lock-studio-fontify-state-to-big-state state))
                (mode (font-lock-studio-fontify-major-mode-alias))
                (pair (assq mode
                            font-lock-studio-major-mode-breakpoints-alist)))
           (if pair
               (setcdr pair (delete big-state (cdr pair))))
           (font-lock-studio-fontify-update-breakpoints)
           (message "Breakpoint unset"))
       (user-error "Can't unset breakpoint here")))))


;; ----------
;; Toggle commands
;;

(defun font-lock-studio-toggle-auto-explain (&optional arg)
  "Toggle if current state should be explained in the message area.

With ARG, a positive value turns this on, a negative off."
  (interactive)
  (font-lock-studio-command-wrapper
   (setq font-lock-studio-auto-explain
         (if arg
             (>= arg 0)
           (not font-lock-studio-auto-explain)))))


(defun font-lock-studio-toggle-show-public-state (&optional arg)
  "Toggle if public state is displayed in Font Lock Studio.

With ARG, a positive value turns this on, a negative off."
  (interactive)
  (font-lock-studio-command-wrapper
   (setq font-lock-studio-show-public-state
         (if arg
             (>= arg 0)
           (not font-lock-studio-show-public-state)))))


(defun font-lock-studio-toggle-show-internal-state (&optional arg)
  "Toggle if internal state is displayed in Font Lock Studio.

With ARG, a positive value turns this on, a negative off."
  (interactive)
  (font-lock-studio-command-wrapper
   (setq font-lock-studio-show-internal-state
         (if arg
             (>= arg 0)
           (not font-lock-studio-show-internal-state)))))


(defun font-lock-studio-toggle-show-compiled-code (&optional arg)
  "Toggle if compiled code is displayed in Font Lock Studio.

With ARG, a positive value turns this on, a negative off."
  (interactive)
  (font-lock-studio-command-wrapper
   (setq font-lock-studio-show-compiled-code
         (if arg
             (>= arg 0)
           (not font-lock-studio-show-compiled-code)))))


(defun font-lock-studio-toggle-debug-on-error (&optional arg)
  "Toggle if the Lisp debugger should be activated when an error occurs.

With ARG, a positive value turns this on, a negative off.

Note that this is a global Emacs option, it is not limited to
Font Lock Studio."
  (interactive)
  (font-lock-studio-command-wrapper
   (setq debug-on-error
         (if arg
             (>= arg 0)
           (not debug-on-error)))))


(defun font-lock-studio-toggle-debug-on-quit (&optional arg)
  "Toggle if the debugger should be used when \\[keyboard-quit] is pressed.
This is useful when tracking down problems in a function that
hangs.

With ARG, a positive value turns this on, a negative off.

Note that this is a global Emacs option, it is not limited to
Font Lock Studio."
  (interactive)
  (font-lock-studio-command-wrapper
   (setq debug-on-quit
         (if arg
             (>= arg 0)
           (not debug-on-quit)))))


;; ----------
;; Support functions
;;

(defun font-lock-studio-format-match-data (md)
  "Format the match data MD."
  (interactive)
  (let ((index 0)
        (msg nil))
    (while md
      (let ((beg (pop md))
            (end (pop md)))
        (if (markerp beg)
            (setq beg (marker-position beg)))
        (if (markerp end)
            (setq end (marker-position end)))
        (if (and beg end)
            (let ((s (format "%d: %d-%d"
                             index
                             beg
                             end)))
              (set-text-properties
               0 (length s)
               (list 'face
                     (list :background
                           (nth (mod index
                                     (length font-lock-studio-color-list))
                                font-lock-studio-color-list)))
               s)
              (setq msg (if msg (concat msg "\n" s) s))))
        (setq index (+ 1 index))))
    (or msg "")))


(defun font-lock-studio-show-match-data ()
  "Echo the active match data in the message area."
  (interactive)
  (if font-lock-studio-keyword-match-data
      (message "Match data:\n%s" (font-lock-studio-format-match-data
                                  font-lock-studio-keyword-match-data))
    (message "Match data not active")))


;; ----------
;; Support functions
;;

(defun font-lock-studio-eval-in-source-buffer (expr)
  "Evaluate an expression in the source buffer.
If interactive, prompt for the expression.
Print result in minibuffer."
  (interactive (list (read-from-minibuffer
		      "Eval: " nil read-expression-map t
		      'read-expression-history)))
  (with-current-buffer font-lock-studio-buffer
    (let ((print-escape-newlines t))
      (princ (eval expr)))))


(defun font-lock-studio-instrument-matcher ()
  "Instrument matcher function symbol, so that it can be debugged in Edebug."
  (interactive)
  (let ((matcher nil))
    (if (numberp font-lock-studio-keyword-number)
        (if font-lock-studio-highlight-number
            (let ((highlight (font-lock-studio-fontify-get-base-highlight)))
              (if (numberp (car highlight))
                  ;; Plain highlight rule.
                  (user-error "Not on match")
                ;; Anchored highlight rule.
                (if (eq font-lock-studio-anchored-state :matcher)
                    (setq matcher (nth 0 highlight))
                  (user-error "Not on match in anchored highlight"))))
          ;; At top-level
          (let ((kw (nth font-lock-studio-keyword-number
                         font-lock-studio-keywords)))
            (setq matcher (car kw))))
      (user-error "No font-lock keyword active"))
    (assert matcher)
    (if (symbolp matcher)
        (edebug-instrument-function matcher)
      (user-error "Matcher is not function symbol"))))


;; Currently not used...
(defun font-lock-studio-edebug-after-point ()
  "Run expression after point with Edebug, in source buffer."
  ;; Black magic and woodoo going on here...
  ;;
  ;; Essentially copied from `edebug-eval-top-level-form', with a
  ;; different reader and with the buffer change.
  (interactive)
  (require 'edebug)
  (let ((expr (let ((edebug-all-forms t)
                    (edebug-all-defs t))
                (edebug-read-and-maybe-wrap-form))))
    (with-current-buffer font-lock-studio-buffer
      (eval-expression expr))))


;; ------------------------------------------------------------
;; Fontification engine.
;;
;; Note that this is *not* the same fontification engine used by the
;; actual font-lock package. This is designed to allow
;; single-stepping, whereas the real engine is designed for raw speed.
;;
;; This engine, however lacks features like recoloring on change and
;; coloring of only visual parts etc.
;;
;; Note that the fontification engine should be able to function
;; without the interface buffer, so all user interaction should be
;; performed by code calling us. Unfortunately, this is somewhat
;; intertwined with the interactive debugger thanks to the edebug
;; integration.


(defmacro font-lock-studio-fontify (&rest body)
  "Like `progn', buffer fontified using the Font Lock Studio engine.

After BODY has been evaluated, the buffer is refontified using
the normal font-lock fontification engine."
  (let ((buffer-var (make-symbol "--buffer--")))
    `(let ((,buffer-var (current-buffer)))
       (with-temp-buffer
         ;; Use temporary buffer as control buffer, without the
         ;; interface.
         (font-lock-studio-fontify-start ,buffer-var)
         (while (not (eq font-lock-studio-keyword-number :done))
           (font-lock-studio-fontify-step))
         (prog1 (with-current-buffer ,buffer-var
                  ,@body)
           (font-lock-studio-fontify-done))))))


(defun font-lock-studio-fontify-start (&optional buffer beg end)
  "Set up the Font Lock Studio fontification engine.

In BUFFER, The region between BEG and END is used."
  (unless buffer
    (setq buffer (current-buffer)))
  (unless beg
    (setq beg (with-current-buffer buffer
                (point-min))))
  (unless end
    (setq end (with-current-buffer buffer
                (point-max))))
  ;; Keep the region as markers, to allow restart to be performed
  ;; after the buffer has been modified.
  (with-current-buffer buffer
    (unless (markerp beg)
      (setq beg (copy-marker beg)))
    (unless (markerp end)
      (setq end (copy-marker end t))))

  (set (make-local-variable 'font-lock-studio-buffer) buffer)
  (set (make-local-variable 'font-lock-studio-region) (cons beg end))
  (set (make-local-variable 'font-lock-studio-original-font-lock-mode)
       (with-current-buffer buffer
         font-lock-mode))
  (let ((keywords (with-current-buffer buffer
                    font-lock-keywords)))
    ;; Strip "compiled" font-lock keywords.
    (if (eq (car-safe keywords) t)
        (setq keywords (nth 1 keywords)))
    (set (make-local-variable 'font-lock-studio-keywords)
         (font-lock-studio-normalize-keywords keywords)))

  (set (make-local-variable 'font-lock-studio-case-fold-search)
       (with-current-buffer buffer
         font-lock-keywords-case-fold-search))

  (set (make-local-variable 'font-lock-studio-multiline)
       (with-current-buffer buffer
         font-lock-multiline))

  (font-lock-studio-fontify-restart))


(defun font-lock-studio-fontify-restart ()
  "Restart the Font Lock Studio fontification engine.

This is expected to be called from a control buffer."
  (let ((beg (car font-lock-studio-region))
        (end (cdr font-lock-studio-region)))

    (with-current-buffer font-lock-studio-buffer
      ;; Disable font-lock.
      (font-lock-mode -1)
      ;; Make `font-lock-face' as an alias for the `face' property.
      (set (make-local-variable 'char-property-alias-alist)
           (copy-tree char-property-alias-alist))
      (let ((pair (assq 'face char-property-alias-alist)))
        (if pair
            (unless (memq 'font-lock-face (cdr pair))
              (setcdr pair (nconc (cdr pair) (list 'font-lock-face))))
          (push (list 'face 'font-lock-face) char-property-alias-alist)))

      ;; Run the "syntactic" font-lock phase.
      (font-lock-studio-save-buffer-state
        (font-lock-fontify-syntactically-region beg end)))

    ;; Set up the control buffer.
    (set (make-local-variable 'font-lock-studio-keyword-number)
         (if font-lock-studio-keywords 0 :done))
    (set (make-local-variable 'font-lock-studio-highlight-number) nil)
    (set (make-local-variable 'font-lock-studio-anchored-state) nil)
    (set (make-local-variable 'font-lock-studio-keyword-match-data) nil)
    (set (make-local-variable 'font-lock-studio-keyword-match-data-saved) nil)
    (make-local-variable 'font-lock-studio-anchored-limit)
    (make-local-variable 'font-lock-studio-edebug-expression-point)
    (set (make-local-variable 'font-lock-studio-point) beg)
    (make-local-variable 'font-lock-studio-fontify-breakpoints)
    (font-lock-studio-fontify-update-breakpoints)))


(defun font-lock-studio-fontify-done ()
  "Exit the Font Lock Studio fontification engine and restore original state."
  ;; Remove the `font-lock-face' alias.
  (with-current-buffer font-lock-studio-buffer
    (set (make-local-variable 'char-property-alias-alist)
         (copy-tree char-property-alias-alist))
    (let ((pair (assq 'face char-property-alias-alist)))
      (when pair
        (setcdr pair (remq 'font-lock-face (cdr pair)))
        (when (null (cdr pair))
          (setq char-property-alias-alist
                (delq pair char-property-alias-alist))))))
  ;; Restore `font-lock-mode'
  (if font-lock-studio-original-font-lock-mode
      (with-current-buffer font-lock-studio-buffer
        (font-lock-mode 1))))


(defun font-lock-studio-fontify-step-while (predicate &optional nonstop)
  "Perform fontification steps while PREDICATE is true.

If NONSTOP is non-nil, don't stop on breakpoints."
  (if (funcall predicate)
      (font-lock-studio-fontify-step-do-while predicate nonstop)
    t))


(defun font-lock-studio-fontify-get-current-state ()
  "The current state.

Return a list on the form:

   (KWRD-NUMBER [HIGHLIGHT-NUMBER [ANCHORED-STATE]])

or nil."
  (let ((state '()))
    (if font-lock-studio-anchored-state
        (push font-lock-studio-anchored-state state))
    (if font-lock-studio-highlight-number
        (push font-lock-studio-highlight-number state))
    (unless (eq font-lock-studio-keyword-number :done)
      (push font-lock-studio-keyword-number state))
    state))


(defun font-lock-studio-fontify-step-do-while (predicate &optional nonstop)
  "Perform fontification steps while PREDICATE is true.
One fontification step is performed before the predicate is tested.

If NONSTOP is non-nil, don't stop on breakpoints.

Return nil if there are no more keywords, `breakpoint' when
stopped on a breakpoint, and t when stopped because the predicate
returned nil."
  (if (eq font-lock-studio-keyword-number :done)
      (error "No more keywords"))
  (let ((res 'continue))
    (while
        (progn
          (font-lock-studio-fontify-step)
          (cond ((eq font-lock-studio-keyword-number :done)
                 (setq res nil))
                ((not (funcall predicate))
                 (setq res t))
                ((and (not nonstop)
                      (member (font-lock-studio-fontify-get-current-state)
                              font-lock-studio-fontify-breakpoints))
                 (setq res 'breakpoint)))
          (eq res 'continue)))
    res))


(defun font-lock-studio-fontify-step ()
  "Perform the next fontification step."
  (interactive)
  (if (eq font-lock-studio-keyword-number :done)
      (error "No more fontification steps")
    (if font-lock-studio-highlight-number
        (let ((highlight (font-lock-studio-fontify-get-base-highlight)))
          (if (numberp (car highlight))
              (font-lock-studio-fontify-current-highlight)
            (cond ((null font-lock-studio-anchored-state)
                   (font-lock-studio-fontify-set-next-anchored-state))
                  ((eq font-lock-studio-anchored-state :pre)
                   (font-lock-studio-fontify-do-anchored-pre-match-form))
                  ((eq font-lock-studio-anchored-state :post)
                   (font-lock-studio-fontify-do-anchored-post-match-form))
                  ((eq font-lock-studio-anchored-state :matcher)
                   (font-lock-studio-fontify-match-anchored-matcher))
                  ((numberp font-lock-studio-anchored-state)
                   (font-lock-studio-fontify-current-anchored-highlight))
                  (t
                   (error "Illegal anchored match state")))))
      (unless (font-lock-studio-fontify-match-current-keyword)
        (font-lock-studio-fontify-set-next-keyword)))))


(defun font-lock-studio-fontify-set-next-keyword ()
  "Set the next keyword to be active.
Return nil when there are no more keywords."
  (font-lock-studio-fontify-set-keyword (+ 1 font-lock-studio-keyword-number)))


(defun font-lock-studio-fontify-set-keyword (keyword-number)
  "Set the KEYWORD-NUMBER to be active.
Return nil if there is no such keyword."
  (setq font-lock-studio-keyword-match-data nil)
  (setq font-lock-studio-keyword-match-data-saved nil)
  (setq font-lock-studio-highlight-number nil)
  (setq font-lock-studio-anchored-state nil)
  (if (>= keyword-number (length font-lock-studio-keywords))
      (progn
        (setq font-lock-studio-keyword-number :done)
        nil)
    (setq font-lock-studio-keyword-number keyword-number)
    (setq font-lock-studio-point (car font-lock-studio-region))
    t))


(defun font-lock-studio-fontify-match-current-keyword ()
  "Search for occurrences described by MATCHER.
Update state and return non-nil if found."
  (assert (eq font-lock-studio-highlight-number nil))
  (let* ((kw (nth font-lock-studio-keyword-number
                  font-lock-studio-keywords))
         (matcher (if (and font-lock-studio-edebug-active
                           font-lock-studio-edebug-expression-point)
                      (font-lock-studio-fontify-read-edebug-expression)
                    (car kw)))
         (res (font-lock-studio-fontify-match-matcher
               matcher
               ;; Limit
               (marker-position (cdr font-lock-studio-region)))))
    (when res
      (font-lock-studio-fontify-set-highlight 0 (cdr kw)))
    res))


(defun font-lock-studio-fontify-match-matcher (matcher &optional limit
                                                       dont-move-forward)
  "Search for MATCHER. See `font-lock-keywords' for details.

LIMIT is the search limit."
  (if (eq font-lock-studio-point limit)
      nil
    (let ((p font-lock-studio-point)
          (case-fold-search font-lock-studio-case-fold-search))
      (let ((res
             (with-current-buffer font-lock-studio-buffer
               ;; Note: Don't set studio buffer local variables here.
               (with-syntax-table (or font-lock-syntax-table (syntax-table))
                 (goto-char p)
                 (if (if (stringp matcher)
                         (re-search-forward matcher limit t)
                       (font-lock-studio-save-buffer-state
                         (funcall matcher limit)))
                     (progn
                       (setq p (point))
                       t)
                   nil)))))
        (when res
          (setq font-lock-studio-keyword-match-data (match-data))
          ;; Font-lock tries to avoid potential problems with matchers
          ;; that don't match anything.
          (unless dont-move-forward
            (unless (> p (match-beginning 0))
              (setq p (+ p 1)))))
        (setq font-lock-studio-point p)
        res))))


(defun font-lock-studio-fontify-get-base-highlight (&optional debug)
  "The current highlight.

If Edebug is enabled and DEBUG is non-nil, the face name
expression is replaced with one that is instrumented by Edebug."
  (let* ((kw (nth font-lock-studio-keyword-number
                  font-lock-studio-keywords))
         (highlight-list (cdr kw))
         (highlight (nth font-lock-studio-highlight-number highlight-list)))
    (font-lock-studio-fontify-maybe-instrument-highlight highlight debug)))


(defun font-lock-studio-fontify-get-anchored-highlight (&optional debug)
  "The current anchored highlight.

See `font-lock-studio-fontify-maybe-instrument-highlight' for DEBUG."
  (assert (numberp font-lock-studio-anchored-state))
  (let* ((base-highlight (font-lock-studio-fontify-get-base-highlight))
         ;; Skip MATCHER, PRE-MATCH-FORM, and POST-MATCH-FORM.
         (highlight-list (nthcdr 3 base-highlight))
         (highlight (nth font-lock-studio-anchored-state
                         highlight-list)))
    (font-lock-studio-fontify-maybe-instrument-highlight highlight debug)))


(defun font-lock-studio-fontify-maybe-instrument-highlight (highlight debug)
  "Return HIGHLIGHT.

If Edebug is enabled and DEBUG is non-nil, the face name
expression is replaced with one that is instrumented by Edebug."
  (if (and debug
           font-lock-studio-edebug-active
           font-lock-studio-edebug-expression-point)
      (cons (car highlight)
            (cons
             (font-lock-studio-fontify-read-edebug-expression)
             (nthcdr 2 highlight)))
    highlight))


(defun font-lock-studio-fontify-read-edebug-expression ()
  "Read the expression of the current form from the interface buffer.
This will allow Edebug to single-step the expression in the
interface buffer itself."
  (require 'edebug)
  (save-excursion
    (goto-char font-lock-studio-edebug-expression-point)
    (let ((expr (let ((edebug-all-forms t)
                      (edebug-all-defs t))
                  (edebug-read-and-maybe-wrap-form))))
      ;; Hack to compensate for the above wrapping lambda:s in a
      ;; "(function (lambda (xxx)...))" construct, which can't be
      ;; applied to "funcall".
      ;;
      ;; TODO: Check if this is something that is new to the Emacs
      ;; trunk, it doesn't appear to behave like this in 24.3.
      (if (and (listp expr)
               (eq (car expr) 'function)
               (listp (nth 1 expr))
               (eq (car (nth 1 expr)) 'lambda))
          (nth 1 expr)
        expr))))


(defun font-lock-studio-fontify-current-highlight ()
  "Fontify current highlight.
Return nil if there are no more highlights."
  (assert font-lock-studio-highlight-number)
  (let ((highlight (font-lock-studio-fontify-get-base-highlight :instrument)))
    (set-match-data font-lock-studio-keyword-match-data)
    (assert (numberp (car highlight)))
    (font-lock-studio-fontify-highlight highlight)
    (font-lock-studio-fontify-set-next-highlight)))


(defun font-lock-studio-fontify-set-next-highlight ()
  "Pick next highlight.
Return nil when there are no more highlights."
  (font-lock-studio-fontify-set-highlight
   (+ 1 font-lock-studio-highlight-number)))


(defun font-lock-studio-fontify-set-highlight (number &optional highlight-list)
  "Set the highlight NUMBER.

Return nil if there is no such highlight.

If HIGHLIGHT-LIST is non nil, it should be the list of highlights
of the current keyword."
  (setq font-lock-studio-anchored-state nil)
  (unless highlight-list
    (let ((kw (nth font-lock-studio-keyword-number
                   font-lock-studio-keywords)))
      (setq highlight-list (cdr kw))))
  (if (< number (length highlight-list))
      (progn
        (setq font-lock-studio-highlight-number number)
        t)
    (setq font-lock-studio-keyword-match-data nil)
    (setq font-lock-studio-highlight-number nil)
    nil))

(defun font-lock-studio-fontify-highlight (highlight)
  "Fontify HIGHLIGHT is the source buffer."
  (set-match-data font-lock-studio-keyword-match-data)
  (let ((p font-lock-studio-point))
    (with-current-buffer font-lock-studio-buffer
      (goto-char p)
      (font-lock-studio-save-buffer-state
        (font-lock-apply-highlight highlight))))
  ;; Ensure that point movements performed by the FACE expression
  ;; are preserved.
  (setq font-lock-studio-point (with-current-buffer font-lock-studio-buffer
                                 (point)))
  (setq font-lock-studio-keyword-match-data (match-data)))


;; --------------------
;; Anchored highlight rules.

(defun font-lock-studio-fontify-do-anchored-pre-match-form ()
  "Run the pre-match form of an anchored highlight rule."
  (assert (eq font-lock-studio-anchored-state :pre))
  (let* ((p font-lock-studio-point)
         (highlight (font-lock-studio-fontify-get-base-highlight))
         (expr (if (and font-lock-studio-edebug-active
                        font-lock-studio-edebug-expression-point)
                   (font-lock-studio-fontify-read-edebug-expression)
                 (nth 1 highlight)))
         (multiline font-lock-studio-multiline)
         limit)
    (set-match-data font-lock-studio-keyword-match-data)
    (with-current-buffer font-lock-studio-buffer
      (goto-char p)
      (let ((pre-match-value (eval expr)))
        (setq p (point))
        (setq limit (if (and (numberp pre-match-value)
                             (> pre-match-value (point))
                             (or multiline
                                 (<= pre-match-value (line-end-position))))
                        pre-match-value
                      (line-end-position)))))
    (setq font-lock-studio-keyword-match-data (match-data))
    (setq font-lock-studio-point p)
    (setq font-lock-studio-anchored-limit limit)
    (font-lock-studio-fontify-set-next-anchored-state)))


(defun font-lock-studio-fontify-do-anchored-post-match-form ()
  "Run the post-match form of an anchored highlight rule."
  (assert (eq font-lock-studio-anchored-state :post))
  (let* ((p font-lock-studio-point)
         (highlight (font-lock-studio-fontify-get-base-highlight))
         (expr (if (and font-lock-studio-edebug-active
                        font-lock-studio-edebug-expression-point)
                   (font-lock-studio-fontify-read-edebug-expression)
                 (nth 2 highlight))))
    (set-match-data font-lock-studio-keyword-match-data)
    (with-current-buffer font-lock-studio-buffer
      (goto-char p)
      (eval expr)
      (setq p (point)))
    (setq font-lock-studio-keyword-match-data (match-data))
    (setq font-lock-studio-point p)
    (font-lock-studio-fontify-set-next-anchored-state)))


(defun font-lock-studio-fontify-match-anchored-matcher ()
  "Search for MATCHER in current anchored highlight rule.
Return nil when no match was found."
  (assert (eq font-lock-studio-anchored-state :matcher))
  (let ((highlight (font-lock-studio-fontify-get-base-highlight)))
    (set-match-data font-lock-studio-keyword-match-data)
    (let ((matched (font-lock-studio-fontify-match-matcher
                    (if (and font-lock-studio-edebug-active
                             font-lock-studio-edebug-expression-point)
                        (font-lock-studio-fontify-read-edebug-expression)
                      (nth 0 highlight))
                    font-lock-studio-anchored-limit
                    'dont-move-point)))
      (font-lock-studio-fontify-set-next-anchored-state matched)
      matched)))


(defun font-lock-studio-fontify-current-anchored-highlight ()
  "Fontify current highlight in an anchored rule."
  (assert (numberp font-lock-studio-anchored-state))
  (font-lock-studio-fontify-highlight
   (font-lock-studio-fontify-get-anchored-highlight :instrument))
  (font-lock-studio-fontify-set-next-anchored-state))


;;
;; Anchored state machine as follows:
;;
;;     nil
;;      |
;;      |
;;    :pre
;;      |
;;      +<-----+<-------+<-------+<-- ...
;;      |      |        |        |
;;   :matcher -+->  0  -+->  1  -+--> ...
;;      |
;;      |
;;    :post
;;      |
;;      |
;;    Next highlight or keyword, if any
;;

(defun font-lock-studio-fontify-set-next-anchored-state
    (&optional matched base-highlight)
  "Set the next fontification state, from inside an anchored highlight rule.

In the state :matcher, match is assumed to have succeeded if
MATCHED is non-nil.

If BASE-HIGHLIGHT is non-nil, it should be the current base highlight."
  (unless base-highlight
    (setq base-highlight (font-lock-studio-fontify-get-base-highlight)))
  (assert (not (numberp base-highlight)))
  (let ((len (length base-highlight)))
    (while (progn
             (font-lock-studio-fontify-set-next-anchored-state0
              matched base-highlight)
             (cond ((null font-lock-studio-anchored-state)
                    nil)
                   ((eq font-lock-studio-anchored-state :pre)
                    (<= len 1))
                   ((eq font-lock-studio-anchored-state :post)
                    (<= len 2))
                   ((eq font-lock-studio-anchored-state :matcher)
                    nil)
                   ((numberp font-lock-studio-anchored-state)
                    (when (>= font-lock-studio-anchored-state (- len 3))
                      (setq font-lock-studio-anchored-state :matcher))
                    nil)
                   (t
                    (error "Unexpected anchor state")))))))


;; For example, this may set :pre state even if there is no
;; PRE-MATCH-FORM in the highlight.
(defun font-lock-studio-fontify-set-next-anchored-state0
    (matched base-highlight)
  "Set next anchored state, new state might not correspond to existing part.

See `font-lock-studio-fontify-set-next-anchored-state' for details."
  (cond ((null font-lock-studio-anchored-state)
         ;; Set default anchored search limit. This is used when
         ;; there is no :pre form or when it is skipped.
         (setq font-lock-studio-anchored-limit
               (let ((p font-lock-studio-point))
                 (with-current-buffer font-lock-studio-buffer
                   (save-excursion
                     (goto-char p)
                     (line-end-position)))))
         (setq font-lock-studio-anchored-state :pre))
        ((eq font-lock-studio-anchored-state :pre)
         (setq font-lock-studio-keyword-match-data-saved
               font-lock-studio-keyword-match-data)
         (setq font-lock-studio-anchored-state :matcher))
        ((eq font-lock-studio-anchored-state :matcher)
         (if matched
             (setq font-lock-studio-anchored-state 0)
           (setq font-lock-studio-keyword-match-data
                 font-lock-studio-keyword-match-data-saved)
           (setq font-lock-studio-keyword-match-data-saved nil)
           (setq font-lock-studio-anchored-state :post)))
        ((eq font-lock-studio-anchored-state :post)
         (font-lock-studio-fontify-set-next-highlight))
        ((numberp font-lock-studio-anchored-state)
         (setq font-lock-studio-anchored-state
               (+ 1 font-lock-studio-anchored-state)))
        (t
         (error "Not in anchored rule"))))


;; --------------------
;; Breakpoint support.
;;

(defun font-lock-studio-fontify-major-mode-alias (&optional mode)
  "The major mode used as holder of breakpoints for the current source buffer.

Typically, the major mode of the source buffer (or MODE, if
specified), unless listed in
`font-lock-studio-major-mode-alias'."
  (unless mode
    (setq mode (with-current-buffer font-lock-studio-buffer
                 major-mode)))
  (let ((res mode))
    (dolist (alias font-lock-studio-major-mode-alias)
      (if (memq mode alias)
          (setq res (car alias))))
    res))


(defun font-lock-studio-fontify-state-to-big-state (state)
  "Convert STATE to \"big state\" form.

The big state is immune to keywords being added or removed, as it
does not contain the keyword number.

See `font-lock-studio-major-mode-breakpoints-alist' for details."
  ;; Here, state is (KWRD-NUMBER [HIGHLIGHT-NUMBER [ANCHORED-STATE]])
  (let* ((keyword-number (car state))
         (kw (nth keyword-number font-lock-studio-keywords))
         (count 0)
         (i 0))
    ;; Check if there are keywords identical to ours prior to us.
    (while (< i keyword-number)
      (if (equal kw (nth i font-lock-studio-keywords))
          (setq count (+ count 1)))
      (setq i (+ i 1)))
    ;; Create (FULLKWRD COUNT [HIGHLIGHT-NUMBER [ANCHORED-STATE]])
    (cons kw
          (cons count
                (cdr state)))))


(defun font-lock-studio-fontify-update-breakpoints ()
  "Update `font-lock-studio-fontify-breakpoints' from saved breakpoints.

See `font-lock-studio-major-mode-breakpoints-alist' for details."
  (setq font-lock-studio-fontify-breakpoints '())
  (let ((bps-long
         (cdr-safe (assq (font-lock-studio-fontify-major-mode-alias)
                         font-lock-studio-major-mode-breakpoints-alist))))
    (dolist (bp bps-long)
      (let ((count 0)
            (equal-keywords 0))
        (dolist (kw font-lock-studio-keywords)
          (if (and (equal kw (car bp))
                   (eq equal-keywords (nth 1 bp)))
              (push (cons count (cdr (cdr bp)))
                    font-lock-studio-fontify-breakpoints))
          (setq count (+ count 1))
          (if (equal kw (car bp))
              (setq equal-keywords (+ equal-keywords 1))))))))


;; --------------------
;; Keyword normalizer
;;

(defun font-lock-studio-normalize-keywords (keywords)
  "Make sure all KEYWORDS are on a similar form.

For keywords on the form `(eval . FORM)', FORM is evaluated and
the result is used.

Converts:                   To:
--------                    --
MATCHER                     (MATCHER (0 font-lock-keyword-face))
\(MATCHER . SUBEXP)          (MATCHER (SUBEXP font-lock-keyword-face))
\(MATCHER . FACENAME)        (MATCHER (0 FACENAME))
\(MATCHER . 'FACENAME)       (MATCHER (0 'FACENAME))
\(MATCHER . HIGHLIGHT)       (MATCHER HIGHLIGHT)"
  (let ((res '()))
    (dolist (kw keywords)
      (if (eq (car-safe kw) 'eval)
          (setq kw
                (with-current-buffer font-lock-studio-buffer
                  (eval (cdr kw)))))
      (cond ((or (not (consp kw))
                 (eq (car kw) 'lambda))
             (setq kw (list kw '(0 font-lock-keyword-face))))
            ((numberp (cdr kw))
             (setq kw (list (car kw) (list (cdr kw) 'font-lock-keyword-face))))
            ((and (eq (car-safe (cdr kw)) 'quote)
                  (symbolp (nth 2 kw)))
             (setq kw (list (car kw) (list 0 (cdr kw)))))
            ((symbolp (cdr kw))
             (setq kw (list (car kw) (list 0 (cdr kw)))))
            ((not (consp (car (cdr kw))))
             (setq kw (list (car kw) (cdr kw)))))
      (push kw res))
    (nreverse res)))


;; ------------------------------------------------------------
;; Convenience functions.
;;

(defun font-lock-studio-list-colors ()
  "List Font Lock Studio colors using `list-colors-display'."
  (interactive)
  (list-colors-display font-lock-studio-color-list
                       "*Font Lock Studio Colors*"))


(defun font-lock-studio-color-test (&optional arg)
  "List Font Lock Studio colors over text with typical font-lock faces.

If ARG is non-nil, list all defined colors."
  (interactive "P")
  (with-help-window "*Font Lock Studio Colors*"
    (let ((faces '(font-lock-string-face
                   font-lock-comment-face
                   font-lock-builtin-face
                   font-lock-constant-face
                   font-lock-keyword-face
                   font-lock-preprocessor-face
                   font-lock-reference-face
                   font-lock-variable-name-face
                   font-lock-function-name-face
                   font-lock-warning-face
                   font-lock-type-face
                   nil
                   )))
      (let ((indent ""))
        (dolist (face faces)
          (let ((s (concat (symbol-name face) indent)))
            (insert (format "%74s" s))
            (insert "\n")
            (setq indent (concat "    |" indent))))
        (dolist (color (if arg (defined-colors) font-lock-studio-color-list))
          (let ((name color))
            (insert (format "%-15s:  " name))
            (dolist (face (reverse faces))
              (let ((teststring "t(1)-"))
                (put-text-property 0 (length teststring)
                                   'face (list :background color) teststring)
                (font-lock-append-text-property 0 (length teststring)
                                                'face face teststring)
                (insert teststring)))
            (insert "\n")))))))


;; ------------------------------------------------------------
;; The end
;;

(provide 'font-lock-studio)

;;; font-lock-studio.el ends here
