# Org Subtree Markdown Clipboard Command Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend `org-ext-copy-subtree-as-markdown` so it clears and reuses `*Org MD Export*`, removes table-of-contents output, generated anchor targets, workflow keywords, and both drawer-contained and standalone state transitions, copies the formatted Markdown, and displays the same buffer with `pop-to-buffer`.

**Architecture:** Continue narrowing the source subtree and exporting it without `SUBTREEP`. Append a command-local options filter so the command's structural requirements win after user and file-local option resolution, remove generated empty anchor targets and standard standalone state-transition entries from the returned Markdown, and format the result in Org's reusable Markdown export buffer before copying and displaying it.

**Tech Stack:** Emacs Lisp with lexical binding, Org's built-in `ox-md` exporter, the repository-local `mdformat.el`, and ERT.

## Global Constraints

- The public command remains `org-ext-copy-subtree-as-markdown` and takes no arguments.
- The source buffer, point, active region, and pre-existing restriction remain unchanged.
- Content outside the current subtree is not exported.
- The subtree root is retained as an ATX level-one Markdown heading.
- Current task headings remain in the export, but all workflow keywords are omitted from root and nested headings.
- The table of contents, generated `<a id="…"></a>` targets, `LOGBOOK` state transitions, and standalone state-transition entries are absent.
- Ordinary Markdown links and non-LOGBOOK drawers remain eligible for export.
- `*Org MD Export*` is cleared before each export and reused rather than duplicated.
- Formatting completes before clipboard mutation and `pop-to-buffer`.
- Export and formatting errors propagate, and neither failure changes the clipboard or displays the output buffer.
- Export failure leaves the reusable buffer empty; formatter failure leaves cleaned, unformatted Markdown in it.
- `ox-md` and `mdformat` load on demand, with no new dependency.
- Existing unrelated working-tree changes remain untouched.
- Do not commit or push unless the user separately authorizes those operations.

---

## File Map

- Modify `org-ext-test.el`: strengthen the three command tests to cover export-option precedence, cleanup of both forms of state log, workflow-keyword suppression, reusable-buffer lifecycle, display ordering, and both failure states.
- Modify `org-ext.el`: reuse `*Org MD Export*`, enforce final export options, remove generated anchor targets and standalone state transitions, and display successful output.
- Update `docs/superpowers/specs/2026-07-24-org-subtree-markdown-clipboard-design.md`: revised and approved for the corrective behavior.

### Task 1: Clean, Copy, and Display the Reusable Markdown Buffer

This task records the original implementation baseline. Task 2 supersedes its workflow-keyword and standalone-transition expectations while retaining its buffer, clipboard, and failure-lifecycle behavior.

**Files:**
- Modify: `org-ext-test.el:127-225`
- Modify: `org-ext.el:884-911`

**Interfaces:**
- Consumes: `(org-export-as 'md)`, `org-export-filter-options-functions`, `(mdformat-buffer)`, `(kill-new STRING)`, `(get-buffer-create "*Org MD Export*")`, and `(pop-to-buffer BUFFER)`.
- Produces: `(org-ext-copy-subtree-as-markdown)`, with the successful formatted output retained in and displayed from `*Org MD Export*`.

- [x] **Step 1: Replace the focused ERT tests with the revised behavior tests**

Replace the three `org-ext-copy-subtree-as-markdown-*` tests in `org-ext-test.el` with:

```elisp
(ert-deftest org-ext-copy-subtree-as-markdown-formats-before-copying ()
  (skip-unless (not (get-buffer "*Org MD Export*")))
  (let ((output-buffer (get-buffer-create "*Org MD Export*")))
    (unwind-protect
        (progn
          (with-current-buffer output-buffer
            (insert "STALE\n"))
          (with-temp-buffer
            (org-mode)
            (insert "#+OPTIONS: toc:t d:t tasks:nil todo:nil\n"
                    "* Before\nOutside\n"
                    "* Container\n"
                    "** TODO Parent\nBody\n"
                    "See [[#child][child]].\n"
                    ":LOGBOOK:\n"
                    "- State \"NEXT\" from \"TODO\" [2026-07-24 Fri]\n"
                    ":END:\n"
                    ":NOTES:\n"
                    "Keep drawer text.\n"
                    ":END:\n"
                    "*** DONE Child\n"
                    ":PROPERTIES:\n"
                    ":CUSTOM_ID: child\n"
                    ":END:\n"
                    "Nested\n"
                    "** Sibling\nNot copied\n"
                    "* After\nOutside\n")
            (let* ((original (buffer-string))
                   (narrow-start
                    (progn
                      (goto-char (point-min))
                      (re-search-forward "^\\*\\* TODO Parent$")
                      (line-beginning-position)))
                   (narrow-end
                    (progn
                      (re-search-forward "^\\* After$")
                      (line-beginning-position))))
              (narrow-to-region narrow-start narrow-end)
              (goto-char narrow-start)
              (forward-line)
              (set-mark (point))
              (end-of-line)
              (setq mark-active t)
              (let ((original-point (point))
                    (org-md-headline-style 'setext)
                    (org-md-toplevel-hlevel 2)
                    (org-export-with-toc t)
                    (org-export-with-drawers t)
                    (org-export-with-tasks nil)
                    (org-export-with-todo-keywords nil)
                    (interprogram-cut-function nil)
                    (interprogram-paste-function nil)
                    copied
                    displayed
                    events)
                (cl-letf (((symbol-function 'mdformat-buffer)
                           (lambda ()
                             (setq events (append events '(format)))
                             (goto-char (point-max))
                             (insert "FORMATTED\n")))
                          ((symbol-function 'kill-new)
                           (lambda (string &optional _replace)
                             (setq copied string
                                   events (append events '(copy)))))
                          ((symbol-function 'pop-to-buffer)
                           (lambda (buffer &rest _)
                             (setq displayed buffer
                                   events (append events '(pop)))
                             buffer)))
                  (org-ext-copy-subtree-as-markdown))
                (let ((markdown
                       (with-current-buffer output-buffer
                         (buffer-string))))
                  (should (equal events '(format copy pop)))
                  (should (eq displayed output-buffer))
                  (should (equal copied markdown))
                  (should (string-match-p "^# TODO Parent$" markdown))
                  (should (string-match-p "^## DONE Child$" markdown))
                  (should (string-match-p "\\[child\\](#child)" markdown))
                  (should (string-match-p "Keep drawer text\\." markdown))
                  (should-not (string-match-p "Table of Contents" markdown))
                  (should-not (string-match-p "<a id=" markdown))
                  (should-not (string-match-p "State \"" markdown))
                  (should-not (string-match-p "Sibling" markdown))
                  (should-not (string-match-p "STALE" markdown))
                  (should (string-suffix-p "FORMATTED\n" markdown)))
                (with-current-buffer output-buffer
                  (should (eq major-mode 'text-mode))
                  (should (= (point) (point-min))))
                (should (= original-point (point)))
                (should mark-active)
                (should (= narrow-start (point-min)))
                (should (= narrow-end (point-max)))
                (save-restriction
                  (widen)
                  (should (equal original (buffer-string))))))))
      (when (buffer-live-p output-buffer)
        (kill-buffer output-buffer)))))

(ert-deftest org-ext-copy-subtree-as-markdown-keeps-clipboard-on-format-error ()
  (skip-unless (not (get-buffer "*Org MD Export*")))
  (let ((output-buffer (get-buffer-create "*Org MD Export*")))
    (unwind-protect
        (progn
          (with-current-buffer output-buffer
            (insert "STALE\n"))
          (with-temp-buffer
            (org-mode)
            (insert "* Parent\nBody\n")
            (goto-char (point-min))
            (let* ((kill-ring '("existing clipboard"))
                   (kill-ring-yank-pointer kill-ring)
                   (interprogram-cut-function nil)
                   (interprogram-paste-function nil)
                   format-buffer
                   unformatted
                   copy-called
                   pop-called)
              (cl-letf (((symbol-function 'mdformat-buffer)
                         (lambda ()
                           (setq format-buffer (current-buffer)
                                 unformatted (buffer-string))
                           (user-error "format failed")))
                        ((symbol-function 'kill-new)
                         (lambda (&rest _) (setq copy-called t)))
                        ((symbol-function 'pop-to-buffer)
                         (lambda (&rest _) (setq pop-called t))))
                (should-error (org-ext-copy-subtree-as-markdown)
                              :type 'user-error))
              (should (eq format-buffer output-buffer))
              (should-not copy-called)
              (should-not pop-called)
              (should (equal kill-ring '("existing clipboard")))
              (with-current-buffer output-buffer
                (should (equal (buffer-string) unformatted))
                (should (string-match-p "^# Parent$" (buffer-string)))
                (should-not (string-match-p "STALE" (buffer-string)))))))
      (when (buffer-live-p output-buffer)
        (kill-buffer output-buffer)))))

(ert-deftest org-ext-copy-subtree-as-markdown-keeps-clipboard-on-export-error ()
  (skip-unless (not (get-buffer "*Org MD Export*")))
  (let ((output-buffer (get-buffer-create "*Org MD Export*")))
    (unwind-protect
        (progn
          (with-current-buffer output-buffer
            (insert "STALE\n"))
          (with-temp-buffer
            (org-mode)
            (insert "* Parent\nBody\n")
            (goto-char (point-min))
            (let* ((kill-ring '("existing clipboard"))
                   (kill-ring-yank-pointer kill-ring)
                   (interprogram-cut-function nil)
                   (interprogram-paste-function nil)
                   format-called
                   copy-called
                   pop-called)
              (cl-letf (((symbol-function 'org-export-as)
                         (lambda (&rest _) (user-error "export failed")))
                        ((symbol-function 'mdformat-buffer)
                         (lambda () (setq format-called t)))
                        ((symbol-function 'kill-new)
                         (lambda (&rest _) (setq copy-called t)))
                        ((symbol-function 'pop-to-buffer)
                         (lambda (&rest _) (setq pop-called t))))
                (should-error (org-ext-copy-subtree-as-markdown)
                              :type 'user-error))
              (should-not format-called)
              (should-not copy-called)
              (should-not pop-called)
              (should (equal kill-ring '("existing clipboard")))
              (with-current-buffer output-buffer
                (should (string-empty-p (buffer-string)))))))
      (when (buffer-live-p output-buffer)
        (kill-buffer output-buffer)))))
```

- [x] **Step 2: Run the focused tests and verify the revised red state**

Run from `lisp/`:

```bash
EMACS=/nix/store/jy03vl70sl38vkrmp5nw0qj93kipf4jp-emacs-mac-macport-30.2.50/bin/emacs
"$EMACS" --batch -Q -L . -l org-ext-test.el \
  --eval '(ert-run-tests-batch-and-exit "^org-ext-copy-subtree-as-markdown-")'
```

Expected: all three tests load and run but fail against the current disposable-buffer implementation. The success test must show missing reusable-buffer/display cleanup behavior; the two error tests must show that `*Org MD Export*` was not cleared or populated as specified. A syntax, load, or unrelated test error is not the expected red state.

- [x] **Step 3: Replace the command's export and output pipeline**

Declare the dynamically bound Org export filter variable beside the existing external-function declarations:

```elisp
(defvar org-export-filter-options-functions)
```

Replace `org-ext-copy-subtree-as-markdown` in `org-ext.el` with:

```elisp
;;;###autoload
(defun org-ext-copy-subtree-as-markdown ()
  "Copy and display the current Org subtree as formatted Markdown.
Retain the subtree root as an ATX level-one heading while omitting the
TOC, generated anchor targets, and LOGBOOK state transitions."
  (interactive)
  (require 'ox-md)
  (require 'mdformat)
  (let ((mark-active nil)
        (output-buffer (get-buffer-create "*Org MD Export*"))
        markdown)
    (with-current-buffer output-buffer
      (let ((inhibit-read-only t))
        (erase-buffer))
      (text-mode))
    (let ((org-export-filter-options-functions
           (append
            org-export-filter-options-functions
            (list
             (lambda (options _backend)
               (dolist (setting
                        '((:md-headline-style atx)
                          (:md-toplevel-hlevel 1)
                          (:with-tasks t)
                          (:with-todo-keywords t)
                          (:with-toc nil)
                          (:with-drawers (not "LOGBOOK"))))
                 (setq options
                       (plist-put options (car setting) (cadr setting))))
               options)))))
      (save-restriction
        (org-narrow-to-subtree)
        (setq markdown (org-export-as 'md))))
    (setq markdown
          (replace-regexp-in-string
           "^<a id=\"[^\"]+\"></a>[ \t]*\n*" "" markdown))
    (with-current-buffer output-buffer
      (insert markdown)
      (mdformat-buffer)
      (kill-new (buffer-string))
      (goto-char (point-min)))
    (pop-to-buffer output-buffer)
    (message "Formatted Markdown subtree copied and displayed")))
```

- [x] **Step 4: Run the focused tests and verify the green state**

```bash
EMACS=/nix/store/jy03vl70sl38vkrmp5nw0qj93kipf4jp-emacs-mac-macport-30.2.50/bin/emacs
"$EMACS" --batch -Q -L . -l org-ext-test.el \
  --eval '(ert-run-tests-batch-and-exit "^org-ext-copy-subtree-as-markdown-")'
```

Expected: `Ran 3 tests, 3 results as expected, 0 unexpected`.

- [x] **Step 5: Run the complete `org-ext` ERT suite**

```bash
EMACS=/nix/store/jy03vl70sl38vkrmp5nw0qj93kipf4jp-emacs-mac-macport-30.2.50/bin/emacs
"$EMACS" --batch -Q -L . -l org-ext-test.el \
  -f ert-run-tests-batch-and-exit
```

Expected: `Ran 6 tests, 6 results as expected, 0 unexpected`.

- [x] **Step 6: Exercise the real formatter without changing the system clipboard or opening a batch window**

```bash
EMACS=/nix/store/jy03vl70sl38vkrmp5nw0qj93kipf4jp-emacs-mac-macport-30.2.50/bin/emacs
"$EMACS" --batch -Q -L . -l org-ext-test.el \
  --eval '(with-temp-buffer
            (org-mode)
            (insert "#+OPTIONS: toc:t d:t\n"
                    "* TODO Parent\n"
                    ":LOGBOOK:\n"
                    "- State \"DONE\" from \"TODO\" [2026-07-24 Fri]\n"
                    ":END:\n"
                    "** Child\nNested.\n")
            (goto-char (point-min))
            (re-search-forward "^\\* TODO Parent$")
            (beginning-of-line)
            (let ((kill-ring nil)
                  (kill-ring-yank-pointer nil)
                  (interprogram-cut-function nil)
                  (interprogram-paste-function nil))
              (cl-letf (((symbol-function (quote pop-to-buffer))
                         (lambda (buffer &rest _) buffer)))
                (unwind-protect
                    (progn
                      (org-ext-copy-subtree-as-markdown)
                      (let ((markdown (car kill-ring)))
                        (unless (and (string-match-p "^# TODO Parent$" markdown)
                                     (not (string-match-p "Table of Contents" markdown))
                                     (not (string-match-p "<a id=" markdown))
                                     (not (string-match-p "State \"" markdown)))
                          (error "Unexpected Markdown: %S" markdown))
                        (princ "real mdformat integration: ok\n")))
                  (when-let ((buffer (get-buffer "*Org MD Export*")))
                    (kill-buffer buffer))))))'
```

Expected: `mdformat: buffer reformatted`, the command success message, and `real mdformat integration: ok`.

- [x] **Step 7: Byte-compile without introducing diagnostics**

```bash
DEPS=/nix/store/chhmf76w149f1zps5nh1y9nlvsnl2w1b-emacs-packages-deps/share/emacs/site-lisp/elpa
EMACS=/nix/store/jy03vl70sl38vkrmp5nw0qj93kipf4jp-emacs-mac-macport-30.2.50/bin/emacs
EMACSLOADPATH="$(find "$DEPS" -mindepth 1 -maxdepth 1 -type d -print | paste -sd: -):" \
  "$EMACS" --batch -Q -L . \
  --eval '(progn
            (require (quote bytecomp))
            (let ((byte-compile-dest-file-function
                   (lambda (_)
                     (expand-file-name "org-ext.elc"
                                       temporary-file-directory))))
              (unless (byte-compile-file "org-ext.el")
                (kill-emacs 1))))'
```

Expected: exit status 0. Existing warnings outside this change may remain; no diagnostic may refer to `org-ext-copy-subtree-as-markdown`, the command-local options filter, `mdformat-buffer`, or `pop-to-buffer`.

- [x] **Step 8: Review the final diff and repository state**

```bash
git diff --check
git diff -- org-ext.el org-ext-test.el
git status --short --branch
```

Expected: no whitespace errors; only the approved command, test, specification, and plan changes are present in this worktree. Leave all work uncommitted and unpushed.

### Task 2: Omit Workflow Keywords and Standalone State Transitions

**Files:**
- Modify: `org-ext-test.el:127-206`
- Modify: `org-ext.el:884-927`

**Interfaces:**
- Consumes: the existing command-local `org-export-filter-options-functions` filter and the Markdown string returned by `(org-export-as 'md)`.
- Produces: task headings without Org workflow keywords and Markdown without standard standalone `- State "…" from "…"` entries.

- [x] **Step 1: Extend the successful-path regression test**

In `org-ext-copy-subtree-as-markdown-formats-before-copying`, change the hostile export settings to request workflow keywords, add a standalone transition matching the reported input, retain an ordinary list item, and change the heading assertions:

```elisp
(insert "#+OPTIONS: toc:t d:t tasks:nil todo:t\n"
        "* Before\nOutside\n"
        "* Container\n"
        "** TODO Parent\nBody\n"
        "- State \"TODO\"       from \"PROMPT\"     [2026-07-24 Fri 10:05]\n"
        "- Keep this ordinary list item.\n"
        "See [[#child][child]].\n"
        ":LOGBOOK:\n"
        "- State \"NEXT\" from \"TODO\" [2026-07-24 Fri]\n"
        ":END:\n"
        ":NOTES:\n"
        "Keep drawer text.\n"
        ":END:\n"
        "*** DONE Child\n"
        ":PROPERTIES:\n"
        ":CUSTOM_ID: child\n"
        ":END:\n"
        "Nested\n"
        "** Sibling\nNot copied\n"
        "* After\nOutside\n")
```

Bind `org-export-with-todo-keywords` to `t`, then replace and extend the successful-output assertions with:

```elisp
(should (string-match-p "^# Parent$" markdown))
(should (string-match-p "^## Child$" markdown))
(should-not (string-match-p "^#+ .*\\_<\\(?:TODO\\|DONE\\|NEXT\\|PROMPT\\)\\_>" markdown))
(should-not (string-match-p "State \"" markdown))
(should (string-match-p "Keep this ordinary list item\\." markdown))
```

- [x] **Step 2: Run the focused tests and verify the corrective red state**

Run from `lisp/`:

```bash
EMACS=/nix/store/jy03vl70sl38vkrmp5nw0qj93kipf4jp-emacs-mac-macport-30.2.50/bin/emacs
"$EMACS" --batch -Q -L . -l org-ext-test.el \
  --eval '(ert-run-tests-batch-and-exit "^org-ext-copy-subtree-as-markdown-")'
```

Expected: `org-ext-copy-subtree-as-markdown-formats-before-copying` fails because the current command emits `# TODO Parent`, `## DONE Child`, and the standalone `State "TODO" from "PROMPT"` list entry. The two failure-lifecycle tests continue to pass.

- [x] **Step 3: Apply the minimal exporter correction**

In the command-local options list, change:

```elisp
(:with-todo-keywords t)
```

to:

```elisp
(:with-todo-keywords nil)
```

Then replace the anchor-only cleanup with nested, narrow cleanups:

```elisp
(setq markdown
      (replace-regexp-in-string
       "^-[ \t]+State \"[^\"]+\"[ \t]+from \"[^\"]+\"[^\n]*\n*" ""
       (replace-regexp-in-string
        "^<a id=\"[^\"]+\"></a>[ \t]*\n*" "" markdown)))
```

The transition expression requires the standard `State "…" from "…"` form; ordinary list items remain intact.

- [x] **Step 4: Run the focused and complete ERT suites**

```bash
EMACS=/nix/store/jy03vl70sl38vkrmp5nw0qj93kipf4jp-emacs-mac-macport-30.2.50/bin/emacs
"$EMACS" --batch -Q -L . -l org-ext-test.el \
  --eval '(ert-run-tests-batch-and-exit "^org-ext-copy-subtree-as-markdown-")'
"$EMACS" --batch -Q -L . -l org-ext-test.el \
  -f ert-run-tests-batch-and-exit
```

Expected: the focused suite reports 3/3 passing and the complete suite reports 6/6 passing.

- [x] **Step 5: Exercise the reported input with the real formatter**

```bash
EMACS=/nix/store/jy03vl70sl38vkrmp5nw0qj93kipf4jp-emacs-mac-macport-30.2.50/bin/emacs
"$EMACS" --batch -Q -L . -l org-ext-test.el \
  --eval '(with-temp-buffer
            (org-mode)
            (insert "* TODO Create heavy-review command to run all reviews on any scope\n"
                    ":PROPERTIES:\n:ID: AC9D8C5E-4222-461D-9366-2599452A6E92\n:END:\n"
                    "- State \"TODO\"       from \"PROMPT\"     [2026-07-24 Fri 10:05]\n"
                    "- Keep this ordinary list item.\n"
                    "** DONE Child\nNested.\n")
            (goto-char (point-min))
            (let ((kill-ring nil)
                  (kill-ring-yank-pointer nil)
                  (interprogram-cut-function nil)
                  (interprogram-paste-function nil))
              (cl-letf (((symbol-function (quote pop-to-buffer))
                         (lambda (buffer &rest _) buffer)))
                (unwind-protect
                    (progn
                      (org-ext-copy-subtree-as-markdown)
                      (let ((markdown (car kill-ring)))
                        (unless (and
                                 (string-match-p
                                  "^# Create heavy-review command" markdown)
                                 (string-match-p "^## Child$" markdown)
                                 (string-match-p
                                  "Keep this ordinary list item\\." markdown)
                                 (not (string-match-p "State \"" markdown))
                                 (not (string-match-p
                                       "^#+ .*\\_<\\(?:TODO\\|DONE\\|NEXT\\|PROMPT\\)\\_>"
                                       markdown)))
                          (error "Unexpected Markdown: %S" markdown))
                        (princ "reported subtree integration: ok\n")))
                  (when-let ((buffer (get-buffer "*Org MD Export*")))
                    (kill-buffer buffer))))))'
```

Expected: `mdformat: buffer reformatted`, the command success message, and `reported subtree integration: ok`.

- [x] **Step 6: Byte-compile and inspect the final state**

Run the byte-compilation command from Task 1, Step 7, followed by:

```bash
git diff --check
git diff -- org-ext.el org-ext-test.el
git status --short --branch
```

Expected: compilation exits with status 0 and no diagnostic names the changed command or cleanup; the diff has no whitespace errors; no untracked `.elc` appears; and all work remains uncommitted and unpushed.
