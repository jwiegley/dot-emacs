# org-ext.el Improvement Specification

Source: maintainer audit (2026-07) of `lisp/org-ext.el` against Org checkout
`~/db/org-mode` @ `3c855d51a` (`10.0-pre`), 33 confirmed findings
(1 S1, 11 S2, 11 S3, 10 S4), independently fact-checked.

## 1. Problem statement

`org-ext.el` (2,061 lines, ~90 commands layered over Org) carries 33
confirmed defects: one data-loss path, eleven destructive-or-wrong behaviors,
eleven bounded defects, and ten minor/latent ones. Several are on daily-use
paths (recording import, capture finalization, agenda bulk commands, todoize,
link editing). Existing coverage (`org-ext-test.el`, 6 tests) exercises only
recording import and Markdown copy; none of the 33 findings has a regression
test.

## 2. Goals

- Eliminate all 33 findings; each fix lands with an ERT regression test that
  fails without the fix.
- Preserve every existing key binding, command name, and documented
  user-facing behavior unless a finding explicitly corrects it.
- Keep compatibility with both the Nix-loaded Org version and the
  `~/db/org-mode` checkout (`10.0-pre`).

## 3. Non-goals

- Refactoring, renaming, splitting, or re-architecting `org-ext.el`.
- Auditing external packages (`org-ql`, `org-roam`, Vulpea, Gnus, OSM,
  mdformat) beyond what a finding requires.
- Performance benchmarking as a deliverable (findings 25–26 are fixed on
  mechanism, not measured latency).
- Live interactive-Emacs validation (batch ERT only).

## 4. Open decisions (defaults applied unless overridden)

| # | Decision | Default |
|---|----------|---------|
| D1 | Org baseline for API contracts | Code must be correct against the Org version loaded by the Nix Emacs **and** `~/db/org-mode` @ HEAD; where they differ, code to the older API. |
| D2 | Inbox destination for finding 13 (`todo.org` vs `drafts.org`) | Unify on `drafts.org` via a `file+function` capture target; interactive `org-ext-goto-inbox` displays the same buffer it positions. |
| D3 | Finding 33 drawer-prefix direction | Match the docstring and upstream: prefix hides drawers, no prefix shows them (swap branches). |

## 5. Constraints

- All fixes in `lisp/org-ext.el`; tests in `lisp/org-ext-test.el`.
- Use Org's public API over regexps where a finding's fix direction names it
  (`org-get-property-block`, `org-with-wide-buffer`, `org-link-make-string`,
  `org-agenda-files`).
- After all changes: re-byte-compile `org-ext.el` and commit the refreshed
  `org-ext.elc` (repo tracks it; a live session may load the stale `.elc`).
- Quality gates per story and at completion (§9).

## 6. Remediation stories

Ordered; each story is independently committable. Findings retain their audit
numbers. Every finding row lists: location → fix → regression test.

### Story A — Data safety (S1 + destructive paths)

| F | Sev | Location | Fix | Test |
|---|-----|----------|-----|------|
| 1 | S1 | `org-ext.el:291-308` | Save destination successfully before deleting any draft source; consume sources only after acknowledged write. | Stub save to signal → draft source remains, inbox not marked complete. |
| 2 | S2 | `:1341-1356` | Copy subtree retaining source, paste, delete marked source only after paste succeeds. | Read-only destination → error leaves source byte-identical. |
| 12 | S2 | `:1986-1998` + unnarrowed capture (`org-config.el:1003-1020`) | Restrict whitespace cleanup to capture begin/end markers. | Capture into file with pre-existing trailing whitespace/NBSP → bytes outside capture markers unchanged. |
| 16 | S3 | `:420-459` | Return nil unless ordered, line-anchored drawer bounds exist (prefer `org-get-property-block`); start all-buffer pass at `point-min`. | No drawer = no-op; drawer-like text in example block untouched; invoke from final heading fixes all. |

### Story B — Recording/import pipeline

| F | Sev | Location | Fix | Test |
|---|-----|----------|-----|------|
| 4 | S2 | `:160-173` | If name after stripping `.txt` already ends in a supported audio extension, test it directly. | `x.m4a.txt` + `x.m4a` adjacent → audio moved. |
| 25 | S4 | `:222-229`, `:248-273`, `:281-308` | Collect hashes once, insert all unique notes, save once, then write receipts/consume sources. | Three notes → one scan/save; injected failure still retries. |
| 14 | S3 | `:1203-1288` | Ambiguous one-word capitalized line = content unless name established and nonempty content follows. | Authored message, one-word continuation (`Thanks`), following message all preserved. |

### Story C — Agenda commands and inbox navigation

| F | Sev | Location | Fix | Test |
|---|-----|----------|-----|------|
| 3 | S2 | `:1885-1941` | Snapshot source markers, apply noninteractive worker to all, `org-agenda-redo` once after loop; register bulk actions if marks intended. | Two region-selected and two bulk-marked entries → both sources change, one redraw. |
| 13 | S3 | `:60-95` | Per D2: single destination, `file+function` target, locator operates on selected widened buffer. | Navigation and capture land in same buffer, incl. initially-narrowed case. |
| 33 | S4 | `:328-349` | Swap prefix branches (D3). | Prefix hides, no prefix shows. |

### Story D — Metadata, todoize, and properties

| F | Sev | Location | Fix | Test |
|---|-----|----------|-----|------|
| 5 | S2 | `:1543-1551` | Validate `(car org-stored-links)` before todoize; use `cadr` (or `org-link-make-string`); nil → `user-error`, no mutation. | Exact URL/description round-trip; empty state signals without changing entry. |
| 6 | S2 | `:461-469` | Parse and validate leading `YYYYMMDD` from `buffer-file-name`. | Mocked today ≠ filename date → filename date inserted. |
| 17 | S3 | `:485-501`, `:1943-1984` | Invoke ID worker explicitly with `arg` before nullary capture hooks (`org-id-get-create` FORCE). | `C-u` on existing ID → changes; no prefix → unchanged. |
| 19 | S3 | `:1478-1495`, `:1569-1577` | Return `(float-time)` when no timestamp property exists (no `(debug)`). | Timestamp-free DONE entry sorts without debugger. |
| 29 | S4 | `:612-621` | Handle nil, `t`, list, and regexp forms of `org-use-property-inheritance` explicitly when adding `WITH`. | Exercise all four representations. |
| 30 | S4 | `:647-655` | Require successful `org-up-heading-safe`; extract priority cookie only when present (letter-or-nil contract). | Top-level → nil; cookie-less parent → nil; `[#A]` parent → `A`. |
| 31 | S4 | `:1633-1642` | Cons current state only after successful ascent. | Top-level TODO → nil; one TODO parent → one keyword, no dup. |

### Story E — Outline structure predicates and chaining

| F | Sev | Location | Fix | Test |
|---|-----|----------|-----|------|
| 7 | S2 | `:677-694` | Recurse with `(org-ext--first-child-todo pred)`. | Matching/nonmatching TODO at multiple depths. |
| 8 | S2 | `:719-730` | Ascend through non-TODO headings to nearest TODO ancestor before ordering. | `Project → Category → First/Second` → only First qualifies. |
| 9 | S2 | `:823-869` | Carry separate previous-ID; apply before replacing. | A/B/C → B→A, C→B, no self-cycles. |
| 22 | S3 | `:1771-1827` | Accept whitespace or end-of-string after contact group in split. | Contact on empty title, then set verb → `(Alice) Read:`. |
| 28 | S4 | `:2016-2026` | Derive choices from Org's normalized TODO key data; support flat syntax and nonalphabetic selectors. | Current nested syntax, legacy flat, `TODO(1)` selector. |

### Story F — Link handling

| F | Sev | Location | Fix | Test |
|---|-----|----------|-----|------|
| 10 | S2 | `:872-886` | Collect source link markers before opening any link. | Two Emacs file links in one subtree → both opened once. |
| 11 | S2 | `:985-1008` | Bound searches to `(line-end-position)`. | Invoke above a later matching link → buffer unchanged. |
| 18 | S3 | `:1433-1442` | Interactive region bounds; literal `replace-match` (`t t`); fall back to group 1 when no description. | Region-only replacement; `[[R&D]]` desc → `R&D`; bare `[[URL]]` → `URL`. |
| 23 | S3 | `:1456-1462` | After removing parameter: `org-link-make-regexps` + `org-element-update-syntax`. | Add/remove unique type → neither params nor parser recognize it. |
| 24 | S4 | `:1444-1448` | Accept `(tag arg)` and use `arg` (drop deprecated one-arg form). | Interactive and programmatic opens, with/without `(4)`. |

### Story G — Hooks, scans, and display

| F | Sev | Location | Fix | Test |
|---|-----|----------|-----|------|
| 15 | S3 | `:1406-1431` | `goto-char (point-min)` inside `save-excursion` before scanning. | Refresh from `point-max` → all rows bound. |
| 20 | S3 | `:1594-1606` | `goto-char (point-min)` before Quill pass (or one combined scan). | Quill refs before and after VER ref all linked. |
| 21 | S3 | `:1644-1659` | Inspect bounded three buffer chars before point; read language only when backward search succeeds; clear match-data risk. | 1–2 initial backticks no-op; no earlier block + stale match data → no stale language. |
| 26 | S4 | `:1666-1724`, `:1829-1841` | Stable pure action returning values; dedupe/count afterward. | Unchanged repeat query → headings traversed once. |
| 27 | S4 | `:361-383`, `:657-660` | Use `(org-agenda-files)` and `string=` comparisons. | List-file string, directory entry, `copy-sequence`d excluded path. |
| 32 | S4 | `:1727-1746` | Bind `inhibit-read-only` while rebuilding summary buffer. | Invoke twice → both summaries produced. |

## 7. Cross-cutting checks folded into fixes

These came from the earlier single-agent review and are covered by the fixes
above or verified during implementation; confirm none survives:

- `org-ext-agenda-show` narrowing/window restoration (`:312-326`) — use
  `org-with-wide-buffer` discipline or indirect buffer; verify selected-window
  restoration under error.
- `org-ext-current-tags` heading regexp `^\*+\s-+` escape loss (`:1617-1631`).
- `post-self-insert-hook` per-keystroke `recent-keys` cost (`:1644-1664`) —
  the finding-21 fix (bounded char inspection) removes it.
- Synchronous `CoreLocationCLI` in capture finalization (`:1960-1984`) —
  bounded timeout/cache or async; not one of the 33 but on the same hook path
  as finding 17/19 work.

## 8. Acceptance criteria

1. All 33 findings fixed per §6; each has an ERT test failing pre-fix.
2. `org-ext-test.el` suite passes in batch against the Nix Emacs and, where
   loadable, against `~/db/org-mode` checkout.
3. Byte-compilation of `org-ext.el` exits 0 with no new warnings.
4. `check-parens` and `git diff --check` clean.
5. Refreshed `org-ext.elc` committed alongside source.
6. No command renamed, no binding in `init.org` invalidated, no behavior
   changed beyond what a finding's row states.

## 9. Verification commands (per story and final)

```bash
# Locate the Nix Emacs binary (plain `emacs` is not on PATH in batch shells)
EMACS=$(ls /nix/store/*emacs*/bin/emacs 2>/dev/null | head -1)

# Test suite
"$EMACS" --batch -L lisp -L ~/db/org-mode/lisp \
  -l lisp/org-ext-test.el -f ert-run-tests-batch-and-exit

# Byte-compile + parens
"$EMACS" --batch -L lisp -f batch-byte-compile lisp/org-ext.el
"$EMACS" --batch lisp/org-ext.el --eval '(check-parens)'

git diff --check
```

## 10. Suggested execution order

A (data safety) → D (metadata/todoize, touches daily capture) → C (agenda) →
B (recordings) → E (structure) → F (links) → G (hooks/display).
Stories are independent; reorder freely, but land A first.
