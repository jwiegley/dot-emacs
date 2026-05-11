# org-indicators — design & implementation notes

A view-only feature in `org-indicators.el` that decorates Org headlines
(both in buffers and in the agenda) with a small fixed-width block of
indicator letters showing which properties an entry has.

## Final design at a glance

Four indicators, each a Unicode small-cap letter (width 1, text-height):

| Glyph | Symbol  | Meaning                                                      |
|-------|---------|--------------------------------------------------------------|
| `ꜰ`   | file    | attachment present (ATTACH tag or `org-attach-dir` exists)   |
| `ᴜ`   | url     | `URL` property set                                           |
| `ɴ`   | note    | body text under heading, OR log notes in LOGBOOK             |
| `ᴛ`   | timelog | CLOCK entries exist in the subtree                           |

Glyphs are joined by single spaces. The block always has the same width
(7 cols for 4 indicators) — slots whose type doesn't apply render as a
space, so the block aligns vertically across rows.

The block's right edge is anchored at
`(tag-end-col - org-indicators-tag-margin)`, so on headlines whose
tags right-align to the same column, all blocks sit at the same column
regardless of how wide each row's tag string is.

## Usage

```elisp
(require 'org-indicators)

;; In Org buffers — buffer-local minor mode
M-x org-indicators-mode
;; or auto-enable
(add-hook 'org-mode-hook #'org-indicators-mode)

;; In agenda — finalize hook
(add-hook 'org-agenda-finalize-hook #'org-indicators-apply-agenda)
;; refresh agenda with `g` to re-apply
```

## Customization

| Variable / face                | Purpose                                                                 |
|--------------------------------|-------------------------------------------------------------------------|
| `org-indicators-chars`         | Alist of `(symbol . string)` — change the glyph for any indicator       |
| `org-indicators-types`         | Which indicators to show, and in what slot order                        |
| `org-indicators-tag-margin`    | Columns reserved for tags (default 14); larger ⇒ block further left     |
| `org-indicators` (face)        | Defaults to bold `font-lock-keyword-face` — change for different look   |

## Architecture

### Public surface

- `org-indicators-mode` — buffer-local minor mode (autoloaded). When
  enabled in an Org buffer, registers a jit-lock fontification function
  and renders indicators in the visible region.
- `org-indicators-apply-agenda` — finalize hook for `*Org Agenda*`
  buffers. Walks each line, looks up `org-hd-marker`/`org-marker`, reads
  the indicators from the source headline, and paints them on the
  agenda line.

### Internal pipeline

1. `org-indicators--at-point` — detection, runs on a headline and
   returns a list of symbols (subset of `org-indicators-types`).
2. `org-indicators--block` — builds the fixed-width glyph string,
   with absent slots rendered as spaces and the present ones faced.
3. `org-indicators--apply-on-line` — places the overlay on the
   current line. Two branches:
   - **with tags** — overlay the alignment whitespace with a `display`
     property; the display string positions the block at the desired
     column.
   - **no tags** — zero-length overlay with `after-string`, padded
     leading spaces so the block falls at the same column it would on
     tagged rows.
4. `org-indicators--fontify` — jit-lock entry point; walks heading
   regex matches in the range, wraps each call in `condition-case` so a
   single bad heading doesn't disable fontification for the buffer.

### Detection helpers

- `org-indicators--has-attachment-p` — `ATTACH` tag (local only) or
  `org-attach-dir` returns a real directory.
- `org-indicators--heading-has-body-p` — skips planning line and all
  drawers, checks for any non-blank content before the next heading.
- `org-indicators--has-log-entries-p` — finds the LOGBOOK drawer,
  checks for `- ` items inside it (state changes, captured notes).
- `org-indicators--has-clock-entries-p` — `^[ \t]*CLOCK:` anywhere in
  the subtree.

The `note` indicator OR's together "has body" and "has log entries", so
a heading whose only content is log notes still shows `ɴ`.

## Bugs hit during implementation (and what they taught)

These are the non-obvious gotchas I learned the hard way — worth
recording for future feature additions.

### 1. `re-search-backward` with greedy quantifiers picks the rightmost match

Original regex:

```
\\([ \t]+\\):\\(?:[[:alnum:]_@#%]+:\\)+[ \t]*$
```

Searching backward from EOL, the regex engine accepts the *rightmost*
start position where the regex matches. That meant group 1 captured
only the single space immediately before `:tag:`, not all 30+ spaces of
alignment whitespace. The display function got `padding-width = 1`,
correctly returned `nil`, and *no overlay was ever applied*.

**Fix:** anchor with `[^ \t\n]` at the start, forcing the match to
begin at the end of the title text — the greedy whitespace group then
spans the full alignment padding.

```
[^ \t\n]\\([ \t]+\\):\\(?:[[:alnum:]_@#%]+:\\)+[ \t]*$
```

### 2. Errors in jit-lock functions can disable font-lock

The user reported the mode "overwriting org-mode itself" — almost
certainly the cascade from (1). When a jit-lock callback errors,
jit-lock can stop calling it for the buffer, which kills syntax
highlighting for the whole org buffer until the buffer is reopened.

**Fix:** wrap each per-heading call in `condition-case`. A single bad
heading no longer poisons the whole buffer.

### 3. Zero-length overlays with `evaporate t` self-delete immediately

For the no-tags branch I used `(make-overlay pos pos)` plus
`after-string` to append glyphs after the title. I initially set
`evaporate t` on this overlay, copying the with-tags branch.

`evaporate` deletes overlays whose length becomes zero — *and a
zero-length overlay is already at zero length*, so it was getting
deleted instantly on the next overlay-related operation.

**Fix:** drop `evaporate` from the no-tags overlay. Keep it on the
with-tags overlay (where the overlay covers real whitespace and is
non-empty).

### 4. `overlays-in` excludes empty overlays unless END = point-max

This isn't a bug in my code — it's a test-harness gotcha. When
verifying that the no-tags overlay was being created, my test used
`(overlays-in (line-beginning-position) (line-end-position))` and saw
nothing. The overlay was at the EOL position, but `(overlays-in BEG
END)` includes empty overlays "at END" only when END denotes
end-of-buffer. The overlay was real and rendered correctly in
interactive Emacs; my test was just blind to it.

**Lesson:** when querying for empty overlays at line boundaries, use
`overlays-at` or extend the search past the newline.

### 5. Emoji glyph widths vary in Emacs

When picking default glyphs, I tried emojis. Most are width 2
(`📎🔗📝📔`), but a few are width 1 in Emacs's default rendering even
with VS16 (`⏱`, `⏱️`). Mixing widths in a single block breaks
alignment.

Even after settling on all-width-2 emoji (e.g. `⏰`), the user pointed
out that emoji height is taller than a regular character cell, which
also disrupts visual rhythm.

**Fix:** switched to Unicode small-cap letters (`ꜰ ᴜ ɴ ʟ ᴛ`). These
are text-style glyphs — width 1, text-height — so they fit cleanly in
a character cell. Bolded via the `org-indicators` face to stand out.

### 6. Indicator block "moves" when tag-string length varies

First alignment scheme placed the block flush with the tag string
(`<block> <one-space> <tags>`). The tag column was preserved per-row,
but the block's column varied across rows because tag-string lengths
vary:

```
Title text                                          ɴ     :Call:
Title text                                          ɴ :Call:LINK:
```

Visually, the `ɴ`s sit at different columns.

**Fix:** anchor the block's right edge to a column derived from
`tag-end-col` (which is constant under right-alignment) minus
`org-indicators-tag-margin`. The trailing whitespace between block
and tags grows or shrinks; the block column stays fixed. Falls back to
flush placement if the tag string is wider than the margin.

## Layout math

For a line whose:

- title content ends at column `T` (`title-end-col`)
- trailing tag string occupies columns `S..E` (`tag-start-col` ..
  `tag-end-col`)
- block width is `W`
- margin is `M` (= `org-indicators-tag-margin`)

Then:

- desired block right-edge column: `desired = E - M`
- latest legal right-edge: `max-end = S - 2` (leaves one space before
  tags)
- actual right-edge: `min(desired, max-end)`
- block start column: `right-edge - W + 1`
- if `block-start < T`, skip (title doesn't leave room)
- otherwise the `display` string is
  `[T..block-start) spaces | block | (right-edge..S) spaces`,
  total width = `S - T` = the padding-width, so tags stay where Org
  put them.

For the no-tags branch, `E` is approximated as
`(abs org-tags-column)` so the block lines up with where tags *would*
be on a tagged line.

## Why overlays (not text properties)

Two reasons:

1. **Non-destructive.** Buffer text is untouched. Saving the file, ediff,
   `M-x untabify`, etc. all see the underlying whitespace, not the glyphs.
2. **Agenda compatibility.** The agenda buffer is regenerated on every
   refresh, but we can paint overlays on it without affecting the
   regeneration. A text property would be either wiped or have to be
   re-applied during fontification.

The trade-off is overlay management (creating, finding, deleting), but
the helpers `org-indicators--remove` / `org-indicators--apply-on-line`
keep this contained.

## Files

- `org-indicators.el` — implementation
- `org-indicators.elc` — byte-compiled version

## Reload after changes

```elisp
M-x load-library RET org-indicators RET
;; toggle the mode off and back on to refresh visible overlays:
M-x org-indicators-mode  M-x org-indicators-mode
;; or simply `g` in the agenda
```
