# Org Subtree Markdown Clipboard Command

**Status:** Approved corrective design
**Date:** 2026-07-24

## Purpose

`org-ext.el` will provide an interactive command named `org-ext-copy-subtree-as-markdown`. The command will convert the current Org subtree into cleaned, formatted Markdown, place that Markdown on the clipboard, and display it with `pop-to-buffer` in a reusable buffer named `*Org MD Export*`. It will not modify the source buffer.

## Behavior

The command operates from any point within an Org subtree. It temporarily narrows the source buffer to that subtree and disables region export, then invokes Org's Markdown exporter without the `SUBTREEP` option. This preserves the subtree's root headline. A command-local export-options filter runs after ordinary Org option resolution and forces ATX headings, Markdown top-level heading level 1, task inclusion without workflow-keyword rendering, no table of contents, and exclusion of the `LOGBOOK` drawer. Consequently, the root is always emitted as `# Heading`; file-local options cannot restore the table of contents or workflow keywords such as `TODO`, `DONE`, `NEXT`, or `PROMPT`; and task subtrees remain present. Other non-LOGBOOK drawers and established export settings remain in effect.

After export, the command removes Org-generated empty anchor targets of the form `<a id="…"></a>` and standalone state-transition list entries in the standard rendered form `- State "…" from "…"`. The latter cleanup is necessary because an Org state transition recorded outside a `LOGBOOK` drawer is an ordinary list item from the exporter's perspective. The match remains narrow so that ordinary list items survive. Ordinary Markdown links are likewise preserved. The cleaned Markdown is inserted into the standard reusable buffer `*Org MD Export*`, which is cleared at the beginning of every invocation and initialized in `text-mode` following Org's Markdown-export convention.

Within the output buffer, the command invokes `mdformat-buffer` and then calls `kill-new` with the formatted contents. `kill-new` updates the kill ring and, where Emacs has a clipboard integration function, the system clipboard. The command moves point to the beginning of the output and displays it with `pop-to-buffer` only after formatting and clipboard capture succeed.

The Markdown exporter and formatter are loaded on demand through `ox-md` and `mdformat`. Successful completion reports that the formatted Markdown was copied and displayed.

## Failure and State Preservation

Export and formatting errors propagate to the caller. Clipboard mutation occurs only after both operations succeed; consequently, a failed export or formatter invocation leaves the clipboard unchanged. Temporary narrowing is unwound automatically.

The reusable output buffer is cleared before export begins. An export failure therefore leaves it empty. The cleaned Markdown is inserted before formatting, so a formatter failure leaves that unformatted text in the buffer for diagnosis. Failed output is not displayed automatically; the named buffer remains available for manual inspection. A successful output buffer remains live and displayed.

## Verification

Focused ERT tests will exercise the real Org Markdown exporter while substituting a deterministic formatter at the external-tool boundary. They will establish that:

- a nested subtree root becomes an ATX level-one Markdown heading even when user or file-local options request another style or level;
- an active region does not limit the export;
- content outside the selected subtree is excluded;
- table-of-contents output, generated anchor targets, `LOGBOOK` state transitions, and standalone state-transition list entries are absent;
- all workflow keywords are omitted from root and nested headings while the task headings themselves remain;
- the same `*Org MD Export*` buffer is cleared and reused;
- formatting precedes clipboard capture and `pop-to-buffer`;
- the displayed and copied contents are identical;
- the source buffer, point, active region, and restriction remain unchanged;
- export and formatting failures leave the clipboard unchanged; and
- export failure leaves the output buffer empty, while formatter failure retains the cleaned unformatted Markdown.

The completed change will also undergo the existing ERT suite and warning-sensitive byte compilation of `org-ext.el`.

## Alternatives Considered

Calling `org-md-export-as-markdown` would reuse Org's fixed buffer, but it does not provide the required option precedence, cleanup ordering, or clipboard sequencing. Passing `SUBTREEP` directly would be shorter, but Org treats the subtree root as document metadata and can omit it from the Markdown body. Narrowing followed by `org-export-as` therefore provides the requested heading semantics.

A custom derived Markdown backend would provide complete control but introduce unnecessary maintenance. A source-copy hook or parse-tree filter could remove standalone state-transition items before translation, but either would add machinery for an entry whose Markdown representation is fixed and readily distinguished. The design therefore uses Org's native settings after file-local option resolution for headings, workflow keywords, the table of contents, and drawers; a narrow post-export cleanup removes generated anchor tags and only list entries matching the standard `- State "…" from "…"` form.
