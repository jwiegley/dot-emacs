# Changelog — `org-llm-wiki.md`

Companion changelog for `/Users/johnw/src/dot-emacs/lisp/docs/org-llm-wiki.md`. Entries are reverse-chronological. Each adversarial-review cycle's findings are summarized in the version that addressed them; *outstanding* findings live in the parent doc's status note at the top.

---

## v2.3c — deep-review reconciliation

An eight-dimension multi-agent deep review (spike internals, dependency-API verification against installed sources, init.org compatibility-matrix verification, doc consistency, concept fidelity, mutation-side soundness, security, performance — every finding adversarially verified) produced 29 confirmed findings. v2.3c applies all of them to the doc; the spike was fixed in the same pass.

**Doc-internal contradictions resolved:**

- **Appendix B identity** restated property-only. The schema template — the operative contract the agent reads — still carried the three-conjunct rule v2.3a abolished; an agent obeying it would refuse exactly the drifted-node reads §2.1 guarantees.
- **Appendix C / §7.0 unified**: Appendix C recommended `mcp-server-lib-with-error-handling` (the rewrap bug §7.0 forbids, spike-verified) and `:server-id "org-wiki"` (Option β) while §7.0 recommends Option α `"default"`. Everything now states Option α and the spike's clause-ordered error macro. The §13 failure-table row no longer claims namespace isolation the design doesn't have.
- **§8.2 / Appendix C search snippets** no longer pre-filter candidates by `org-wiki-root` path prefix — that silently re-introduced path into read identity. Candidate enumeration is corpus-wide (wiki tree ∪ roam-DB nodes with `:WIKI_KIND:`), and §2.1 now states this implementation consequence (plus the mirror-image stray-property privacy cost).
- **Appendix A** no longer annotates `#+filetags:` as a "tags-local query target".

**Claims corrected against reality:**

- **Hash coverage (new 🔴 in §9)**: with the real config's `org-hash-recursive nil`, the entry hash stops at the first `**` subheading — where all §4 body content lives — so body edits do not change the node hash. Three reconciliation options listed; decision required before the mutation slice. New §3.4 matrix row; "Merkle" framing removed from §1.2/§1.3/Appendix D.
- **§9.2**: the wiki dir-local `org-hash-update-on-save nil` upgraded from "optional belt-and-braces" to **required** — it is the only mechanism closing the non-RPC-save laundering path.
- **§9** now headlines that all integrity mechanisms are tamper-*evidence*, not tamper-*prevention*.
- **§10.1/§13 degraded mode**: org-ql-semantic signals `user-error` on backend failure rather than degrading; `wiki_search` must catch and fall back to text matching itself (the spike now does).
- **§13.4**: the "10-minute RPC timeout" had no substrate (mcp-server-lib dispatch is synchronous, no timeout primitive); replaced with the honest mechanism set — `C-g` through `unwind-protect`, timestamped stale-sentinel cleanup (`org-wiki-lock-stale-seconds`), and crash-time `wiki_recover`.
- **§7.0/Appendix C ported to `mcp-server-lib-register-server`** (per-tool `register-tool` is obsolete as of 0.3.0); `:description` must be a hand-written summary, never `(documentation handler)`. Stale mcp-server-lib line-number citations replaced with symbolic references.
- **§3.4 matrix**: exclude-regexp count corrected (8 entries); capture key `w` is *taken* (Work prefix), not free; the Nix-installed `elisp-dev-mcp` package registers its own endpoint when enabled — clients must connect to the endpoint wiki tools use.
- **§7.1**: `wiki_node_metadata` strips any `HASH_*` property unconditionally; noted that `wiki_read_node` returns the drawer by design (integrity rests on tool-only hash writes, not secrecy).
- **§13 injection row**: wiki bodies replayed at query time must be delimited by the prompt-assembly layer, not only raw sources at ingest.
- **§3.5**: `MIND_MAP.org` explicitly in the writable set (structured RPCs for narrative; `wiki_sync` for its dblocks).

**New §14 v1 recommendation**: build the minimal mutation slice (allowlist + git + lint-time drift detection + file-per-node blast radius) before the WAL/sentinel/plan-apply machinery — the concept-fidelity review's conclusion was that the likeliest failure mode of the full transactional design is not corruption but an empty wiki.

Spike updated in the same pass (now 21 tests): ranking-preserving semantic search with `:sort` and text fallback via `condition-case`; corpus-wide candidate files via the roam DB; org-id refresh throttled (`org-wiki-id-refresh-interval`) closing the rescan-per-miss DoS; reads reuse buffers and delay mode hooks; unconditional `HASH_*` strip in metadata; structured `org-wiki-error` → JSON tool-error mapping (no more `internal_error` flattening, no paths in payloads); registration ported to `register-server` with hand-written descriptions; k parsing clamped.

---

## v2.3b — Karpathy-spirit recovery

A deep comparison of the doc against Karpathy's original Teachers Tech walkthrough and `MIND_MAP.md` gist surfaced *tonal* and *emphasis* drift: the doc had become substantively faithful to Karpathy's three-layer architecture while drifting away from his *philosophy* of casual evolution, demo-first persuasion, and human ergonomics. v2.3b applies six small edits to recover what the architectural rigor had crowded out, without sacrificing the rigor itself.

- **§1.5 "What using the wiki feels like"** (new). Three concrete scenarios — adding a source, asking a question, seeing the synthesis — written from the human's perspective rather than the agent's. The cross-source query (Karpathy's killer demo: "food + temples → which neighborhood") is now in §1, not buried in §8.2. Karpathy's "you focus on what goes in and what questions to ask" framing is explicit.
- **§3.1 adds `wiki/MIND_MAP.org`** to the canonical directory layout. Karpathy's gist version centers on a single hub document the agent maintains; the doc previously dispersed this into `wiki/indices/`. `MIND_MAP.org` is the *human-readable* hub (top-to-bottom narrative + auto-generated dynamic blocks); indices remain for queries.
- **§11.5 "The graph view as a first-class complement"** (new). Karpathy spends real screen time on Obsidian's graph view as a way to *see* the synthesis compounding. `org-roam-ui` is the Org-side equivalent (already in the user's package inventory) but had been mentioned only in passing. §11.5 elevates it: indices for queries, graph for seeing.
- **Appendix B preface** acknowledges the schema template is a starter, meant to evolve as the wiki grows. Karpathy's iteration ethos — "the schema evolves as the wiki grows" — is now explicit at the top of the template rather than implicit.
- **§7 divergence acknowledgment**. The doc takes a much more structured approach than Karpathy's "agent writes markdown directly" model; v2.3b adds a callout that names this divergence, explains why it's deliberate (the user's stakes are higher than Karpathy's disposable demo), and notes that direct-write Karpathy-style operation is a perfectly reasonable alternative for low-stakes contexts (e.g., a scratch wiki). The cost-benefit is now on the page.
- **§13.1 reframe**. The 10K+ node scaling planning is now flagged at the top as deferred work — read once, forget about it until the wiki actually feels slow. Karpathy's "personal scale ~100 articles" framing is honored: Phase 0 needs none of this.

Net effect: the doc still has the rigor that four adversarial cycles produced, but the *aesthetic* moves back toward Karpathy's casual-and-evolving original. The implementation discipline serves the human, not the other way around.

---

## v2.3a — identity refinement (property-only)

Follow-up to v2.3 in response to user clarification: the v2.0 reframe to "tagged subgraph" was meant to make `:WIKI_KIND:` the *single* identity criterion, but v2.0–v2.2 left §2.1 over-determined as a three-conjunct rule (property + filetag + path). v2.3a simplifies:

- **Identity is property-only.** A node is a wiki node iff it has `:WIKI_KIND:`. The `~/org/wiki/` directory and `:wiki:` filetag are placement *conventions*, not identity criteria. Wiki nodes that drift outside the canonical directory remain valid for reads.
- **The write-allowlist (§3.5) is the *only* place path matters.** Mutating tools refuse to edit files outside `~/org/wiki/` even when they have `:WIKI_KIND:`. This protects against stray-property mutation without restricting the search surface.
- **The validator's role changes**: §7.5 now emits *warnings* (not errors) for nodes that drift from convention (have `:WIKI_KIND:` but aren't under `~/org/wiki/` or lack `:wiki:` filetag). Drift is fine until you try to mutate something at risk.

Spike package updated to match:

- `org-wiki-node-p` is now property-only; verified by spike test `org-wiki-test-node-p-true-outside-wiki-root` (formerly `…-false-outside-…`).
- New `org-wiki-writable-p` predicate gates the future mutation slice; verified by `org-wiki-test-writable-p-false-outside-wiki-root`.
- 19 ERT tests pass (1 added, 1 inverted).

---

## v2.3 — empirical grounding via the read-only spike

Not a patch round responding to a fifth adversarial review. The fourth review concluded the cycle of doc-only iteration had hit diminishing returns; what was needed was running code. v2.3 is the doc revision that:

- **Adds section-status badges** (🟢 / 🟡 / 🔴) so the doc honestly signals what's spec-quality versus what needs empirical verification before implementation.
- **Anchors verified claims** to a real working package: the Nix-installed `org-wiki` package is a read-only MCP spike that empirically validates the load-bearing assumptions of the design. Sections with the `✓ verified by spike` annotation have been confirmed against running code on the user's actual Emacs install.

Sections promoted from "claimed correct" to "empirically verified" by the spike's 18 ERT tests:

- **§2.1 / Appendix D** — `(property "WIKI_KIND")` identity predicate matches by existence, not value. Test `org-wiki-test-property-predicate-matches-existence`.
- **§4.1** — `(org-hash-property)` accessor returns `"HASH_sha512_256"` for the default algorithm; lowercase-suffix variant is the form `org-hash` actually writes. Test `org-wiki-test-hash-property-name-when-loaded`.
- **§7.0** — `mcp-server-lib-register-tool`'s positional-first / keyword-rest signature works as documented; multi-positional-arg defuns produce schemas with all parameters typed as `"string"`; `MCP Parameters:` docstring blocks parse correctly. Tests `org-wiki-test-mcp-register-tool-accepts-multi-arg`, `org-wiki-test-mcp-schema-from-docstring`.
- **§7.0 error-handling pattern** — clause order matters. `mcp-server-lib-tool-error` inherits from `user-error` from `error`; a generic `(error ...)` clause placed before the specific `(mcp-server-lib-tool-error ...)` clause silently absorbs structured errors. The spike's `org-wiki-mcp--with-error-handling` macro orders clauses correctly. Tests `org-wiki-test-tool-error-survives-rewrap-pattern`, `org-wiki-test-with-error-handling-preserves-tool-error`, `org-wiki-test-with-error-handling-converts-generic-error`. §7.0 now emphasizes "CLAUSE ORDER MATTERS" with a side-by-side example.

Sections that the spike does **not** validate (mutation-side) remain 🔴: §7.6, §7.6.1, §9.4, §13.3, §13.4, Appendix C body. These require a subsequent mutation-side spike before further doc iteration.

The doc itself remains v2.2 in content for the mutation-side prose; v2.3 is a confidence overlay, not a rewrite. CHANGES.md and the in-doc status note + badges are the visible diff.

---

## v2.2 — patches the third adversarial pass

In-place patch over v2.1 applying every finding from the third adversarial pass.

- **WAL recovery rewritten** (§7.5 `wiki_recover` + §7.6 step 13 + §13.3 journal schema). The journal now records absolute `file_path` per row (so recovery doesn't depend on `org-id-locations` being consistent with corrupted property drawers); on `after_hash` match the recovery replays steps 10–12 (DB update, embedding-queue enqueue, commit-row append) — previously it only appended the journal row, silently desyncing the roam DB and embedding queue; the journal-corruption and missing-backup failure modes are now explicitly handled.
- **Transaction discipline wrapped in `unwind-protect`** (§7.6 step 1) — without this, Elisp errors in steps 2–12 would leak the sentinel forever. Lock-release path now guaranteed.
- **Hash precondition branched for create paths** (§7.6). Tools come in `mutate-existing` (run precondition) and `create-fresh` flavors (skip precondition; instead assert no existing file/`:ID:` at the target). Closes the bug where `wiki_create_node_apply` would have rejected every node creation because new nodes have no stored hash.
- **Sentinel lock honesty** (§7.6 step 1 + §13.4). The sentinel coordinates *RPC against RPC* only — `save-buffer` does not consult it. v2.1's claim that "the RPC's file lock blocks `save-buffer`" was false. The doc now defines an `org-wiki-mode` minor mode with a buffer-local `before-save-hook` guard that surfaces an error to the user when a sentinel exists.
- **Dir-locals story deleted** (§7.6 step 9 + §9.4). The v2.1 suppression of `org-roam-ext-pre-save-hook` via `dir-locals.el` was both broken (dir-locals can't gracefully remove items from list-valued hooks without trip-wiring the "unsafe local variable" prompt) AND unnecessary — verified that `org-roam-ext-pre-save-hook`'s revise-title only fires for paths matching `meeting|bahai|positron|git-ai` (`org-roam-ext.el` lines 283–296); `wiki/` is not in that pattern. §9.4 now documents the `org-wiki-mode` minor mode as the future-proof seam if the pattern is ever widened.
- **Option B race fixed** (§5.3). The `org-attach-attach-file` call now uses the path returned by `vulpea-create` in its `vulpea-note` struct (`(vulpea-note-path note)`), not `(org-id-goto id)`. `org-id-locations` is updated lazily; a just-created node's ID may not be registered, causing `org-id-goto` to fail or trigger a full corpus rescan. Also explicitly calls `org-id-add-location` and `org-roam-db-update-file` after attach.
- **MCP namespace honesty** (§7.0). The doc acknowledges that `mcp-server-lib`'s `:server-id` is a *separate logical endpoint*, not an in-connection namespace — tools registered under `"org-wiki"` are invisible to clients connecting via `"default"`. Documents Option α (shared `"default"` endpoint with `wiki_`-prefixed ids) and Option β (separate `"org-wiki"` endpoint client must connect to). Default recommendation: Option α.
- **MCP error-signaling reworked** (§7.0). `mcp-server-lib-with-error-handling` catches and re-wraps `mcp-server-lib-tool-throw` errors, corrupting structured JSON. The doc now uses a small `org-wiki-mcp--throw` helper that `signal`s `'mcp-server-lib-tool-error` directly, plus a narrow `condition-case` on `'error` for unexpected Lisp errors.
- **MCP schema-type honesty** (§7.0). Every auto-generated schema arg is `"string"` (verified `mcp-server-lib.el` lines 323–340). Tools that conceptually take arrays, diffs, or objects receive a *JSON-encoded string* and parse it themselves. The doc says so explicitly so tool authors don't expect richer JSON-schema types.
- **Element-cache reset** (§7.6.1). Position-based edits bypass `org-element-cache`'s tracking, so subsequent `org-element-at-point` calls in the same transaction may return stale ASTs (and with `org-element-cache-persistent` true on Emacs 29+, the corruption can survive into the next session). The mutation example now calls `(org-element-cache-reset)` after the batch.
- **`wiki_lint_run --schema-changed` defined** (§7.5). Added `schema_changed` parameter that ignores cached `:LAST_LINTED:` and re-validates the whole corpus against the new `CLAUDE.md`. v2.1 referenced this flag without defining it.
- **Hash property literal eliminated** (§4.1). All docs and examples now use lowercase `:HASH_sha512_256:` (matching what `(format "HASH_%s" 'sha512_256)` actually produces) and instruct code to always go through `(org-hash-property)` rather than hardcoding any string.
- **Sandbox-story coherence** (§3.5.1 ↔ §13 failure table). The §13 row for "LLM writes outside allowlist" now defers to §3.5.1, naming MCP path-prefix checks + tool-inventory restriction as the *primary* defense, and OS perms + git hooks as defense-in-depth against honest mistakes only. v2.1 had §3.5.1 honest but §13 still treating chmod as primary.
- **`(user-data ...)` portability** (§7.6 step 4). The doc now says the wiki module defines its own fallback (`(or (and (fboundp 'user-data) (user-data path)) (expand-file-name path (locate-user-emacs-file "org-wiki/")))`) so contributors who don't have the user's helper still get sensible defaults.

---

## v2.1 — patches the v2.0 adversarial review

In-place patch over v2.0 applying every critical and high finding from the v2.0 adversarial review.

- **Identity predicate** switched from `(tags-local "wiki")` to `(property "WIKI_KIND")` everywhere (§2.1, §3.4, §10.3, §11.1, §11.2, Appendix C) — verified against `org-ql`'s own test suite that `tags-local` excludes file-level `#+filetags:` and `tags` honors the user's allow-list (which doesn't include `:wiki:`).
- **Hash property name corrected.** `org-hash` writes `HASH_<algo>` (algorithm-suffixed via `(format "HASH_%s" org-hash-algorithm)`), not `HASH`. §4 adds a normative shorthand note; property-drawer examples updated; implementation guidance everywhere uses `(org-hash-property)` accessor.
- **`org-hash-confirm` precondition added.** §7.6 step 2 verifies a stored hash *exists* before calling `(org-hash-confirm nil nil t)` with `raise-error`, closing the "no stored hash → silent nil → bypass" gap.
- **`(secure-hash 'sha256 path)` byte-hash bug fixed.** §5.1 and Appendix C now use the file-bytes form `(with-temp-buffer (set-buffer-multibyte nil) (insert-file-contents-literally path) (secure-hash 'sha256 (current-buffer)))`. Earlier form hashed the path string.
- **MCP `register-tool` signature corrected.** Handler is the *positional first* argument, then keyword properties. Handlers must be 0-arg or N-positional-arg (no `&rest`); each positional becomes a JSON-schema field; `MCP Parameters:` docstring block uses 2–4 space indent for `name - desc`. Appendix C signatures rewritten as multi-positional defuns returning `json-encode`'d strings.
- **`lock-file` replaced with sentinel-file pattern** (`write-region ... 'excl`) because `lock-file` raises an interactive prompt that would freeze MCP.
- **Synchronous `org db embed --prune` removed** from `wiki_archive_apply`: now enqueues a high-priority prune; in-process `org-ql-semantic--cache` cleared immediately; `wiki_search` filters `:ARCHIVED: t` at result time until the queue drains.
- **Journal upgraded to write-ahead log.** Each mutating RPC writes a `pending` row before mutation and a `committed` row after verified save. §13.3 spells out the schema; §7.6 step 13 explains recovery.
- **§3.5.1 rewritten** with honesty about `claude-code-ide --dangerously-skip-permissions`: same-user OS permissions and git pre-commit hooks catch *honest* mistakes, not adversarial ones. The *only* effective defense is restricting the agent's tool inventory (no shell, no general write, no third-party filesystem MCP). `chmod 0555` on directories (was incorrectly `0444`).
- **§4.3 / §3.4 keyword list inconsistency fixed.** The user's primary TODO sequence is restored to `DRAFT → TODO → DOING → WAIT → DEFER → TASK → HABIT → APPT → DONE/CANCELED/PASS`.
- **§5.3 Option B rewritten** with the correct API: `org-attach-attach-file` (programmatic) called at the source-record's heading. Earlier draft cited `org-attach-attach-set`, which is not a real function. ID-keyed sharding (per `org-attach-id-uuid-folder-format`), not byte-hash-keyed.
- **§7.6.1 mutation example fixed.** `org-id-find` with non-nil second arg returns a marker, not a filename — the example now uses `(gethash id org-id-locations)` for file lookup, then verifies `:ID:` at the entry.
- **§9.4 rename-suppression mechanism corrected.** `org-roam-ext-do-not-delete` controls transcript-file deletion, not pre-save renaming.
- **Async dblock regeneration.** §11.1 adds a scaling-caveat subsection. `org-update-all-dblocks` runs synchronously on the main thread; for corpora beyond ~1K wiki nodes, run regenerations in a child Emacs via `async-start` or materialize hot indices once daily via cron.
- **Embedding-queue back-pressure** specifies soft-cap (`wiki_sync` warns) and hard-cap (mutating RPCs refuse) limits (§10.1).
- **`vulpea-create` partial-failure recovery** — §13 adds an explicit failure-mode row and remediation.
- **`org db embed` degraded mode** — §10.1 specifies the fallback to title/byte-offset matching in `org-ql-semantic` when the backend is unreachable.
- **`wiki_recover` added** to §7.5 maintenance tools; auto-runs from `org-wiki-mcp-enable` on stale-lock detection.
- **`(user-data "...")` annotated** as a user-specific helper from init.org (not a standard Emacs function).
- **Status note added** at the top of the document: snippets are verified pseudocode, not implementation. APIs were checked against the installed `mcp-server-lib`, `org-hash`, `org-attach`, and `org-ql` sources, but readers must still re-check live docstrings before shipping.

---

## v2.0 — major restructure

Major restructure from v1.1.

**Headline change**: the wiki is reframed as a *tagged subgraph* of the existing single roam DB (your `org-roam-directory` is `~/org/`), not as a separate roam root. The wiki coexists with all other corpus content and is identified by `:wiki:` filetag + `:WIKI_KIND:` property + `wiki/` path, queried via `(property "WIKI_KIND")`.

Other significant changes:

- An `org-attach`-based raw-storage option (Option B).
- A Compatibility Matrix (§3.4) mapping every relevant init.org variable to its wiki implication.
- Explicit MCP integration with the already-running server (§7.0).
- Idempotency keys + dry-run/apply pairs on every mutating tool (§7.3).
- A Vulpea-first API stance (Appendix C, §7.6).
- A canonical Hook Ordering sequence (§9.4) with explicit `org-hash--inhibit-on-save` discipline to prevent on-save hash laundering.
- A TODO-keyword mapping (§4.3) onto your non-standard `org-todo-keywords` (DRAFT/WAIT/SCRAP/QUOTE/PROMPT...).
- Explicit acknowledgment of `claude-code-ide --dangerously-skip-permissions` and what that requires from the sandbox layers (§3.5.1).
- §10 grounded in your real configured pgvector + bge-m3 backend.
- §13.4 acknowledging unresolved concurrent-edit problems.
- Deterministic Phase 1 lint delegated to `org-lint` where redundant (§8.3).
- `org-id-find` replaced with `gethash`-on-`org-id-locations` for hot-path validation (§7.6).
- Explicit `org-roam-db-update-file` per-RPC since your config has `org-roam-db-update-on-save = nil` (§7.6).
- `secure-hash` not `hash-store` for `:RAW_ID:` (§5.1).
- Filename-collision suffix on sub-minute creates (§3.3).
- Backups/journal paths under `user-data` (§13.3).

**Prior art added** (§1.4): Karpathy's MIND_MAP.md gist; `jkitchin/org-db-v3`; `jkitchin/emacs-rag-libsql`; `yibie/org-supertag`; Obsidian's Agent Client plugin.

---

## v1.1 — initial published draft

First published architecture. Incorporated feedback from the initial Phase-4 / Phase-5 forge cycle: hook-ordering with `org-hash--inhibit-on-save` (subsequently revised in v2.1+), structured-edit MCP surface, explicit failure-mode table, scale + multi-machine sections, transaction journal, deterministic-then-LLM lint, async embedding refresh, `wiki/frozen/` discipline.

(v1.0 existed only briefly as the initial outline before the first review pass; v1.1 was the first integrated draft.)

---

*The document itself, like the wiki, evolves — treat this changelog the way you'd treat a project's git log: it records what shifted and why, not the current state.*
