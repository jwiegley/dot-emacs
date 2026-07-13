# Migrated Emacs packages — authorship

On 2026-07-07 the 48 git submodules under `~/.emacs.d/lisp/` were removed.
Most are now supplied by the Nix-managed Emacs environment. This file records
their authorship, upstream repositories, and migration revisions in case any
package needs to become a development submodule again.

**`llm-setup` is the only package NOT moved** — it has local changes and stays a
submodule (see `~/.emacs.d/.gitmodules`).

> **Archive note.** The moved working trees were placed in `~/dl/submodules/`,
> but `~/dl` is a symlink to `~/Downloads` (a macOS-managed, auto-cleaned
> folder), and that archive has since been cleared. The repository URLs and
> revisions below reconstruct each listed migration source with
> `git clone <repo> && git checkout <rev>`; as always, a gitlink cannot preserve
> uncommitted changes that may have existed inside a submodule working tree.
> If you keep a local archive again, use a durable location.

For 44 packages, the migration revision equals the final gitlink recorded by
the superproject. Four rows instead record the newer source revision selected
by the Nix migration; the older gitlinks remain recoverable from Git history:

| Package | Final gitlink | Migration rev |
|---------|---------------|---------------|
| `claude-code-ide` | `a9485f766ea6` | `cc508396a09e` |
| `elisp-mcp-dev` | `70933ace320e` | `d70a8f38eded` |
| `gptel` | `33ed0f6f6985` | `ebf0f3d8e993` |
| `mcp-server-lib` | `9e44d6af2e79` | `dec55e640598` |

The current Nix mapping is deliberately not one uniform kind of pin:

- 40 packages have local overlay definitions whose revisions exactly match
  the migration revisions below.
- Seven use the stock package from the flake-locked Nix package set: `async`,
  `format-all`, `erc-yank`, `git-annex`, `mcp`, `nix-update`, and `regex-tool`.
- `use-package` is supplied by Emacs 30 itself, not by a local Nix source
  override.

In the normal Emacs environments, 35 of the former submodules are selected,
four are explicitly excluded, eight retain exact definitions but are not
selected, and `use-package` is bundled as described above.

## Authored by you (36)

Your own packages. The table records migration revisions; 30 have
matching local Nix source pins, five use stock Nix packages, and `use-package`
is bundled with Emacs 30.

| Package | Repo | Migration rev |
|---------|------|---------------|
| `alert` | https://github.com/jwiegley/alert.git | `31fc56855289` |
| `async` | https://github.com/jwiegley/emacs-async.git | `5faab2891660` |
| `ecard` | https://github.com/jwiegley/ecard.git | `e79cd68c4946` |
| `emacs-copy-code` | https://github.com/jwiegley/emacs-copy-code | `0a122d04caab` |
| `emacs-loeb` | https://github.com/jwiegley/emacs-loeb | `5e66a400102e` |
| `emacs-lzw` | https://github.com/jwiegley/emacs-lzw | `27f4c8ed656d` |
| `emacs-pl` | https://github.com/jwiegley/emacs-pl.git | `c5ee5646a49e` |
| `emacs-z3` | https://github.com/jwiegley/emacs-z3 | `ce2d19772ac8` |
| `erc-yank` | https://github.com/jwiegley/erc-yank.git | `55d96f18c5df` |
| `git-annex` | https://github.com/jwiegley/git-annex-el.git | `7f12f0acb254` |
| `git-undo` | https://github.com/jwiegley/git-undo-el.git | `1e94d2dad39f` |
| `gnus-harvest` | https://github.com/jwiegley/gnus-harvest.git | `29b406e1ed5a` |
| `gptel-emacs-tools` | https://github.com/jwiegley/gptel-emacs-tools | `1ae5e496ea7f` |
| `gptel-litellm` | https://github.com/jwiegley/gptel-litellm | `c6b8603816dd` |
| `gptel-prompts` | https://github.com/jwiegley/gptel-prompts.git | `be29a9aa471e` |
| `gptel-rag` | https://github.com/jwiegley/gptel-rag | `eadf31e78ffc` |
| `hash-store` | https://github.com/jwiegley/hash-store | `2074c01f0517` |
| `haskell-config` | https://github.com/jwiegley/haskell-config.git | `9f42695fc99a` |
| `initsplit` | https://github.com/jwiegley/initsplit.git | `e488e8f95661` |
| `machines` | https://github.com/jwiegley/machines | `ba64481bfbe2` |
| `magit-ai` | https://github.com/jwiegley/magit-ai.git | `3f7fce8ebb0f` |
| `nix-update` | https://github.com/jwiegley/nix-update-el.git | `d67f4f7ba8c8` |
| `ob-gptel` | git@github.com:jwiegley/ob-gptel | `71584eb30e83` |
| `org-agenda-overlay` | git@github.com:jwiegley/org-agenda-overlay | `a8e6a0052e91` |
| `org-context` | https://github.com/jwiegley/org-context.git | `de0da4e8f000` |
| `org-devonthink` | https://github.com/jwiegley/org-devonthink | `37314ea676f1` |
| `org-drafts` | git@github.com:jwiegley/org-drafts | `b9302b746fcf` |
| `org-hash` | https://github.com/jwiegley/org-hash.git | `53a7474d93e0` |
| `org-table-loeb` | git@github.com:jwiegley/org-table-loeb.git | `f90f334bfe77` |
| `org-wiki` | git@github.com:jwiegley/org-wiki.git | `1c8f21ef5eed` |
| `pending` | git@github.com:jwiegley/pending.git | `b3192937905b` |
| `regex-tool` | https://github.com/jwiegley/regex-tool.git | `0b4a0111143c` |
| `springboard` | https://github.com/jwiegley/springboard.git | `012c44daa6d4` |
| `stock-quote` | https://github.com/jwiegley/stock-quote | `8e3fc578fcbb` |
| `use-package` | https://github.com/jwiegley/use-package.git | `2f09ce195f86` |
| `vulpea-field` | https://github.com/jwiegley/vulpea-field | `dfb6d9032d77` |

## Third-party (12)

Not written by you — you had these vendored as submodules to track (or fork)
upstream. Ten have matching local Nix source pins; `format-all` and `mcp` use
stock Nix packages.

| Package | Original author | Note | Repo | Migration rev |
|---------|-----------------|------|------|---------------|
| `chess` | Mario Lang (orig.) | maintainer | https://github.com/jwiegley/emacs-chess.git | `e51e89fa2215` |
| `claude-code-ide` | Yoav Orot (manzaltu) | third-party | https://github.com/manzaltu/claude-code-ide.el | `cc508396a09e` |
| `elisp-mcp-dev` | Laurynas Biveinis | third-party | https://github.com/laurynas-biveinis/elisp-mcp-dev.git | `d70a8f38eded` |
| `emacs-format-all-the-code` | Lassi Kortela | third-party | https://github.com/lassik/emacs-format-all-the-code | `0dbe9c70eaf8` |
| `gptel` | Karthik Chikmagalur (karthink) | third-party | https://github.com/karthink/gptel.git | `ebf0f3d8e993` |
| `ledger-mode` | the Ledger project | third-party | git@github.com:ledger/ledger-mode.git | `b43c9d04e030` |
| `llm-tool-collection` | Ad (skissue) | third-party | https://github.com/skissue/llm-tool-collection | `b9fd45bedf3e` |
| `mcp` | lizqwerscott | third-party | https://github.com/lizqwerscott/mcp.el | `2d172809cbdb` |
| `mcp-server-lib` | Laurynas Biveinis | third-party | https://github.com/laurynas-biveinis/mcp-server-lib.el | `dec55e640598` |
| `org-autolist` | Calvin Young | fork | https://github.com/jwiegley/org-autolist.git | `c37e390de487` |
| `vulpea` | Boris Buliga (d12frosted) | fork | https://github.com/jwiegley/vulpea.git | `ea5d6e551115` |
| `wombag` | Karthik Chikmagalur | third-party | https://github.com/karthink/wombag | `62f8e7ae8c8f` |

`gptel` was wiped from `~/.emacs.d/lisp/gptel` and repackaged with Nix on
2026-07-07 (you don't work on it locally anymore). It is pinned in the overlay
to `ebf0f3d` and — importantly — is built as a MELPA package (a `src` override
of the stock `melpaBuild` gptel, **not** `compileEmacsFiles`) so it keeps its
`package.el` version metadata; otherwise `gptel-fn-complete` and other gptel-*
packages that declare `(gptel "0.9.8")` cannot be activated.

## Re-adding one as a submodule

To turn one back into a submodule of `~/.emacs.d` and drop its Nix definition:

```sh
cd ~/.emacs.d
# Example: move `alert` back under lisp/
git submodule add https://github.com/jwiegley/alert.git lisp/alert
git -C lisp/alert checkout 31fc56855289          # the pinned rev above
# then re-add its (use-package … :load-path "lisp/alert") in ~/org/init.org,
# and remove the corresponding Nix selector/source override where one exists
```

The exact `:load-path` lines that were removed are recoverable from this
repository's `init.org` history (the migration commit).
