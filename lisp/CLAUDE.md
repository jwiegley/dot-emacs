# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This is John Wiegley's Emacs Lisp personal configuration repository. It contains local configuration modules plus a small number of retained project directories. Most package dependencies that once lived here as git submodules are now supplied by the Nix-managed Emacs environment; `SUBMODULE-AUTHORSHIP.md` at the repository root records that migration.

## Key Packages and Modules

The repository contains several major components:

- **Core Modules**: Individual `.el` files in the root directory (e.g., `cl-info.el`, `org-config.el`, `gptel-presets.el`)
- **Retained Subdirectories**: `badi-calendar/` and the sole remaining git submodule, `llm-setup/`
- **Nix-managed Dependencies**: External packages such as GPTel, Org extensions, and MCP libraries are installed by Nix rather than checked out below `lisp/`
- **MCP Integration**: Local adapters such as `mcp-convert.el` and `anvil-ext.el`; the legacy `mcp-server-lib` configuration is currently disabled
- **Org-mode Extensions**: Various org-mode enhancements (`org-roam-ext.el`, `org-ql-ext.el`, `org-smart-capture.el`)

## Emacs Lisp Development Patterns

### Code Organization

**Lexical Binding** - All modern packages use lexical binding:
```elisp
;;; package-name.el --- Description -*- lexical-binding: t; -*-
```

**File Structure** - Standard Elisp package layout:
```elisp
;;; package-name.el --- Brief description -*- lexical-binding: t; -*-

;; Package metadata (Author, Version, Package-Requires, URL, Keywords)

;;; Commentary:
;; Detailed usage documentation

;;; Code:

(require 'dependencies)

(defgroup package-name nil ...)
(defcustom package-name-option t ...)

;;;###autoload
(defun package-name-command () ...)

(defun package-name--helper () ...)  ; Internal functions use --

(provide 'package-name)
;;; package-name.el ends here
```

**Namespace Conventions**:
- Public API: `package-name-function`
- Private/internal: `package-name--internal` (double dash)
- Predicates: `package-name-enabled-p` (ends with -p)
- Modes: `package-name-mode` (ends with -mode)
- Hooks: `package-name-mode-hook` (ends with -hook)

### Autoloads

Interactive commands and mode definitions use autoload cookies:
```elisp
;;;###autoload
(defun org-smart-capture ()
  "Smart capture entry point."
  (interactive)
  ...)

;;;###autoload
(define-derived-mode my-mode text-mode "MyMode"
  "A custom major mode."
  ...)
```

Generate autoloads only from a package's own source checkout, using the build
system documented there. The local single-file modules in this directory are
loaded by `init.org` and do not share a generated package-autoloads file.

### Dependencies and Loading

**Package Headers** specify dependencies:
```elisp
;; Package-Requires: ((emacs "27.1") (dash "2.19") (s "1.12"))
```

**Require Statements** for runtime dependencies:
```elisp
(require 'cl-lib)      ; Use cl-lib, not deprecated cl package
(require 'subr-x)      ; For string-trim, thread-first, etc.
(require 'seq)         ; For modern sequence operations
```

**Optional Features** use autoloads or eval-after-load:
```elisp
(with-eval-after-load 'org
  (add-hook 'org-mode-hook #'my-package-setup))
```

## Development Commands

### Building and Compilation

The former Eask, Make, and Cask package trees are not repository-local
development targets anymore. For a Nix-managed dependency, work in its
upstream checkout or the source pinned by the Nix overlay and use that
project's own commands. For `llm-setup`, enter the retained submodule and
follow its `CLAUDE.md` and `flake.nix`.

### Byte Compilation

**Individual files**:
```bash
emacs -batch -f batch-byte-compile file.el
```

**Check for warnings**:
```bash
emacs -batch -L . -f batch-byte-compile file.el 2>&1 | grep -i warning
```

**Batch compilation** (for multiple files):
```bash
emacs -batch -L . -f batch-byte-compile *.el
```

### Testing Workflows

**ERT Tests** - Test file naming:
- `*-test.el` or `*-tests.el` (e.g., `mcp-server-lib-test.el`)
- Located in package root or `test/` subdirectory

**Run tests interactively**:
```elisp
;; Load test file
(load-file "path/to/test-file.el")

;; Run all tests
(ert t)

;; Run specific test
(ert "test-name-regexp")

;; Run tests matching pattern
(ert 'tag)

;; Batch mode
(ert-run-tests-batch-and-exit)
```

## Interactive Development

### REPL-driven Development

**Evaluate expressions** during development:
```elisp
;; Eval last sexp: C-x C-e
;; Eval defun: C-M-x
;; Eval buffer: M-x eval-buffer
;; Eval region: M-x eval-region
```

**Reload package** after changes:
```elisp
;; Unload feature first to clear old definitions
(unload-feature 'package-name t)

;; Load updated version
(load-file "package-name.el")
```

**Interactive debugging**:
```elisp
;; Set debug-on-error globally
(setq debug-on-error t)

;; Debug specific function
(debug-on-entry 'function-name)
(cancel-debug-on-entry 'function-name)

;; Insert debugging breakpoint
(defun my-function (arg)
  (debug)  ; Will trigger debugger here
  ...)

;; Trace function calls
(trace-function 'function-name)
(untrace-function 'function-name)
```

### Development Helpers

**Check function definitions**:
```elisp
;; Find function definition
(find-function 'function-name)

;; Describe function
(describe-function 'function-name)

;; Show function documentation
(documentation 'function-name)
```

**Macro expansion**:
```elisp
;; Expand macro once
(macroexpand-1 '(macro-call args))

;; Fully expand macro
(macroexpand-all '(macro-call args))

;; Interactive macro expansion
(pp-macroexpand-last-sexp)
```

**Performance profiling**:
```elisp
;; Profile function
(elp-instrument-function 'function-name)
(elp-results)
(elp-restore-all)

;; Benchmark code
(benchmark-run 1000
  (function-to-test))
```

## Architecture and Code Organization

### Package Structure
- Most repository-local code is a single `.el` module.
- `badi-calendar/` is a retained local tree; `llm-setup/` is the sole remaining git submodule and has its own guidance.
- External package sources are Nix-managed and should not be assumed to exist below `lisp/`.

### MCP (Model Context Protocol) Integration
The repository includes extensive MCP integration:
- `mcp-convert.el`: local MCP conversion utilities
- `anvil-ext.el`: local Anvil compatibility and endpoint configuration
- `mcp-server-lib` and `elisp-dev-mcp`: Nix definitions retained, but excluded from the normal environment and `COMMENT`-disabled in `init.org`

### GPTel Integration
Significant AI/LLM integration through the `gptel` package:
- `gptel`: Nix-installed upstream package
- `gptel-presets.el`, `gptel-ext.el`: Configuration and extensions
- `gptel-backends.el`, `gptel-tools.el`: Backend and tool configuration
- Prompt files in the repository-root `prompts/` directory

### Org-mode Ecosystem
Rich org-mode configuration and extensions:
- `org-config.el`: Main org configuration (48KB)
- `org-roam-ext.el`: Org-roam extensions
- `org-smart-capture.el`: Enhanced capture templates
- `org-context`, `org-hash`, `org-drafts`: Nix-installed packages, with local extension modules where present

## Testing Strategy

When modifying packages:
1. Check for existing test files (`*-test.el`)
2. Run package-specific tests using the appropriate tool (Eask, Make, or Cask)
3. Ensure byte-compilation succeeds without warnings
4. For a Nix-managed package, run its checks in the source checkout that owns its build metadata
5. Test interactively with `M-x ert` for immediate feedback

## Common Development Tasks

### Creating a New Package

1. Create package file with proper header:
```elisp
;;; package-name.el --- Description -*- lexical-binding: t; -*-

;; Copyright (C) 2025 Author Name

;; Author: Author Name <email>
;; Version: 0.1.0
;; Package-Requires: ((emacs "27.1"))
;; Keywords: keywords
;; URL: https://github.com/user/package-name

;;; Commentary:
;;; Code:

(defgroup package-name nil
  "Group documentation."
  :group 'applications
  :prefix "package-name-")

(provide 'package-name)
;;; package-name.el ends here
```

2. Create test file `package-name-test.el`:
```elisp
;;; package-name-test.el --- Tests -*- lexical-binding: t; -*-

(require 'ert)
(require 'package-name)

(ert-deftest package-name-test-basic ()
  "Test basic functionality."
  (should (equal expected actual)))

(provide 'package-name-test)
;;; package-name-test.el ends here
```

3. Create build configuration (Eask recommended):
```elisp
;; Eask
(package "package-name" "0.1.0" "Description")
(author "Name" "email")
(license "GPL-3.0")
(package-file "package-name.el")
(script "test" "eask test ert package-name-test.el")
(depends-on "emacs" "27.1")
```

### Debugging Common Issues

**Package not loading**:
- Check `(provide 'package-name)` matches filename
- Verify `load-path` includes package directory
- Check for circular dependencies

**Void variable errors**:
- Ensure `defvar`/`defcustom` before use
- Check for typos in variable names
- Verify lexical vs dynamic scope

**Byte-compilation warnings**:
- Fix all warnings - they indicate real issues
- Use `cl-lib` functions, not deprecated `cl`
- Declare functions from other packages: `(declare-function fn "file")`

**Test failures**:
- Run tests interactively to see full error output
- Use `should-error` for expected errors
- Check test isolation - tests should not depend on each other

## Important Notes

- This is a personal configuration repository with active development
- Many packages are maintained by John Wiegley and other contributors
- Some packages have their own upstream repositories (e.g., `use-package`, `async`)
- The repository uses Git for version control with regular commits
- Byte-compiled files (`.elc`) are tracked in the repository
- Always test changes interactively before committing
