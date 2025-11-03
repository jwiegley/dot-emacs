# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Repository Overview

This is John Wiegley's Emacs Lisp personal configuration and packages repository. It contains custom Emacs modules, packages, and configurations organized as a collection of independent Elisp projects.

## Key Packages and Modules

The repository contains several major components:

- **Core Modules**: Individual `.el` files in the root directory (e.g., `cl-info.el`, `org-config.el`, `gptel-presets.el`)
- **Packages with Subdirectories**: Larger packages with their own structure (e.g., `chess/`, `use-package/`, `async/`, `gptel/`)
- **MCP Integration**: Model Context Protocol server library (`mcp-server-lib/`) and related tools
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

Generate autoloads with:
```bash
make autoloads  # For packages with Makefiles
eask generate autoloads  # For Eask-based packages
```

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

For packages using **Eask** (e.g., `mcp-server-lib`, `async`, `elisp-mcp-dev`):
```bash
# Install dependencies and compile
eask install-deps
eask compile

# Run tests
eask test ert <test-file.el>

# Run custom scripts (defined in Eask file)
eask run test
eask run org-lint
```

For packages using **Make** (e.g., `use-package`, `async`, `vulpea`):
```bash
# Compile elisp files
make elc

# Run tests
make test

# Interactive testing
make test-interactive

# Clean compiled files
make clean

# Generate autoloads
make autoloads
```

For packages using **Cask** (e.g., `chess`):
```bash
cask install
cask exec ert-runner
```

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

**Test patterns in this repo**:
```elisp
;; mcp-server-lib uses custom test helpers
(require 'mcp-server-lib-ert)
(setq mcp-server-lib-ert-server-id "test-server")

;; Tests use defconst for test data
(defconst my-test--data "test value"
  "Test data documentation.")

;; Use regexp matchers for output
(should (string-match-p expected-regexp actual))
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
- Each major package is self-contained in its own directory
- Packages may have their own `CLAUDE.md`, `README.org`, and build configuration
- Many packages use Eask for modern Elisp project management

### MCP (Model Context Protocol) Integration
The repository includes extensive MCP integration:
- `mcp-server-lib/`: Core MCP server library for Elisp
- `mcp-convert.el`: MCP conversion utilities
- `elisp-mcp-dev/`: Development tools for MCP in Elisp
- `mcp/`: Additional MCP-related functionality

### GPTel Integration
Significant AI/LLM integration through the `gptel` package:
- `gptel/`: Main GPTel package
- `gptel-presets.el`, `gptel-ext.el`: Configuration and extensions
- `gptel-claude-oauth.el`: Claude-specific authentication
- Various prompt management in `gptel-prompts/`

### Org-mode Ecosystem
Rich org-mode configuration and extensions:
- `org-config.el`: Main org configuration (48KB)
- `org-roam-ext.el`: Org-roam extensions
- `org-smart-capture.el`: Enhanced capture templates
- `org-context/`, `org-hash/`, `org-drafts/`: Additional org packages

## Testing Strategy

When modifying packages:
1. Check for existing test files (`*-test.el`)
2. Run package-specific tests using the appropriate tool (Eask, Make, or Cask)
3. Ensure byte-compilation succeeds without warnings
4. For packages with Eask, use `eask test` command
5. For packages with Makefiles, use `make test` and `make test-interactive`
6. Test interactively with `M-x ert` for immediate feedback

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
