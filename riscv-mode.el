;;; riscv-mode.el --- Major-mode for RISC V assembly
;;
;; Copyright (C) 2016 Adam Niederer
;;
;; Author: Adam Niederer <https://github.com/AdamNiederer>
;; Maintainer: Adam Niederer
;; Created: September 29, 2016
;; Version: 0.1
;; Keywords: riscv assembly
;; Package-Requires: ((emacs "24.4"))
;; Homepage: https://github.com/AdamNiederer/riscv-mode
;;
;; This file is not part of GNU Emacs.
;;
;; This file is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation; either version 3, or (at your option)
;; any later version.

;; This file is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;;; Commentary:
;;
;; riscv-mode provides syntax highlighting, code execution with spike, and
;; syntactic indentation
;;
;;; Code:

(require 'thingatpt)

(defgroup riscv nil
  "Major mode for editing RISC V assembly"
  :prefix "riscv-"
  :group 'languages
  :link '(url-link :tag "Github" "https://github.com/AdamNiederer/riscv-mode")
  :link '(emacs-commentary-link :tag "Commentary" "riscv-mode"))

(defconst riscv-registers
  "\\bzero\\|ra\\|[sgtf]p\\|f?s1[01]\\|f?s[0-9]\\|t[0-6]\\|f?a[0-7]\\|ft[0-9]\\|ft1[01]")

(defconst riscv-keywords
  '("lui" "auipc"
    "jal" "jalr"
    "beq" "bne" "blt" "bge" "bltu" "bgeu"
    "lh" "lb" "lw" "lbu" "lhu"
    "sb" "sh" "sw"
    "add" "sub"
    "addi"
    "sll" "slt" "sltu" "xor" "srl" "sra" "or" "and"
    "slti" "sltiu" "xori" "ori" "andi" "slli" "srli" "srai"
    "fence" "fence.i"
    "scall" "sbreak" "ecall" "ebreak"
    "rdcycle" "rdcycleh" "rdtime" "rdtimeh" "rdinstret" "rdinstreth"
    "lwu" "ld" "sd"
    "addiw" "slliw" "srliw" "sraiw" "adw" "subw" "sllw" "srlw" "sraw"
    "mul" "mulh" "mulhsu" "mulhu" "div" "divu" "rem" "remu"
    "mulw" "divw" "divuw" "remw" "remuw"
    ;; Atomics
    "lr.w" "sc.w" "amoswapw" "amoadd.w" "amoxor.w" "amoand.w" "amoor.w"
    "amomin.w" "amomax.w" "amominu.w" "amomaxu.w"
    "lr.d" "sc.d" "amosdapd" "amoadd.d" "amoxor.d" "amoand.d" "amoor.d"
    "amomin.d" "amomax.d" "amominu.d" "amomaxu.d"
    ;; Floating point
    "flw" "fsw" "fmadd.s" "fmsub.s" "fnmsub.s" "fnmadd.s"
    "fadd.s" "fsub.s" "fmul.s" "fdiv.s" "fsqrt.s"
    "fsgnj.s" "fsnjn.s" "fsnjx.s"
    "fmin.s" "fmax.s" "fcvt.w.s" "fcvt.wu.s" "fmv.x.s"
    "feq.s" "flt.s" "fle.s"
    "fclass.s" "fcvt.s.w" "fcvt.s.wu" "fmv.s.x"
    "frcsr" "frrm" "frflags" "fscsr" "fsrm" "fsflags" "fsrmi" "fsflagsi"
    "fcvt.l.s" "fcvt.l.u.s" "fcvt.s.l" "fcvt.s.lu"
    ;; Double Precision
    "fld" "fsd" "fmadd.d" "fmsub.d" "fnmsub.d" "fnmadd.d"
    "fadd.d" "fsub.d" "fmul.d" "fdiv.d" "fsqrt.d"
    "fsgnj.d" "fsnjn.d" "fsnjx.d"
    "fmin.d" "fmax.d" "fcvt.w.d" "fcvt.wu.d" "fmv.x.d"
    "feq.d" "flt.d" "fle.d"
    "fclass.d" "fcvt.d.w" "fcvt.d.wu" "fmv.d.x"
    "frcsr" "frrm" "frflags" "fscsr" "fsrm" "fsflags" "fsrmi" "fsflagsi"
    "fcvt.l.d" "fcvt.l.u.d" "fcvt.d.l" "fcvt.d.lu"
    "fmv.d.x"
    ;; Pseudoinstructions
    "nop"
    "la" "li"
    "lb" "lh" "lw" "ld"
    "sb" "sh" "sw" "sd"
    "flw" "fld"
    "fsw" "fsd"
    "mv"
    "not" "neg" "negw"
    "sext"
    "seqz" "snez" "sltz" "sgtz"
    "fmv.s" "fmv.d"
    "fabs.s" "fabs.d"
    "fneg.s" "fneg.d"
    "beqz" "bnez" "blez" "bgez" "btlz" "bgtz"
    "j" "jal" "jr" "jalr" "ret" "call" "tail"))

(defconst riscv-defs
  '(".align"
    ".ascii"
    ".asciiz"
    ".byte"
    ".data"
    ".double"
    ".extern"
    ".float"
    ".globl"
    ".half"
    ".kdata"
    ".ktext"
    ".space"
    ".text"
    ".word"))

(defconst riscv-font-lock-keywords
  `((("\\_<-?[0-9]+\\>" . font-lock-constant-face)
     ("\"\\.\\*\\?" . font-lock-string-face)
     ("[A-z][A-z0-9_]*:" . font-lock-function-name-face)
     (,(regexp-opt riscv-keywords) . font-lock-keyword-face)
     (,(regexp-opt riscv-defs) . font-lock-preprocessor-face)
     (,riscv-registers . font-lock-type-face))))

(defcustom riscv-tab-width tab-width
  "Width of a tab for RISCV mode"
  :tag "Tab width"
  :group 'riscv
  :type 'integer)

(defcustom riscv-interpreter "spike"
  "Interpreter to run riscv code in"
  :tag "RISCV Interpreter"
  :group 'riscv
  :type 'string)

(defvar riscv-mode-map
  (let ((map (make-keymap)))
    (define-key map (kbd "<backtab>") 'riscv-dedent)
    (define-key map (kbd "C-c C-c") 'riscv-run-buffer)
    (define-key map (kbd "C-c C-r") 'riscv-run-region)
    (define-key map (kbd "C-c C-l") 'riscv-goto-label-at-cursor)
    map)
  "Keymap for riscv-mode")

(defun riscv--interpreter-buffer-name ()
  "Return a buffer name for the preferred riscv interpreter"
  (format "*%s*" riscv-interpreter))

(defun riscv--get-indent-level (&optional line)
  "Returns the number of spaces indenting the last label."
  (interactive)
  (- (save-excursion
       (goto-line (or line (line-number-at-pos)))
       (back-to-indentation)
       (current-column))
     (save-excursion
       (goto-line (or line (line-number-at-pos)))
       (beginning-of-line)
       (current-column))))

(defun riscv--last-label-line ()
  "Returns the line of the last label"
  (save-excursion
    (previous-line)
    (end-of-line)
    (re-search-backward "^[ \t]*\\w+:")
    (line-number-at-pos)))

(defun riscv-indent ()
  (interactive)
  (indent-line-to (+ riscv-tab-width
                     (riscv--get-indent-level (riscv--last-label-line)))))

(defun riscv-dedent ()
  (interactive)
  (indent-line-to (- (riscv--get-indent-level) riscv-tab-width)))

(defun riscv-run-buffer ()
  "Run the current buffer in a riscv interpreter, and display the output in another window"
  (interactive)
  (let ((tmp-file (format "/tmp/riscv-%s" (file-name-base))))
    (write-region (point-min) (point-max) tmp-file nil nil nil nil)
    (riscv-run-file tmp-file)
    (delete-file tmp-file)))

(defun riscv-run-region ()
  "Run the current region in a riscv interpreter, and display the output in another window"
  (interactive)
  (let ((tmp-file (format "/tmp/riscv-%s" (file-name-base))))
    (write-region (region-beginning) (region-end) tmp-file nil nil nil nil)
    (riscv-run-file tmp-file)
    (delete-file tmp-file)))

(defun riscv-run-file (&optional filename)
  "Run the file in a riscv interpreter, and display the output in another window.
The interpreter will open filename. If filename is nil, it will open the current
buffer's file"
  (interactive)
  (let ((file (or filename (buffer-file-name))))
    (when (buffer-live-p (get-buffer (riscv--interpreter-buffer-name)))
      (kill-buffer (riscv--interpreter-buffer-name)))
    (start-process riscv-interpreter
                   (riscv--interpreter-buffer-name)
                   riscv-interpreter file))
  (switch-to-buffer-other-window (riscv--interpreter-buffer-name))
  (read-only-mode t)
  (help-mode))

(defun riscv-goto-label (&optional label)
  (interactive)
  (let ((label (or label (read-minibuffer "Go to Label: "))))
    (beginning-of-buffer)
    (re-search-forward (format "[ \t]*%s:" label))))

(defun riscv-goto-label-at-cursor ()
  (interactive)
  (riscv-goto-label (word-at-point)))

;;;###autoload
(define-derived-mode riscv-mode prog-mode "RISC V"
  "Major mode for editing RISC V assembly."
  (font-lock-add-keywords nil riscv-font-lock-keywords)
  (setq tab-width riscv-tab-width)
  (setq indent-line-function 'riscv-indent)
  (modify-syntax-entry ?# "< b" riscv-mode-syntax-table)
  (modify-syntax-entry ?\n "> b" riscv-mode-syntax-table))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.riscv\\'" . riscv-mode))

(provide 'riscv-mode)
;;; riscv-mode.el ends here
