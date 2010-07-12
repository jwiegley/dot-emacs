;; easm.el --- Assembler for Emacs' bytecode interpreter
;;
;; Copyright 2010  Helmut Eller <eller.helmut@gmail.com>.
;;
;; Version: 0.1 (2010-Jun-27)
;;
;; This program is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.
;;
;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.
;;
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.
;;
;;; Commentary:
;;
;; A simple assembler for Emacs' bytecode interpreter.
;; Example:
;;
;;   (easm '(x) '((varref x) (return))) => #[(x) "‡" [x] 1]
;;
;; The first argument to `easm' ist the arglist of the function and
;; the second argument is a list of symbolic instructions.  The
;; assembler turns the symbolic instructions into an executable
;; function.  The assembler needs to create a bytevector of
;; instructions, the constant-pool and compute the stack frame size.
;;
;; I haven't found much of a specification for the instructions but
;; src/bytecode.c is quite readable in case you can't guess the
;; meaning from instruction names.  The disassembler is the quickest
;; way to see what instructions are most useful and how to use them.
;;
;; The ELisp byte-compiler allegedly creates LAP code before
;; assembling but it seemed too intermingled with the rest of the
;; compiler to be useful as standalone assembler.  So I wrote my own.
;;
;; Unfortunately the instruction set is very limited.  About the only
;; thing that you can do more efficiently in this assembly code than
;; in compiled Lisp are loops and possibly state machines.
;;
;;; Code:


(eval-when-compile
  (require 'cl))

(defstruct easm-instruction
  name	     ; name of the instruction e.g.: byte-varref
  code 	     ; bytecode
  effect     ; stack effect = <#pushed> - <#popped>
  )

;; map our symbolic names easm-instruction.
(defvar easm-instructions
  (let ((tab (make-hash-table :test 'eq)))
    (loop for code from 0
	  for name across byte-code-vector
	  when name do
	  (let* ((string (symbol-name name))
		 (key (intern (substring string (length "byte-"))))
		 (effect (aref byte-stack+-info code))
		 (instr (make-easm-instruction :name name :code code
					       :effect effect)))
	    (assert (string-match "^byte-" string))
	    (puthash key instr tab)))
    tab))

(defun easm-lookup (name &optional noerror)
  "Return the easm-instruction for the symbol NAME."
  (cond ((gethash name easm-instructions))
	(noerror)
	(t (error "Unkown instruction: %S" name))))


;; used to gather various information; lots of in-situ updating going on.
(defstruct easm-context
  instructions ; list of symbol instructions
  constants    ; an alist ((<value> . (<instructions using it> ...)))
  labels       ; an alist ((<name> <pc> . (<instructions using it> ...)))
  code	       ; assembled bytevector
  )

;; Add (KEY . (VALUE)) to ALIST; if KEY is already present merge VALUE
;; to the present list.
(defun easm-alist-add (alist key value)
  (let* ((probe (assoc key alist)))
    (cond (probe
	   (push value (cdr probe))
	   alist)
	  (t (cons (cons key (list value)) alist)))))

;; Iterate over the list of symbolic instructions collecting
;; information about constants and labels.
(defun easm-scan (ctx)
  (let ((constants '())
	(labels '()))
    (dolist (i (easm-context-instructions ctx))
      (case (car i)
	((constant varref varbind varset)
	 (setq constants (easm-alist-add constants (cadr i) i)))
	((goto goto-if-nil goto-if-not-nil
	       goto-if-nil-else-pop goto-if-not-nil-else-pop)
	 (setq labels (easm-alist-add labels (cadr i) i)))))
    (setf (easm-context-constants ctx) constants)
    (dolist (l labels)
      (push nil (cdr l)))
    (setf (easm-context-labels ctx) labels)))

;; Choose and order for the objects in the constant-pool and backpatch
;; the symbolic instructions with the corresponding index.  Objects
;; which are referenced in more places receive smaller indexes.
(defun easm-assign-constants (ctx)
  (let ((alist (easm-context-constants ctx)))
    (setq alist (sort alist (lambda (c1 c2)
			      (> (length (cdr c1))
				 (length (cdr c2))))))
    (setf (easm-context-constants ctx) alist)
    (loop for i from 0
	  for (c . patchlist) in alist do
	  (dolist (inst patchlist)
	    (setf (cadr inst) i)))))

;; map symbolic instruction names to a emitter functions.
(defvar easm-emitters (make-hash-table :test 'eq))

;; Define an emitter function.  The function receives the easm-context
;; and the symbolic instruction as argument.  It should emit
;; the corresponding bytecode.
(defmacro* easm-define-emitters ((&rest instructions) &body body)
  (declare (indent 1))
  `(let ((fun (lambda (ctx instruction)
		(macrolet ((pc () '(1- (point)))
			   (name () '(car instruction))
			   (arg0 () '(cadr instruction)))
		  . ,body))))
     (dolist (i ',instructions)
       (puthash i fun easm-emitters))))

(easm-define-emitters (goto goto-if-nil goto-if-not-nil
			    goto-if-nil-else-pop goto-if-not-nil-else-pop)
  (easm-emit-opcode (name))
  (easm-emit-uint16 0)			; will be backpatched
  (setf (cadr instruction) (- (pc) 2))	; store pc for backpatching
  )

(easm-define-emitters (varref varbind varset call unbind)
  (let ((base (easm-instruction-code (easm-lookup (name)))))
    (cond ((<= (arg0) 5)
	   (easm-emit (+ base (arg0))))
	  ((<= (arg0) 255)
	   (easm-emit (+ base 6))
	   (easm-emit (arg0)))
	  (t
	   (easm-emit (+ base 7))
	   (easm-emit-uint16 (arg0))))))

(easm-define-emitters (constant)
  (cond ((< (arg0) byte-constant-limit)
	 (easm-emit (+ byte-constant (arg0))))
	(t
	 (easm-emit byte-constant2)
	 (easm-emit-uint16 (arg0)))))

(easm-define-emitters (listN concatN insertN)
  (easm-emit-opcode (name))
  (easm-emit (arg0)))

(easm-define-emitters (label)
  (let ((probe (assoc (cadr instruction) (easm-context-labels ctx))))
    (cond (probe (setf (cadr probe) (pc)))
	  (t (message "Unused label: %S" (cadr instruction))))))

;; create a unibyte buffer to hold the emitted code
(defmacro easm-with-code-buffer (&rest body)
  (declare (indent 0))
  `(with-temp-buffer
     (set-buffer-multibyte nil)
     (buffer-disable-undo)
     . ,body))

;; emit a single byte
(defun easm-emit (byte)
  (assert (typep byte '(integer 0 255)))
  (insert byte))

;; emit a 2bytes for a unsinged integer
(defun easm-emit-uint16 (uint16)
  (assert (typep uint16 '(integer 0 65535)))
  (easm-emit (logand uint16 255))
  (easm-emit (ash uint16 -8)))

;; emit the opcode for the instruction with name NAME.
(defun easm-emit-opcode (name)
  (let ((inst (easm-lookup name)))
    (cond (inst (easm-emit (easm-instruction-code inst)))
	  (t (error "Unknown opcode: %S" name)))))

;; update the bytevector at index I and I+1 with UINT16.
(defun easm-patch (bytevector i uint16)
  (assert (typep uint16 '(integer 0 65535)))
  (aset bytevector i (logand uint16 255))
  (aset bytevector (1+ i) (ash uint16 -8)))

;; emit bytecode to a buffer.  PC-offsets for labels not known at the
;; beginning and are backpatched at the end.
(defun easm-build-codevector (ctx)
  (easm-with-code-buffer
    (dolist (i (easm-context-instructions ctx))
      (let* ((name (car i))
	     (emitter (gethash name easm-emitters)))
	(cond (emitter
	       (funcall emitter ctx i))
	      (t
	       (easm-emit-opcode name)))))
    (setf (easm-context-code ctx) (buffer-string)))
  (let ((code (easm-context-code ctx)))
    (loop for (label pc . patchlist) in (easm-context-labels ctx) do
	  (when (not pc)
	    (error "Undefined label: %S" label))
	  (dolist (i patchlist)
	    (easm-patch code (cadr i) pc)))))


;; state for the stack analyzer
(defstruct easm-stack-state
  bytevector	; instruction sequence
  worklist	; list of (pc . depth) places that we need to visit
  max		; the maximum depth so far
  seen		; an array to mark visited pc-offsets: visited
					;  offsets contain the depth; unvisited elements nil.
  )

;; map opcodes to stack analyzer functions
(defvar easm-stack-analyzers (make-hash-table :test 'eql))

;; define a analyzer function for OPCODES.
(defmacro* easm-define-stack-analyzer (opcodes &body body)
  (declare (indent 1))
  `(let ((fun (lambda (state pc opcode depth)
		(macrolet ((bytevector () '(easm-stack-state-bytevector state))
			   (worklist () '(easm-stack-state-worklist state)))
		  . ,body))))
     (dolist (opcode ,opcodes)
       (puthash opcode fun easm-stack-analyzers))))

;; return a list (<from> ... <from+length-1>)
(defun easm-range+ (from length)
  (loop for i from from below (+ from length)
	collect i))

;; encode two return values in a fixnum: the lower 8 bit are the PC increment
;; and the higher bits the new stack depth.
(defmacro easm-next (pc+ depth+)
  `(logior ,pc+ (ash (+ depth ,depth+) 8)))

(easm-define-stack-analyzer (append (easm-range+ byte-varref 6)
				    (easm-range+ byte-constant
						 byte-constant-limit))
  (easm-next 1 1))

(easm-define-stack-analyzer (list (+ byte-varref 6))
  (easm-next 2 1))

(easm-define-stack-analyzer (list (+ byte-varref 7)
				  byte-constant2)
  (easm-next 3 1))

(easm-define-stack-analyzer (append (easm-range+ byte-varbind 6)
				    (easm-range+ byte-varset 6))
  (easm-next 1 -1))

(easm-define-stack-analyzer (list (+ byte-varbind 6)
				  (+ byte-varset 6))
  (easm-next 2 -1))

(easm-define-stack-analyzer (list (+ byte-varbind 7)
				  (+ byte-varset 7))
  (easm-next 3 -1))

(easm-define-stack-analyzer (easm-range+ byte-call 6)
  (easm-next 1 (- (- opcode byte-call))))

(easm-define-stack-analyzer (list (+ byte-call 6))
  (easm-next 2 (- (easm-fetch-uint8 (bytevector) (1+ pc)))))

(easm-define-stack-analyzer (list (+ byte-call 7))
  (easm-next 3 (- (easm-fetch-uint16 (bytevector) (1+ pc)))))

(easm-define-stack-analyzer (easm-range+ byte-unbind 6)
  (easm-next 1 0))

(easm-define-stack-analyzer (list (+ byte-unbind 6))
  (easm-next 2 0))

(easm-define-stack-analyzer (list (+ byte-unbind 7))
  (easm-next 3 0))

(easm-define-stack-analyzer (list byte-return)
  nil)

(easm-define-stack-analyzer (list byte-goto)
  (easm-add-work state (easm-fetch-uint16 (bytevector) (1+ pc)) depth)
  nil)

(easm-define-stack-analyzer (list byte-goto-if-nil
				  byte-goto-if-not-nil)
  (easm-add-work state (easm-fetch-uint16 (bytevector) (1+ pc)) (1- depth))
  (easm-next 3 -1))

(easm-define-stack-analyzer (list byte-goto-if-nil-else-pop
				  byte-goto-if-not-nil-else-pop)
  (easm-add-work state (easm-fetch-uint16 (bytevector) (1+ pc)) depth)
  (easm-next 3 -1))

(easm-define-stack-analyzer (list byte-listN byte-concatN byte-insertN)
  (easm-next 2 (- (1- (easm-fetch-uint8 (bytevector) (1+ pc))))))

(defun easm-fetch-uint8 (bytevector offset)
  (aref bytevector offset))

(defun easm-fetch-uint16 (bytevector offset)
  (+ (aref bytevector offset)
     (ash (aref bytevector (1+ offset)) 8)))

;; used for debugging only
(defun easm-opcode-name (opcode)
  (macrolet ((within (lo len) `(and (<= ,lo opcode) (< opcode (+ ,lo ,len)))))
    (or (aref byte-code-vector opcode)
	(cond ((within byte-varref 8) 'varref)
	      ((within byte-varbind 8) 'varbind)
	      ((within byte-varset 8) 'varset)
	      ((within byte-unbind 8) 'unbind)
	      ((within byte-call 8) 'call)
	      ((within byte-constant byte-constant-limit) 'constant))
	(error "Unknown opcode: %d" opcode))))

;; remember the stack depth at offset PC.  Also update max depth
;; acrodingly.
(defun easm-note-depth (state pc depth)
  (let ((seen (easm-stack-state-seen state))
	(max (easm-stack-state-max state)))
    (assert (not (aref seen pc)))
    (when nil ; debug
      (let ((opcode (aref (easm-stack-state-bytevector state) pc)))
	(message "%2d: %2d  %s" pc depth (easm-opcode-name opcode))))
    (aset seen pc depth)
    (when (< max depth)
      (setf (easm-stack-state-max state) depth))))

;; add (PC . DEPTH) to the worklist
(defun easm-add-work (state pc depth)
  (let ((seen (easm-stack-state-seen state)))
    (cond ((aref seen pc)
	   (assert (= (aref seen pc) depth)))
	  (t
	   (push (cons pc depth) (easm-stack-state-worklist state))))
    nil))

;; compute the maximum stack depth for the bytecode vector BYTEVECTOR.
;; This is a worklist algorithm.  We start at PC=0 with depth=0.  For
;; the current instruction we compute the new stack depth and the next
;; PC.  For simple instruction we can just increment PC and the new
;; depth can easily be computed with a lookup in `byte-stack+-info'.
;; More complicated instructions have custom analyzer functions.  For
;; example for conditional jumps we add an entry (PC . DEPTH) for the
;; branch target.  And entry (PC . DEPTH) in the worklist means that
;; the instruction at offset PC is executed with DEPTH elements on the
;; stack.  The SEEN table is used to mark already visited instructions
;; and to ensure that the stack depth is consistent at control joins.
(defun easm-compute-stack-depth (bytevector)
  (let* ((seen (make-vector (length bytevector) nil))
	 (state (make-easm-stack-state :bytevector bytevector
				       :max 0 :seen seen)))
    (easm-add-work state 0 0)
    (while (easm-stack-state-worklist state)
      (destructuring-bind (pc . depth) (pop (easm-stack-state-worklist state))
	(let ((next nil))
	  (while (and (not (aref seen pc))
		      (setq next
			    (let* ((opcode (aref bytevector pc))
				   (analyzer (gethash opcode
						      easm-stack-analyzers)))
			      (easm-note-depth state pc depth)
			      (if analyzer
				  (funcall analyzer state pc opcode depth)
				(easm-next 1 (aref byte-stack+-info opcode))))))
	    (incf pc (logand next 255))
	    (setq depth (ash next -8)))
	  (when (aref seen pc)
	    (when next
	      (assert (= (aref seen pc) (ash next -8))))))))
    (easm-stack-state-max state)))


(defun easm-list-to-vector (list)
  (vconcat list))

(defun easm (arglist lap)
  "Assemble a byte-code-function with args ARGLIST from LAP.
LAP (Lisp Assembly Program) is a list of symbolic instructions.
Example:

 (easm '(x)
       '((varref x)
	 (return)))

retuns an identify function.

The symbolic instruction names are the same as for the
`disassemble'.  So the disassemler is the good tool to learn
about the existing instructions.

Labels are written as (label NAME).  E.g:

   (easm '() '((label loop) (goto loop)))

returns an endless loop.

Constants are written as (constant VALUE). E.g.

 (easm '() '((constant 42) (return)))

constantly returns 42."
  (let ((ctx (make-easm-context :instructions (mapcar #'copy-sequence lap))))
    (easm-scan ctx)
    (easm-assign-constants ctx)
    (easm-build-codevector ctx)
    (let* ((code  (easm-context-code ctx))
	   (constants (easm-list-to-vector
		       (mapcar #'car (easm-context-constants ctx))))
	   (depth (easm-compute-stack-depth code)))
      (make-byte-code arglist code constants depth))))



;; Some testing code.

;; return t iff `easm-compute-stack-depth' computes the same stack
;; depth as the byte compiler.  It's not always the case; probably due
;; to peephole optimizations.
(defun easm-check-symbol (symbol)
  (let* ((fun (symbol-function symbol))
	 (code (progn (fetch-bytecode fun) (aref fun 1)))
	 (depth (easm-compute-stack-depth code))
	 (ok (= depth (aref fun 3))))
    ;;(unless ok (debug nil symbol depth (aref fun 3)))
    (message "%s: %s" (if ok 'ok (format "%d %s" (- (aref fun 3) depth)
					 (cons depth (aref fun 3))))
	     symbol)
    ok))

(defun easm-check-all-symbols ()
  (interactive)
  (let ((failed '()))
    (catch 'break
      (mapatoms (lambda (symbol)
		  (when (and (fboundp symbol)
			     (byte-code-function-p (symbol-function symbol)))
		    (unless (easm-check-symbol symbol)
		      (push symbol failed))
		    (when (and nil (> (length failed) 100))
		      (throw 'break nil))))))
    (sort failed (lambda (s1 s2)
		   (< (length (aref (symbol-function s1) 1))
		      (length (aref (symbol-function s2) 1)))))))


;;; Examples:

(defun easm-example-fac (x)
  (if (zerop x) 1 (* x (easm-example-fac (1- x)))))

(fset 'easm-example-fac2
      (easm '(x)
	    '((constant zerop)
	      (varref x)
	      (call 1)
	      (goto-if-nil l1)
	      (constant 1)
	      (return)
	      (label l1)
	      (varref x)
	      (constant easm-example-fac2)
	      (varref x)
	      (sub1)
	      (call 1)
	      (mult)
	      (return))))

;; note: (= x 0) can be implement with bytecodes while (zerop x)
;; requires a call.
(defun easm-example-fac3 (x)
  (let ((accu 1))
    (while (not (= x 0))
      (setq accu (* x accu))
      (setq x (1- x)))
    accu))

;; almost the same as fac3 but x is kept on the stack
(fset 'easm-example-fac4
      (easm '(x)
	    '((constant 1)
	      (varbind accu)
	      (varref x)
	      ;; x
	      (label loop)
	      (dup)
	      (constant 0)
	      (eqlsign)
	      ;; x flag
	      (goto-if-not-nil done)
	      (dup)
	      (varref accu)
	      ;; x x accu
	      (mult)
	      (varset accu)
	      (sub1)
	      (goto loop)
	      (label done)
	      ;; x
	      (discard)
	      (varref accu)
	      (unbind 1)
	      (return))))

(defun easm-test ()
  (assert (= (easm-example-fac 10) (easm-example-fac2 10)))
  (assert (= (easm-example-fac 10) (easm-example-fac4 10))))

(provide 'easm)

;; easm.el ends here
