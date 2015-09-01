;; And this is all working too....
;; This buffer shows a "block-comment" where we wish to comment large blocks
;; of the buffer between one lentic buffer and the other.
;; hello well this is all working
;; In this case, we use latex tags to indicate the code blocks. Outside of
;; these tags, we start every line with comments. Inside we do not (although
;; we leave comments that are there.

;; \begin{code}
(println "It is now broken")
;; \end{code}

;; We can have multiple code blocks, of course, after the first.

;; \begin{code}
(println "hello")
;; \end{code}

;; And more

;; \begin{code}
(println "Hello")
;; \end{code}

;; And more

;; \begin{code}
(println "hello")
;; \end{code}

;; And we can put more comments after the final text. And finally, we finish
;; with a file local variable to tell lentic what kind of text this is. Note
;; that start characters which are comments in both clojure and latex. In real
;; use dir-local variables work better.

;; %%
;; %% Local Variables:
;; %% lentic-init: (lentic-default-init lentic-clojure-latex-init)
;; %% End:
;; %%
