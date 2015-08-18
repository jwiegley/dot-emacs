;; This file is similar to block-comment.clj, but uses delayed cloning.
;; That is all the lentic functionality runs on the idle cycle. Originally,
;; this was a good idea, as lentic.el was rather inefficient, and could make
;; emacs lag. Now this is probably less efficient and isn't really necessary.


;; \begin{code}
(println "hello world")
;; \end{code}

;; Lorem ipsum dolor sit amet, consectetuer adipiscing elit. Donec hendrerit
;; tempor tellus. Donec pretium posuere tellus. Proin quam nisl, tincidunt et,
;; mattis eget, convallis nec, purus. Cum sociis natoque penatibus et magnis dis
;; parturient montes, nascetur ridiculus mus. Nulla posuere. Donec vitae dolor.
;; Nullam tristique diam non turpis. Cras placerat accumsan nulla. Nullam rutrum.
;; Nam vestibulum accumsan nisl.

;; Lorem ipsum dolor sit amet, consectetuer adipiscing elit. Donec hendrerit
;; tempor tellus. Donec pretium posuere tellus. Proin quam nisl, tincidunt et,
;; mattis eget, convallis nec, purus. Cum sociis natoque penatibus et magnis dis
;; parturient montes, nascetur ridiculus mus. Nulla posuere. Donec vitae dolor.
;; Nullam tristique diam non turpis. Cras placerat accumsan nulla. Nullam rutrum.
;; Nam vestibulum accumsan nisl.

;; Lorem ipsum dolor sit amet, consectetuer adipiscing elit. Donec hendrerit
;; tempor tellus. Donec pretium posuere tellus. Proin quam nisl, tincidunt et,
;; mattis eget, convallis nec, purus. Cum sociis natoque penatibus et magnis dis
;; parturient montes, nascetur ridiculus mus. Nulla posuere. Donec vitae dolor.
;; Nullam tristique diam non turpis. Cras placerat accumsan nulla. Nullam rutrum.
;; Nam vestibulum accumsan nisl.


;; ;;

;; %%
;; %% Local Variables:
;; %% lentic-init: lentic-clojure-latex-delayed-init
;; %% End:
;; %%
