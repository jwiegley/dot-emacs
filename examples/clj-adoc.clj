;; Clojure Asciidoc
;; ================

;; This is the same transformation as adoc-clj, but we start from this time from
;; the clojure file rather than the asciidoc.

;; [source,lisp]
;; ----
(println "hello")
;; ----

;; In practice, this makes very little difference.

;; [source,clojure]
;; ----
(println "In case I am using the clojure style")
;; ----

;; And here are the local variables.

;; //
;; // Local Variables:
;; // lentic-init: lentic-clojure-asciidoc-init
;; // End: 
;; //
