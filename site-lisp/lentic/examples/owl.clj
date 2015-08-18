;; %% The contents of this file are subject to the LGPL License, Version 3.0.

;; %% Copyright (C) 2012, 2013, Newcastle University

;; %% This program is free software: you can redistribute it and/or modify
;; %% it under the terms of the GNU Lesser General Public License as published by
;; %% the Free Software Foundation, either version 3 of the License, or
;; %%  (at your option) any later version.
;; %%
;; %%  This program is distributed in the hope that it will be useful,
;; %%  but WITHOUT ANY WARRANTY; without even the implied warranty of
;; %%  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; %%  GNU Lesser General Public License for more details.
;; %%
;; %%  You should have received a copy of the GNU Lesser General Public License
;; %%  along with this program.  If not, see http://www.gnu.org/licenses/.

;; This is just a big file to test performance of clojure->latex transformation.
;; The code comes from my Tawny-OWL project, but is not an up to date version.

;; In this case, I have a single code block comment which is obviously not
;; what we would want in reality.
;; \begin{code}
(ns ^{:doc "Build ontologies in OWL."
      :author "Phillip Lord"}
  tawny.owl
  (:require
   [clojure.walk :only postwalk]
   [clojure.set]
   [clojure.java.io]
   [tawny.util :as util])
  (:import
   (org.semanticweb.owlapi.model
    OWLAxiom
    OWLEntity
    OWLObject
    OWLOntologyManager OWLOntology IRI
    OWLClassExpression OWLClass OWLAnnotation
    OWLIndividual OWLDatatype
    OWLObjectPropertyExpression
    OWLNamedObject OWLOntologyID
    OWLAnnotationProperty OWLObjectProperty
    OWLDataFactory OWLOntologyFormat
    OWLDataProperty OWLDataRange OWLProperty OWLPropertyExpression
    OWLDataPropertyExpression OWLLiteral)
   (org.semanticweb.owlapi.apibinding OWLManager)
   (org.coode.owlapi.manchesterowlsyntax ManchesterOWLSyntaxOntologyFormat)
   (org.semanticweb.owlapi.io StreamDocumentTarget OWLXMLOntologyFormat
                              RDFXMLOntologyFormat)
   (org.semanticweb.owlapi.util DefaultPrefixManager OWLEntityRemover)
   (java.io ByteArrayOutputStream FileOutputStream PrintWriter)
   (java.io File)
   (java.util Collections)
   (org.semanticweb.owlapi.model AddAxiom RemoveAxiom AddImport
                                 AddOntologyAnnotation)))
;; \end{code}


;; The next set of forms all contain values that percolate across all the
;; namespaces that contain ontologies. Resetting all of these when owl.clj is
;; eval'd is a pain, hence they are all defonce. Access is via a fn, because
;; this is more adapatable and also because I monkey patch them inside
;; protege. They used to be closures but this was a pain to type hint
;; \begin{code}
(defonce
  ^{:doc "The OWLDataFactory used for Tawny."
    :private true}
  vowl-data-factory (atom nil))

(defn ^OWLDataFactory owl-data-factory
  "Returns the main factory for all other objects."
  []
  (when-not @vowl-data-factory
    (reset! vowl-data-factory
            (OWLManager/getOWLDataFactory)))
  @vowl-data-factory)

(defonce
  ^{:doc "The OWLOntologyManager used for Tawny."
    :private true}
  vowl-ontology-manager (atom nil))

(defn ^OWLOntologyManager owl-ontology-manager
  "The single OWLOntologyManager used by Tawny."
  []
  (when-not @vowl-ontology-manager
    (reset! vowl-ontology-manager
            (OWLManager/createOWLOntologyManager (owl-data-factory))))
  @vowl-ontology-manager)

(defonce
  ^{:doc "Map between namespaces and ontologies"}
  ontology-for-namespace (ref {}))

(defn ^IRI iri
  "Returns an IRI object given a string or URI. Does no transformation on the
string; use 'iri-for-name' to perform ontology specific expansion"
  [name]
  (util/with-types
    [name [String java.net.URL java.io.File]]
    (IRI/create name)))

(load "owl_self")

(defn named-object?
  "Returns true iff entity is an OWLNamedObject."
  [entity]
  (instance? OWLNamedObject entity))

(defn ^OWLNamedObject as-named-object
  "If entity is a named object do nothing, else throw
an exception."
  [entity]
  (or
   (and (instance? OWLNamedObject entity)
        entity)
   (throw (IllegalArgumentException. "Expecting a named entity"))))

;;; Begin current ontology support

;; not sure this is necessary now as (almost) all functions now take an
;; ontology parameter, which is generally going to be the nicer way to achieve
;; things.

(defn get-current-ontology-maybe
  "Gets the current ontology, or nil if there is not one."
  ([]
     (get-current-ontology-maybe *ns*))
  ([ns]
     ;; have taken out the current bound ontology as we don't need it now and
     ;; it comes at a cost
     (get @ontology-for-namespace ns)))

(defn get-current-ontology
  "Gets the current ontology. Throws an exception if there is not current
ontology"
  ([]
     (get-current-ontology *ns*))
  ([ns]
     (or (get-current-ontology-maybe ns)
         ;; so break
         (throw (IllegalStateException. "Current ontology has not been set")))))

(defmacro defnwithfn
  "Define a new var like defn, but compose FUNCTION with BODY before
rather than just using BODY directly."
  [name function & body]
  `(let [vr# (defn ~name ~@body)]
     (alter-var-root
      vr#
      (fn [f#]
        (fn ~name [& args#]
          (apply ~function f# args#))))
     vr#))

(defonce
  ^{:doc "Hook called when the default ontology is used"}
  default-ontology-hook (util/make-hook))

;;
;; The following section is aggressively optimized, because these functions
;; are called for almost every other method invocation. Where ever possible,
;; we avoid variadic methods; things that could be done as loops are unwound,
;; and some logic is done in macro. There is some code duplication as a
;; result.
;;
(defn- default-ontology-base-dispatcher [ffco f & args]
  "Invoke f ensuring that the first argument is an ontology or nil.
This works wqhere we already know that the first value of args is not an
ontology. So, we search for :ontology frame or call ffco to fetch this ontology."
  (util/run-hook default-ontology-hook)
  (apply f (ffco) args))

(defmacro ^{:private true} dispatch-maybe
  "Dispatch with the default ontology if necessary and if it is present."
  [f & args]
  ;; the majority of this macro is duplicated in variadic
  ;; version of dispatch-ontology-maybe
  `(if
       (or (instance?
            org.semanticweb.owlapi.model.OWLOntology ~(first args))
           (nil? ~(first args)))
     (~f ~@args)
     (do
       (tawny.util/run-hook tawny.owl/default-ontology-hook)
       (~f (tawny.owl/get-current-ontology-maybe) ~@args))))

(defn default-ontology-maybe
  "Invoke f ensuring the first argument is an ontology or nil.
The logic used is the same as default-ontology except that no error is
signalled if there is no current-ontology. The multi-arity function avoids
variadic calls most of the time."
  ([f a]
     (dispatch-maybe f a))
  ([f a b]
     (dispatch-maybe f a b))
  ([f a b c]
     (dispatch-maybe f a b c))
  ([f a b c d]
     (dispatch-maybe f a b c d))
  ([f a b c d e]
     (dispatch-maybe f a b c d e))
  ([f a b c d e fa]
     (dispatch-maybe f a b c d e fa))
  ([f a b c d e fa & args]
     (if (or
          (instance? org.semanticweb.owlapi.model.OWLOntology a)
          (nil? a))
       (apply f a b c d e fa args)
       (apply default-ontology-base-dispatcher
              get-current-ontology-maybe
              f a b c d e fa args))))

(defmacro ^{:private true} dispatch
  "Dispatch with the default ontology if necessary."
  [f & args]
  ;; the majority of this macro is duplicated in variadic
  ;; version of dispatch-ontology
  `(if
       (instance?
        org.semanticweb.owlapi.model.OWLOntology ~(first args))
     (~f ~@args)
     (do
       (util/run-hook default-ontology-hook)
       (~f (get-current-ontology) ~@args))))

(defn default-ontology
  "Invoke f ensuring the first argument is an ontology or nil.
If the first argument is already an ontology use that, if not use the default
ontology, or throw an IllegalStateException. To set the default ontology use
either the defontology macro, or ontology-to-namespace. This function is
multi-arity as a micro optimization, to avoid a variadic invocation."
  ([f]
     (dispatch f))
  ([f a]
     (dispatch f a))
  ([f a b]
     (dispatch f a b))
  ([f a b c]
     (dispatch f a b c))
  ([f a b c d]
     (dispatch f a b c d))
  ([f a b c d e]
     (dispatch f a b c d e))
  ([f a b c d e fa]
     (dispatch f a b c d e fa))
  ([f a b c d e fa & args]
     (if (or
          (instance? org.semanticweb.owlapi.model.OWLOntology a)
          (nil? a))
       (apply f a b c d e fa args)
       (apply default-ontology-base-dispatcher
              get-current-ontology
              f a b c d e fa args))))

;; broadcast-ontology is also highly optimized
(defn- broadcast-ontology-int
  "Implements the broadcast function for up to six arguments. First argument
is an ontology, the last is th function that we are broadcasting to, and all
the other arguments are arguments to be passed. At this point o may be either
an ontology or nil, depending on what calls this, and a-f are definately not
lists. There was a good reason for putting fnc at the end of the argument
list, but I cannot remember what it was."
  ;; at this point o is definately an ontology and a-f are definately not lists
  ([o a fnc]
     (fnc o a))
  ([o a b fnc]
     ;; dispense with the list for this case when we don't need it
     (fnc o a b))
  ([o a b c fnc]
     (list
      (fnc o a b)
      (fnc o a c)))
  ([o a b c d fnc]
     (list
      (fnc o a b)
      (fnc o a c)
      (fnc o a d)))
  ([o a b c d e fnc]
     (list
      (fnc o a b)
      (fnc o a c)
      (fnc o a d)
      (fnc o a e)))
  ([o a b c d e f fnc]
     (list
      (fnc o a b)
      (fnc o a c)
      (fnc o a d)
      (fnc o a e)
      (fnc o a f))))

(defn broadcast-ontology-full
  "Given a function which expects an ontology and two other arguments, ensure
that the first argument is an ontology (see default-ontology for details),
then f repeatedly against the second args and all subsequent arguments
flattened. Where possible, we avoid using this function for the micro-optimisd
broadcast-ontology."
  [f & args]
  (apply default-ontology
         (fn [o & narg]
           (doall
            (map (partial f o (first narg))
                 (flatten
                  (rest narg)))))
         args))

(defmacro ^{:private true}
  if-not-sequential
  "If all seqs are not sequential. This is a micro-optimisation, as use of
every? requires a list at run time when we have an list of arguments." 
  [seqs & rest]
  `(if (and
        ~@(map
           (fn [seq]
             `(not (sequential? ~seq)))
           ;; reverse the seqs because the last argument is often a list, for
           ;; calls from the named entity functions, such as owl-class. So, we
           ;; can break early and fail fast in these cases.
           (reverse seqs)))
     ~@rest))

(defn broadcast-ontology
  "Given a function, fnc, and args ensure that the first arg is an ontology
using default-ontology, and then broadcast the rest, so that the fnc is called
with the first and second args, first and third args and so on. This function
is micro-optimised to avoid use of variadic method calls or list operations."
  ([fnc a b]
     (if-not-sequential
      [a b]
      (default-ontology
        broadcast-ontology-int
        a b fnc)
      (broadcast-ontology-full fnc a b)))
  ([fnc a b c]
     (if-not-sequential
      [a b c]
      (default-ontology
        broadcast-ontology-int a b c fnc)
      (broadcast-ontology-full fnc a b c)))
  ([fnc a b c d]
     (if-not-sequential
      [a b c d]
      (default-ontology
        broadcast-ontology-int a b c d fnc)
      (broadcast-ontology-full fnc a b c)))
  ([fnc a b c d e]
     (if-not-sequential
      [a b c d e]
      (default-ontology
        broadcast-ontology-int a b c d e fnc)
      (broadcast-ontology-full fnc a b c)))
  ([fnc a b c d e f]
     (if-not-sequential
      [a b c d e f]
      (default-ontology
        broadcast-ontology-int a b c d e f fnc)))
  ([fnc a b c d e f & args]
     (apply broadcast-ontology-full
            fnc a b c d e f args)))

(defn- broadcast-ontology-maybe-full
  "Like broadcast-ontology-maybe-full but does not signal an error if there is no current
ontology."
  [f & args]
  (apply default-ontology-maybe
         (fn broadcast-ontology-maybe [o & narg]
           (doall
            (map (partial f o (first narg))
                 (flatten
                  (rest narg)))))
         args))

(defn broadcast-ontology-maybe
  "Like broadcast-ontology but does not signal an error where there is no
default ontology."
  ([fnc a b]
     (if-not-sequential
      [a b]
      (default-ontology-maybe
        broadcast-ontology-int
        a b fnc)
      (broadcast-ontology-maybe-full fnc a b)))
  ([fnc a b c]
     (if-not-sequential
      [a b c]
      (default-ontology-maybe
        broadcast-ontology-int a b c fnc)
      (broadcast-ontology-maybe-full fnc a b c)))
  ([fnc a b c d]
     (if-not-sequential
      [a b c d]
      (default-ontology-maybe
        broadcast-ontology-int a b c d fnc)
      (broadcast-ontology-maybe-full fnc a b c d)))
  ([fnc a b c d e]
     (if-not-sequential
      [a b c d e]
      (default-ontology-maybe
        broadcast-ontology-int a b c d e fnc)
      (broadcast-ontology-maybe-full fnc a b c d e)))
  ([fnc a b c d e & args]
     (apply broadcast-ontology-maybe-full
            fnc a b c d e args)))

;;
;; End micro-optimized section!
;;

(defmacro defdontfn
  "Like defn, but automatically adds the current-ontology to the args
if the first arg is not an ontology. Throws an IllegalStateException
if there is no current ontology.

The 'd' stands for definitely."
  [name & body]
  `(defnwithfn ~name #'default-ontology
     ~@body))

(defmacro defmontfn
  "Like defn, but automatically adds the current ontology or nil to the args
  if the first arg is not an ontology.

The 'm' stands for maybe."
  [name & body]
  `(defnwithfn ~name #'default-ontology-maybe
     ~@body))


(defmacro defbdontfn
  "Like the defn and defdontfn, but broadcasts. That is it expects a three arg
function, f with ontology, x and y, but defines a new function which takes
ontology, x and rest, returning a list which is f applied to ontology, x and
the flattened elements of rest.

Uses the default ontology if not supplied and throws an IllegalStateException
  if this is not set."
  [name & body]
  `(defnwithfn ~name #'broadcast-ontology
     ~@body))

(defmacro defbmontfn
  "Like defbdontfn, but also accepts nil as either the passed or default ontology."
  [name & body]
  `(defnwithfn ~name #'broadcast-ontology-maybe
     ~@body))

;;; Axiom mainpulation
(defdontfn add-axiom
  "Adds an axiom from the given ontology, or the current one."
  [^OWLOntology o  ^OWLAxiom axiom]
  (.applyChange (owl-ontology-manager)
                (AddAxiom. o axiom))
  axiom)

(defdontfn remove-axiom
  "Removes a list of axioms from the given ontology, or the current one."
  [o & axiom-list]
  (doall
   (map (fn [axiom]
          (.applyChange (owl-ontology-manager)
                        (RemoveAxiom. o axiom)))
        (flatten axiom-list))))

(defdontfn remove-entity
  "Remove from the ontology an entity created and added by
owl-class, defclass, object-property or defoproperty. Entity is the value
returned by these functions.

This removes all the axioms that were added. So, for example, a form such as

   (defclass a
      :subclass b
      :equivalent c)

adds three axioms -- it declares a, makes it a subclass of b, and equivalent
of c."
  [o ^OWLEntity entity]
  (let [remover
        (OWLEntityRemover. (owl-ontology-manager)
                           (hash-set o))]
    (.accept entity remover)
    (.applyChanges (owl-ontology-manager)
                   (.getChanges remover))))

;;; Begin Ontology options

;; ontology options -- additional knowledge that I want to attach to each
;; ontology,  but which gets junked when the ontology does.
(def ^{:doc "Ontology options. A map on a atom for each ontology"}
  ontology-options-atom (atom {}))

;; return options for ontology -- lazy (defn get-ontology-options [ontology])
(defdontfn ontology-options
  "Returns the ontology options for 'ontology'
or the current-ontology"
  [o]
  (if-let [options
           (get @ontology-options-atom o)]
    options
    (get
     (swap!
      ontology-options-atom assoc o (ref {}))
     o)))

;;; Begin iri support
(defdontfn ^IRI get-iri
  "Gets the IRI for the given ontology, or the current ontology if none is given"
  [^OWLOntology o]
  (.getOntologyIRI
   (.getOntologyID o)))

(defdontfn iri-for-name
  "Returns an IRI object for the given name.

This is likely to become a property of the ontology at a later date, but at
the moment it is very simple."
  [o name]
  (if-let [iri-gen (:iri-gen (deref (ontology-options o)))]
    (iri-gen name)
    (iri (str (get-iri o) "#" name))))

;;; Begin interned-entity-support
(defonce
  ^{:doc "Hook called when an new var is created with an OWLObject, with the var"}
  intern-owl-entity-hook
  (util/make-hook))

(defn
  run-intern-hook
  "Run intern-owl-entity hooks and return first argument."
  [var]
  (util/run-hook intern-owl-entity-hook var)
  var)

;; In the idea world, these would be one function. However, they can't be. The
;; intern version works where we do not know the symbol at compile time. This
;; is generally useful for read'ing and the like. The symbol created cannot be
;; used in the same form because the compiler doesn't know that it has been
;; defined.
(defn intern-owl-string
  "Interns an OWL Entity. Compared to the clojure.core/intern function this
signals a hook, and adds :owl true to the metadata. NAME must be a strings"
  ([name entity]
     (tawny.owl/run-intern-hook
      (intern *ns*
              (with-meta
                (symbol name)
                {:owl true})
              entity))))

;; While this version uses def semantics -- the point here is that the def
;; form is expanded at compile time, the compiler recognises that the form has
;; been defined, and so allows subsequent referencing of the symbol within the
;; same form.
(defmacro intern-owl
  "Intern an OWL Entity. Compared to the clojure.core/intern function this
signals a hook, and adds :owl true to the metadata. NAME must be a symbol"
  ([name entity]
     ;; we use def semantics here, rather than intern-owl-string, because
     ;; intern is not picked up by the compiler as defining a symbol
     `(tawny.owl/run-intern-hook
       (def ~(vary-meta name
                        merge
                        {:owl true})
         ~entity))))

;;; Begin OWL2 datatypes
(def
  ^{:doc "A map of keywords to the OWL2Datatypes values"}
  owl2datatypes
  (into {}
        (for [^org.semanticweb.owlapi.vocab.OWL2Datatype
              k (org.semanticweb.owlapi.vocab.OWL2Datatype/values)]
          [(keyword (.name k)) k])))

;;; Begin Annotation Support

;; annotations
(defbdontfn add-a-simple-annotation
  "Adds an annotation to a named object."
  [o ^OWLNamedObject named-entity annotation]
  (let [axiom
        (.getOWLAnnotationAssertionAxiom
         (owl-data-factory)
         (.getIRI named-entity) annotation)]
    (add-axiom o axiom)))

(defn- add-a-name-annotation
  "Add a tawny-name annotation to named-entity, unless the :noname
ontology option has been specified, in which case do nothing."
  [o named-entity name]
  (when
      (and
       (not (get @(ontology-options o)
                 :noname false))
       (instance? String name))
    (add-a-simple-annotation o named-entity (tawny-name name))))

(defbdontfn add-an-ontology-annotation
  "Adds an annotation to an ontology."
  [o o annotation]
  (.applyChange
   (owl-ontology-manager)
   (AddOntologyAnnotation. o annotation)))

(defdontfn add-annotation
  {:doc "Add an annotation in the ontology to either the named-entity
or the ontology. Broadcasts over annotations."
   :arglists '([ontology named-entity & annotations]
                 [named-entity & annotations]
                   [ontology & annotations][annotations])}
  [o & args]
  (if (named-object? (first args))
    (add-a-simple-annotation
     o (first args) (rest args))
    (add-an-ontology-annotation
     ;; okay, so this is wierd, but broadcasting requires a three arg
     ;; function, first being an ontology.
     o o args)))

(defn- ^OWLAnnotationProperty ensure-annotation-property
  "Ensures that 'property' is an annotation property,
converting it from a string or IRI if necessary."
  [o property]
  (cond
   (instance? OWLAnnotationProperty property)
   property
   (instance? IRI property)
   (.getOWLAnnotationProperty
    (owl-data-factory) property)
   (instance? String property)
   (ensure-annotation-property
    o
    (iri-for-name o property))
   :default
   (throw (IllegalArgumentException.
           (format "Expecting an OWL annotation property: %s" property)))))

(defmontfn annotation
  "Creates a new annotation property. If literal is a string it is
interpreted as a String in English. Alternatively, a literal creatd
with the literal function."
  ([o annotation-property literal]
     (cond
      (instance? String literal)
      (annotation o annotation-property literal "en")
      (instance? IRI literal)
      (.getOWLAnnotation
       (owl-data-factory)
       (ensure-annotation-property o annotation-property)
       literal)
      (instance? OWLLiteral literal)
      (.getOWLAnnotation
       (owl-data-factory)
       (ensure-annotation-property o annotation-property)
       literal)
      :default
      (throw (IllegalArgumentException.
              "annotation takes a String or OWLLiteral"))))
  ([o annotation-property ^String literal ^String language]
     (annotation o annotation-property
                 (.getOWLLiteral (owl-data-factory) literal language))))

(defbdontfn add-super-annotation
  "Adds a set of superproperties to the given subproperty."
  [o subproperty superproperty]
  (.applyChange (owl-ontology-manager)
                (AddAxiom.
                 o
                 (.getOWLSubAnnotationPropertyOfAxiom
                  (owl-data-factory)
                  subproperty
                  (ensure-annotation-property o superproperty)))))


(def deprecated-add-sub-annotation
  "The same as add-super-annotation used to implement the old
add-sub-annotation functionality."
  add-super-annotation)

;; various annotation types
(def label-property
  (.getRDFSLabel (owl-data-factory)))

(defmontfn label
  "Return an OWL label annotation."
  [o & args]
  (apply annotation o label-property args))

(def owl-comment-property
  (.getRDFSComment (owl-data-factory)))

(defmontfn owl-comment
  "Return an OWL comment annotation."
  [o & args]
  (apply annotation o owl-comment-property args))

(def is-defined-by-property
  (.getRDFSIsDefinedBy (owl-data-factory)))

(defmontfn is-defined-by
  "Return an is defined by annotation."
  [o & args]
  (apply annotation o is-defined-by-property args))

(def see-also-property
  (.getRDFSSeeAlso (owl-data-factory)))

(defmontfn see-also
  "Returns a see-also annotation."
  [o & args]
  (apply annotation o
         see-also-property args))

(def backward-compatible-with-property
  (.getOWLBackwardCompatibleWith (owl-data-factory)))

(defmontfn backward-compatible-with
  "Returns a backward compatible with annotation."
  [o & args]
  (apply annotation o
         backward-compatible-with-property
         args))

(def incompatible-with-property
  (.getOWLIncompatibleWith (owl-data-factory)))

(defmontfn incompatible-with
  "Returns an incompatible with annotation."
  [o & args]
  (apply annotation o
         incompatible-with-property
         args))

(def version-info-property
  (.getOWLVersionInfo (owl-data-factory)))

(defmontfn version-info
  "Returns a version info annotation."
  [o & args]
  (apply annotation o
         version-info-property
         args))

(def deprecated-property
  (.getOWLDeprecated (owl-data-factory)))

(defmontfn deprecated
  "Returns a deprecated annotation."
  [o & args]
  (apply annotation o
         deprecated-property
         args))

(defbmontfn add-label
  "Add labels to the named entities."
  [o named-entity label]
  (add-annotation
   o
   named-entity
   [(tawny.owl/label o label)]))

(defbmontfn add-comment
  "Add comments to the named entities."
  [o named-entity comment]
  (add-annotation o named-entity
                  [(owl-comment o comment)]))


(def ^{:private true} annotation-property-handlers
  {
   :super add-super-annotation
   :subproperty deprecated-add-sub-annotation
   :annotation add-annotation
   :comment add-comment
   :label add-label
   })

(defdontfn annotation-property-explicit
  "Add this annotation property to the ontology"
  [o name frames]
  (let [property (ensure-annotation-property o name)]
    ;; add the propertyq
    (.addAxiom (owl-ontology-manager)
               o
               (.getOWLDeclarationAxiom
                (owl-data-factory)
                property))
    ;; add a name annotation
    (add-a-name-annotation o property name)
    ;; apply the handlers
    (doseq [[k f] annotation-property-handlers
            :when (get frames k)]
      (f o property (get frames k)))
    ;; return the property
    property))

(defdontfn annotation-property
  {:doc "Creates a new annotation property."
   :arglists '([ontology name & frames] [name & frames])}
  [o name & frames]
  (annotation-property-explicit
   o
   name
   (util/check-keys
    (util/hashify frames)
    (keys annotation-property-handlers))))

(defn- get-annotation-property
  "Gets an annotation property with the given name."
  [o property]
  (.getOWLAnnotationProperty
   (owl-data-factory)
   (iri-for-name o property)))

(defn- extract-ontology-frame
  "Extracts the ontology frames from a list of frames.
Currently, we define this to be the second value iff the first is an :ontology
keyword. Returns a map of :ontology and the ontology or nil, and :args with
the args minus the ontology frame if it exists."
  [frames]
  (if (= :ontology (first frames))
    {:ontology (second frames)
     :frames (nthrest frames 2)}
    {:ontology nil
     :frames frames}))

(defn- entity-generator [entity frames entity-function]
  (let [ontsplit (extract-ontology-frame frames)
        ont (:ontology ontsplit)
        frames (:frames ontsplit)
        entity-name (name entity)
        ]
    `(let [entity#
           ~(if ont
              `(~entity-function
                ~ont
                ~entity-name
                ~@frames)
              `(~entity-function
               ~entity-name
               ~@frames))]
       (tawny.owl/intern-owl ~entity entity#))))

(defmacro ^{:private true} defentity
  "Defines a new entity macro."
  [name docstring entity-function]
  `(defmacro
     ~name
     ~docstring
     [entity# & frames#]
     (entity-generator entity# frames# ~entity-function)))

(defentity defaproperty
  "Defines a new annotation property in the current ontology.
See 'defclass' for more details on the syntax"
  'tawny.owl/annotation-property)

(comment
  (defmacro defaproperty
    "Defines a new annotation property in the current ontology.
See 'defclass' for more details on the syntax."
    [property & frames]
    (let [ontsplit (extract-ontology-frame frames)
          ont (:ontology ontsplit)
          frames (:frames ontsplit)]
      `(let [property-name# (name '~property)
             property#
             (tawny.owl/annotation-property
              ~ont
              property-name#
              ~@frames)]
         (intern-owl ~property property#)))))

;;; Ontology manipulation

(defn ontology-to-namespace
  "Sets the current ontology as defined by `defontology'"
  ([o]
     (ontology-to-namespace *ns* o))
  ([ns o]
     (dosync
      (alter
       ontology-for-namespace
       assoc ns o))))

(defn- remove-ontology-from-namespace-map
  "Remove an ontology from the namespace map"
  [o]
  (dosync
   (doseq
       [ns
        ;; select namespaces with given ontology
        (for [[k v] @ontology-for-namespace
              :when (= v o)]
          k)]
     (alter ontology-for-namespace
            dissoc ns))))

(def
  ^{:doc "Hook called immediately after an ontology is removed from the
owl-ontology-manager."}
  remove-ontology-hook (util/make-hook))

(defn remove-ontology-maybe
  "Removes the ontology with the given ID from the manager.
This calls the relevant hooks, so is better than direct use of the OWL API. "
  [^OWLOntologyID ontologyid]
  (when (.contains (owl-ontology-manager) ontologyid)
    (let [o (.getOntology (owl-ontology-manager) ontologyid)]
      (.removeOntology
       (owl-ontology-manager) o)
      ;; remove the ontology options
      (dosync
       (swap! ontology-options-atom
              dissoc o))
      ;; remove the ontology from the namespace map
      (remove-ontology-from-namespace-map o)
      (util/run-hook remove-ontology-hook o)
      o)))

(defn- add-an-ontology-name
  "Adds an tawny-name annotation to ontology, unless the :noname ontology
  options is specified in which case do nothing."
  [o n]
  (when
      (and
       (not (get @(ontology-options o)
                 :noname false))
       n)
    (add-an-ontology-annotation
     o o (tawny-name n))))

(defn- set-iri-gen
  "Add an IRI gen function to the ontology options."
  [o f]
  (if f
    (dosync
     (alter (ontology-options o)
            merge {:iri-gen f}))))

(defn- set-prefix
  "Sets a prefix for the ontology."
  [^OWLOntology o ^String p]
  (if p
    (.setPrefix
     (.asPrefixOWLOntologyFormat
      (.getOntologyFormat
       (owl-ontology-manager) o))
     p (str (get-iri o)))))


(defn- add-ontology-comment
  "Adds a comment annotation to the ontology"
  [o s]
  (if s
    (add-annotation o (owl-comment o s))))


(defn- add-see-also
  "Adds a see also annotation to the ontology"
  [o s]
  (if s
    (add-annotation o (see-also o s))))

(defn- add-version-info
  "Adds a version info annotation to the ontology."
  [o v]
  (if v
    ;; ontology annotation is a default ontology function, so need to pass
    ;; ontology twice even if this makes little sense!
    (add-an-ontology-annotation o o v)))

;; owl imports
(defn owl-import
  "Adds a new import to the current ontology. o may be an
ontology or an IRI"
  ([o]
     (owl-import (get-current-ontology) o))
  ([ontology-into o]
     (let [iri (if (instance? OWLOntology o)
                 (get-iri o)
                 o)]
       (.applyChange (owl-ontology-manager)
                     (AddImport. ontology-into
                                 (.getOWLImportsDeclaration
                                  (owl-data-factory)
                                  iri))))))
;; ontology
(def ^{:private true} ontology-handlers
  {:iri-gen set-iri-gen,
   :prefix set-prefix,
   :name add-an-ontology-name
   :seealso add-see-also
   :comment add-ontology-comment
   :versioninfo add-version-info
   })

(defn ontology
  "Returns a new ontology. See 'defontology' for full description."
  [& args]
  (let [options (apply hash-map args)
        ;; the prefix is specified by the prefix or the name.
        ;; this allows me to do "(defontology tmp)"
        options (merge options
                       {:prefix (or (:prefix options)
                                    (:name options))})
        iri (iri (get options :iri
                             (str
                              (java.util.UUID/randomUUID)
                              (if-let [name
                                       (get options :name)]
                                (str "#" name)))))
        noname (get options :noname false)
        ]
    (remove-ontology-maybe
     (OWLOntologyID. iri))
    (let [ontology
          (.createOntology (owl-ontology-manager) iri)]
      (if noname
        (dosync
         (alter
          (tawny.owl/ontology-options ontology)
          merge {:noname true}))
        (owl-import ontology
                    (tawny-ontology)))
      (doseq [[k f] ontology-handlers
              :when (get options k)]
        (f ontology (get options k)))
      ontology)))

(defmacro defontology
  "Define a new ontology with `name'.

The following keys must be supplied.
:iri -- the IRI for the new ontology
:prefix -- the prefix used in the serialised version of the ontology
"
  [name & body]
  `(do
     (let [ontology# (ontology :name ~(clojure.core/name name) ~@body)
           var#
           (def
             ~(with-meta name
                (assoc (meta name)
                  :owl true))
             ontology#)]
       (tawny.owl/ontology-to-namespace ontology#)
       var#
       )))

;;; Begin ontology look up functions
(defn- check-entity-set
  [entity-set iri]
  ;; ontology could be in full, or could be punning. Either way we are
  ;; stuffed.
  (when (< 1 (count entity-set))
    (throw
     (IllegalArgumentException.
      (format "Can not uniquely determine type of IRI: %s,%s" iri entity-set))))
  ;; IRI appears once; happiness or
  ;; IRI appears not at all
  (when (= 1 (count entity-set))
    (first entity-set)))

(defdontfn entity-for-iri
  "Return the OWLObject for a given IRI if it exists, checking
'ontology' first, but checking all loaded ontologies.

This function uses a heuristic to find the right entity. If you want
more control use 'check-entity-set' and the '.getEntitiesInSignature'
method of OWLOntology."
  [^OWLOntology o ^IRI iri]
  (or
   ;; single item in current ontology
   (check-entity-set
    (.getEntitiesInSignature o iri)
    iri)
   ;; single item in current or imports
   (check-entity-set
    (.getEntitiesInSignature o iri true)
    iri)
   ;; single item in anything we know about
   ;; perhaps this is not sure a good idea, since the result will depend on
   ;; loaded ontologies, which might change for different invocations.
   (check-entity-set
    (apply
     clojure.set/union
     (map #(.getEntitiesInSignature ^OWLOntology % iri true)
          (vals @ontology-for-namespace)))
    iri)))

(defdontfn entity-for-string
  "Returns the OWLObject for a given string.
See 'entity-for-iri' for more details. Attempts both ontology specific iri to name
conversion, and direct use of string as an IRI."
  [o string]
  (or (entity-for-iri o (iri-for-name o string))
      ;; string name somewhere?
      (entity-for-iri o (iri string))))

(defdontfn get-prefix
  "Returns the prefix for the given ontology, or the current ontology if none
is given."
  [^OWLOntology o]
  ;; my assumption here is that there will only ever be one prefix for a given
  ;; ontology. If not, it's all going to go wrong.
  (first
   (keys
    (.getPrefixName2PrefixMap
     (.asPrefixOWLOntologyFormat
      (.getOntologyFormat (owl-ontology-manager)
                                o))))))

(defdontfn save-ontology
  "Save the current 'ontology' in the file or `filename' if given.
If no ontology is given, use the current-ontology"
  ([o filename]
     (save-ontology o filename (ManchesterOWLSyntaxOntologyFormat.)
                    (str "## This file was created by Tawny-OWL\n"
                         "## It should not be edited by hand\n" )))
  ([o filename format]
     (save-ontology o filename format ""))
  ([^OWLOntology o ^String filename format prepend]
     (let [file (File. filename)
           output-stream (new FileOutputStream file)
           file-writer (new PrintWriter output-stream)
           ^OWLOntologyFormat
           this-format
           (cond
            (= format :rdf) (RDFXMLOntologyFormat.)
            (= format :omn) (ManchesterOWLSyntaxOntologyFormat.)
            (= format :owl) (OWLXMLOntologyFormat.)
            :else format)]
       (when (.isPrefixOWLOntologyFormat this-format)
         (doseq [ont (vals @ontology-for-namespace)
                 :when (get-prefix ont)]
           (.setPrefix
            (.asPrefixOWLOntologyFormat this-format) (get-prefix ont)
            (str (get-iri ont) "#")))
         (.setPrefix (.asPrefixOWLOntologyFormat this-format) (get-prefix o)
                     (str (get-iri o) "#")))
       (.print file-writer prepend)
       (.flush file-writer)
       (.saveOntology (owl-ontology-manager) o
                      this-format output-stream))))

;;; Begin OWL entity guess/ensure
(derive ::class ::object)
(derive ::object-property ::object)
(derive ::object-property ::property)
(derive ::data-property ::property)
(derive ::data-property ::data)

(defmontfn guess-type
  "Guesses the type of the entity. Returns ::object, :data or :annotation or
nil where the type cannot be guessed. IllegalArgumentException is thrown for
arguments which make no sense (not an OWLObject, IRI, String or number).

What this means is, for a collection find the first entity for which we can
guess a type for. For an OWLClass, OWLIndividual, OWLDatatype or
OWLAnnotationProperty object return the appropriate value. For an IRI check
the current ontology, the current ontology with its import closure, and all
known ontologies with their import clojure. For a string convert to an IRI
using the current ontology rules, and check again. Finally, check convert to
an IRI with no transformation. nil is returned when the result is not clear.
"
  [o entity]
  (let [oneof? (fn[& rest]
                 (some
                  #(instance? % entity) rest))]
    (cond
     ;; it's a collection -- find the first entity
     (coll? entity)
     (some (partial guess-type o) entity)
     ;; return if individual, class, datatype
     (oneof?
      OWLClassExpression)
     ::class
     (oneof? OWLObjectPropertyExpression)
     ::object-property
     (oneof?
      OWLAnnotationProperty)
     ::annotation
     (oneof?
      OWLDataPropertyExpression)
     ::data-property
     (oneof?
      OWLDataRange)
     ::data
     ;; up to this point, o can be nil -- after this point, we need to know
     ;; the ontology we are searching in.
     ;; if an IRI, see if it is the current ontology
     (instance? IRI entity)
     (guess-type o (entity-for-iri o entity))
     ;; keyword -- these are builtin OWL2Datatypes
     (and (keyword? entity)
          (get owl2datatypes entity))
     ::data
     ;; string name in current ontology?
     (string? entity)
     (guess-type o (entity-for-string o entity))
     ;; owl individuals tell us nothing, cause we still don't know!
     (instance? OWLIndividual entity)
     nil
     (number? entity)
     nil
     ;; if we get nil, carry on, because we may be able to determine the type
     ;; from a later argument.
     (nil? entity)
     nil
     ;; probably it's something crazy here.
     :default
     (throw (IllegalArgumentException.
             (str "Cannot guess this type:" entity))))))

(defmontfn guess-individual-literal
  [o entity]
  (cond
   (coll? entity)
   (some (partial guess-individual-literal o) entity)
   (instance? OWLIndividual entity)
   ::individual
   (instance? OWLLiteral entity)
   ::literal
   (instance? IRI entity)
   (guess-individual-literal o
                             (entity-for-iri o entity))
   (string? entity)
   (if-let [owlentity (entity-for-string o entity)]
     (guess-individual-literal
      o owlentity)
     ::literal)
   (number? entity)
   ::literal
   (or (= true entity)
       (= false entity))
   ::literal
   :default
   (throw (IllegalArgumentException.
           (str "Cannot tell if this is individual or literal:" entity)))))

(defn-
  ^{:private true}
  ^OWLObjectProperty ensure-object-property
  "Ensures that the entity in question is an OWLObjectProperty
or throw an exception if it cannot be converted."
  [o prop]
  (cond
   (fn? prop)
   (ensure-object-property o (prop))
   (instance? OWLObjectPropertyExpression prop)
   prop
   (instance? IRI prop)
   (.getOWLObjectProperty (owl-data-factory) prop)
   (string? prop)
   (ensure-object-property o (iri-for-name o prop))
   :default
   (throw (IllegalArgumentException.
           (str "Expecting an object property. Got: " prop)))))

(defn- ensure-class-except [clz]
  (throw (IllegalArgumentException.
          (str "Expecting a class. Got: " clz))))

(defn- ^OWLClass ensure-class
  "If clz is a String return a class of with that name,
else if clz is a OWLClassExpression add that."
  [o clz]
  (cond
   (instance? org.semanticweb.owlapi.model.OWLClassExpression clz)
   clz
   (instance? IRI clz)
   (.getOWLClass (owl-data-factory) clz)
   (string? clz)
   (ensure-class o (iri-for-name o clz))
   (fn? clz)
   (try
     (ensure-class o (clz))
     (catch clojure.lang.ArityException e
       (ensure-class-except clz)))
   true (ensure-class-except clz)))

(defn-
  ^OWLDataProperty ensure-data-property
  "Ensures that 'property' is an data property,
converting it from a string or IRI if necessary."
  [o property]
  (cond
   (instance? OWLDataProperty property)
   property
   (instance? IRI property)
   (.getOWLDataProperty
    (owl-data-factory) property)
   (instance? String property)
   (ensure-data-property o
                         (iri-for-name o property))
   :default
   (throw (IllegalArgumentException.
           (format "Expecting an OWL data property: %s" property)))))

(defn-
  ^OWLPropertyExpression
  ensure-property
  "Ensures that the entity in question is an OWLPropertyExpression.
If prop is ambiguous (for example, a string or IRI that whose type has not
been previously defined) this will create an OWLObjectProperty rather than
an OWLDataProperty"
  [o prop]
  (let [type
        (or
          ;; guess the type -- if we can't then object-property it's because
          ;; we don't know and not because it's illegal
          (guess-type o prop)
          ::object-property)]
    (case type
      ::object-property
      (ensure-object-property o prop)
      ::data-property
      (ensure-data-property o prop))))

(defn- ^OWLDatatype ensure-datatype
  "Ensure that 'datatype' is an OWLDatatype. Will convert from an keyword for
  builtin datatypes."
  [o datatype]
  (cond
   (instance? OWLDatatype datatype)
   datatype
   (instance? org.semanticweb.owlapi.vocab.OWL2Datatype datatype)
   (.getDatatype ^org.semanticweb.owlapi.vocab.OWL2Datatype datatype (owl-data-factory))
   (keyword? datatype)
   (if-let [d (get owl2datatypes datatype)]
     (ensure-datatype o d)
     (throw (IllegalArgumentException.
             (str "Was expecting a datatype. Got " datatype "."))))
   (instance? IRI datatype)
   (.getOWLDatatype (owl-data-factory) ^IRI datatype)
   :default
   (throw (IllegalArgumentException.
           (str "Was expecting a datatype. Got " datatype ".")))))

(defn- ^org.semanticweb.owlapi.model.OWLDataRange ensure-data-range
  "Ensure that 'data-range' is a OWLDataRange either directly or
as a datatype."
  [o data-range]
  (cond
   (instance? org.semanticweb.owlapi.model.OWLDataRange data-range)
   data-range
   :default
   (ensure-datatype o data-range)))

(defn- ^OWLIndividual ensure-individual
  "Returns an INDIVIDUAL.
If INDIVIDUAL is an OWLIndividual return individual, else
interpret this as a string and create a new OWLIndividual."
  [o individual]
  (cond (instance? org.semanticweb.owlapi.model.OWLIndividual individual)
        individual
        (instance? IRI individual)
        (.getOWLNamedIndividual (owl-data-factory)
                                individual)
        (string? individual)
        (ensure-individual o (iri-for-name o individual))
        :default
        (throw (IllegalArgumentException.
                (str "Expecting an Individual. Got: " individual)))))


;; Begin add-owl objects
(defbdontfn
  add-superclass
  {:doc "Adds one or more superclasses to name in ontology."
   :arglists '([name & superclass] [ontology name & superclass])}
  [o name superclass]
  (add-axiom o
             (.getOWLSubClassOfAxiom
              (owl-data-factory)
              (ensure-class o name)
              (ensure-class o superclass))))

(defbdontfn
  add-subclass
  {:doc "Adds one or more subclasses to name in ontology."
   :arglists '([name & subclass] [ontology name & subclass])}
  [o name subclass]
  (add-axiom o
             (.getOWLSubClassOfAxiom
              (owl-data-factory)
              (ensure-class o subclass)
              (ensure-class o name))))

(def deprecated-add-subclass
  ^{:doc "This maintains the functionality of the old add-subclass function
which actually added superclasses. The new add-subclass does the
opposite of this."
    :deprecated "1.1"
    :arglists '([name & superclass] [ontology name & superclass])}
  #'add-superclass)

(defbdontfn add-equivalent
  {:doc "Adds an equivalent axiom to the ontology."
   :arglists '([name equivalent] [ontology name equivalent])
   }
  [o name equivalent]
  (add-axiom o
             (.getOWLEquivalentClassesAxiom
              (owl-data-factory)
              (ensure-class o name)
              (ensure-class o equivalent))))

(defbdontfn add-disjoint
  {:doc "Adds a disjoint axiom to the ontology."
   :arglists '([name disjoint] [ontology name disjoint])}
  [o name disjoint]
  (add-axiom
   o
   (.getOWLDisjointClassesAxiom
    (owl-data-factory)
    ;; array class expressions!
    ^"[Lorg.semanticweb.owlapi.model.OWLClassExpression;"
    (into-array OWLClassExpression
                [(ensure-class o name)
                 (ensure-class o disjoint)]))))

(defdontfn add-disjoint-union
  "Adds a disjoint union axiom to all subclasses."
  [o clazz subclasses]
  (let [ensured-subclasses
        (util/domap #(ensure-class o %) subclasses)
        ]
    (list
     (add-axiom o
                (.getOWLDisjointUnionAxiom
                 (owl-data-factory)
                 (ensure-class o clazz)
                 (java.util.HashSet. ^java.util.Collection ensured-subclasses))))))

(defdontfn add-class
  "Adds a class to the ontology."
  [o name]
  (add-axiom o
             (.getOWLDeclarationAxiom
              (owl-data-factory)
              (ensure-class o name))))

;; a class can have only a single haskey, so ain't no point broadcasting this.
(defdontfn add-has-key
  "Adds a has-key to the class."
  [o class propertylist]
  ;; nil or empty list safe
  (if (seq propertylist)
    (let [type (guess-type o propertylist)
          propertylist
          (cond
           (isa? type ::object)
           (map (partial ensure-object-property o) propertylist)
           (isa? type ::data)
           (map (partial ensure-data-property o) propertylist)
           :default
           (throw
            (IllegalArgumentException.
             "Unable to determine type of property")))]
      (add-axiom o
                 (.getOWLHasKeyAxiom (owl-data-factory)
                                     (ensure-class o class)
                                     ^"[Lorg.semanticweb.owlapi.model.OWLPropertyExpression;"
                                     (into-array
                                      org.semanticweb.owlapi.model.OWLPropertyExpression
                                      propertylist))))))

(defbdontfn add-domain
  "Adds all the entities in domainlist as domains to a property."
  [o property domain]
  (add-axiom o
             (.getOWLObjectPropertyDomainAxiom
              (owl-data-factory)
              (ensure-object-property o property)
              (ensure-class o domain))))

(defbdontfn add-range
  "Adds all the entities in rangelist as range to a property."
  [o property range]
  (add-axiom o
             (.getOWLObjectPropertyRangeAxiom
              (owl-data-factory)
              (ensure-object-property o property)
              (ensure-class o range))))

(defbdontfn add-inverse
  "Adds all the entities in inverselist as inverses to a property."
  [o property inverse]
  (add-axiom o
             (.getOWLInverseObjectPropertiesAxiom
              (owl-data-factory)
              (ensure-object-property o property)
              (ensure-object-property o inverse))))

(defmontfn inverse
  "Creates an object inverse of expression."
  [o property]
  (.getOWLObjectInverseOf
   (owl-data-factory)
   (ensure-object-property o property)))

(defbdontfn add-superproperty
  "Adds all items in superpropertylist to property as
a superproperty."
  [o property superproperty]
  (add-axiom o
             (.getOWLSubObjectPropertyOfAxiom
              (owl-data-factory)
              (ensure-object-property o property)
              (ensure-object-property o superproperty))))

(defbdontfn add-subproperty
  "Adds all items in superpropertylist to property as
a superproperty."
  [o property subproperty]
  (add-axiom o
             (.getOWLSubObjectPropertyOfAxiom
              (owl-data-factory)
              (ensure-object-property o subproperty)
              (ensure-object-property o property))))


(def ^{:deprecated "1.1"
       :doc "This is the same as add-superproperty but marked as deprecated
and used as the handler for :subproperty."
       } deprecated-add-superproperty
  add-superproperty)


;; broadcasts specially
(defdontfn add-subchain
  "Adds a property chain to property."
  [o property subpropertylist]
  (when subpropertylist
    (let [property (ensure-object-property o property)
          lists (filter sequential? subpropertylist)
          properties (filter (comp not sequential?) subpropertylist)
          ]
      (list
       ;; add individual entities are a single chain
       (add-axiom o
                  (.getOWLSubPropertyChainOfAxiom
                   (owl-data-factory)
                   (map (partial ensure-object-property o) properties)
                   property))
       ;; add sequential entities as a chain in their own right
       (map (partial add-subchain
                     o property)
            lists)))))

(def
  ^{:doc "This is the same as add-subchain, but marked as deprecated
and used as the handler for :subpropertychain."
    :deprecated "1.1"} deprecated-add-subpropertychain
  add-subchain)


(defbdontfn add-equivalent-property
  "Adds a equivalent data properties axiom."
  [o property equivalent]
  (add-axiom
   o (.getOWLEquivalentObjectPropertiesAxiom
      (owl-data-factory)
      (ensure-object-property o property)
      (ensure-object-property o equivalent))))

(defdontfn equivalent-properties
  "Adds properties as equivalent to the ontology."
  [o properties]
  (let [properties
        (map (partial
               ensure-object-property o) properties)]
    (add-axiom
     o (.getOWLEquivalentObjectPropertiesAxiom
        (owl-data-factory)
        ^"[Lorg.semanticweb.owlapi.model.OWLObjectPropertyExpression;"
        (into-array OWLObjectPropertyExpression
                    properties)))))

(defbdontfn add-disjoint-property
  "Adds a disjoint property axiom to the ontology"
  [o name disjoint]
  (add-axiom
   o
   (.getOWLDisjointObjectPropertiesAxiom
    (owl-data-factory)
    ^"[Lorg.semanticweb.owlapi.model.OWLObjectPropertyExpression;"
    (into-array OWLObjectPropertyExpression
                [(ensure-object-property o name)
                 (ensure-object-property o disjoint)]))))

(defdontfn disjoint-properties
  "Make all the properties in PROPERTIES disjoint."
  [o properties]
  (let [properties
        (doall
         (map (partial ensure-object-property o) properties))]
    (add-axiom
     o (.getOWLDisjointObjectPropertiesAxiom
        (owl-data-factory)
        ^"[Lorg.semanticweb.owlapi.model.OWLObjectPropertyExpression;"
        (into-array OWLObjectPropertyExpression
                    properties)))))

(def
  ^{:private true}
  charfuncs
  {:transitive #(.getOWLTransitiveObjectPropertyAxiom
                 ^OWLDataFactory %1 ^OWLObjectProperty %2)
   :functional #(.getOWLFunctionalObjectPropertyAxiom
                 ^OWLDataFactory %1 ^OWLObjectProperty %2)
   :inversefunctional #(.getOWLInverseFunctionalObjectPropertyAxiom
                        ^OWLDataFactory %1 ^OWLObjectProperty %2)
   :symmetric #(.getOWLSymmetricObjectPropertyAxiom
                ^OWLDataFactory %1 ^OWLObjectProperty %2)
   :asymmetric #(.getOWLAsymmetricObjectPropertyAxiom
                 ^OWLDataFactory %1 ^OWLObjectProperty %2)
   :irreflexive #(.getOWLIrreflexiveObjectPropertyAxiom
                  ^OWLDataFactory %1 ^OWLObjectProperty %2)
   :reflexive #(.getOWLReflexiveObjectPropertyAxiom
                ^OWLDataFactory %1 ^OWLObjectProperty %2)})

(defbdontfn add-characteristics
  "Add a list of characteristics to the property."
  [o property characteristic]
  (when-not (get charfuncs characteristic)
    (throw (IllegalArgumentException.
            "Characteristic is not recognised:" characteristic)))
  (add-axiom o
             ((get charfuncs characteristic)
              (owl-data-factory) (ensure-object-property o property))))

(def ^{:private true} object-property-handlers
  {
   :domain add-domain
   :range add-range
   :inverse add-inverse
   :sub add-subproperty
   :super add-superproperty
   :subproperty deprecated-add-superproperty
   :characteristic add-characteristics
   :subchain add-subchain
   :subpropertychain deprecated-add-subpropertychain
   :disjoint add-disjoint-property
   :equivalent add-equivalent-property
   :annotation add-annotation
   :label add-label
   :comment add-comment})

;; object properties
(defdontfn object-property-explicit
  "Returns an object-property. This requires an hash with a list
value for each frame."
  [o name frames]
  (let [o (or (first (get frames :ontology))
              o)
        property (ensure-object-property o name)]
    (do
      ;; add the property
      (add-axiom o
                 (.getOWLDeclarationAxiom
                  (owl-data-factory) property))
      ;; add a name annotation
      (add-a-name-annotation o property name)
      ;; apply the handlers
      (doseq [[k f] object-property-handlers
              :when (get frames k)]
        (f o property (get frames k))))
    property))

(defdontfn object-property
  "Returns a new object property in the current ontology."
  [o name & frames]
  (let [keys (list* :ontology (keys object-property-handlers))]
    (object-property-explicit
     o name
     (util/check-keys
      (util/hashify-at keys frames)
      keys))))

(defentity defoproperty
  "Defines a new object property in the current ontology."
  'tawny.owl/object-property)

(comment
  (defmacro defoproperty
    "Defines a new object property in the current ontology."
    [property & frames]
    `(let [property-name# (name '~property)
           property# (tawny.owl/object-property property-name# ~@frames)]
       (intern-owl ~property property#))))

(defmontfn
  guess-type-args
  {:doc  "Broadcasting version of guess-type"
   :private true}
  [o & args]
  (guess-type o args))

(defmontfn guess-individual-literal-args
  {:doc "Broadcasting version of guess-individual-literal"
   :private true}
  [o & args]
  (guess-individual-literal o args))

;; multi methods for overloaded entities. We guess the type of the arguments,
;; which can be (unambiguous) OWLObjects, potentially ambiguous IRIs or
;; strings. If we really can tell, we guess at objects because I like objects
;; better.
(defmulti owl-some
  "Returns an existential restriction with another class or a data range."
  #'guess-type-args)
(defmulti only
  "Returns a universal rescriction with another class or data range."
#'guess-type-args)

(defmulti some-only
  "Returns a list containing existential restrictions to each of the arguments,
and universal relationship to the union of each of the arguments."
  #'guess-type-args)

(defmulti owl-and
  "Returns an intersection restriction to all of the arguments."
  #'guess-type-args)

(defmulti owl-or
  "Returns an union restriction to all of the arguments."
  #'guess-type-args)

(defmulti exactly
  "Returns an exact cardinality restriction."
  #'guess-type-args)

(defmulti oneof
  "Returns a one-of restriction to the arguments of individuals or
data ranges."
  #'guess-individual-literal-args)

(defmulti at-least
  "Returns a minimum cardinality restriction."
  #'guess-type-args)

(defmulti at-most
  "Returns a maximum cardinality restriction."
  #'guess-type-args)

(defmulti has-value
  "Returns a has-value restriction."
  #'guess-type-args)

;; this is the outlier because it is also used for individuals, so is called
;; overloaded on arity
(defmulti
  ^{:private true
    :doc "Returns a data or object complement of restriction."}
  owl-not-one #'guess-type-args)

;; use declare here because I just don't want to owl-not later
(declare fact-not)

(defmontfn owl-not
  "Returns a complement of restriction or negative property assertion axiom."
  ([o entity]
     (owl-not-one o entity))
  ([o property entity]
     (fact-not o property entity)))

(defn guess-type-error
  "Throws an exception always"
  [& args]
  (throw (IllegalArgumentException.
          (str "Unable to determine the type of: " args))))

(defmethod owl-some nil [& rest]
  (apply guess-type-error rest))

(defmethod only nil [& rest]
  (apply guess-type-error rest))

(defmethod some-only nil [& rest]
  (apply guess-type-error rest))

(defmethod owl-and nil [& rest]
  (apply guess-type-error rest))

(defmethod owl-or nil [& rest]
  (apply guess-type-error rest))

(defmethod owl-not-one nil [& rest]
  (apply guess-type-error rest))

(defmethod exactly nil [& rest]
  (apply guess-type-error rest))

(defmethod at-least nil [& rest]
  (apply guess-type-error rest))

(defmethod at-most nil [& rest]
  (apply guess-type-error rest))

(defmethod has-value nil [& rest]
  (apply guess-type-error rest))

;; short cuts for the terminally lazy. Still prefix!
(def && owl-and)
(def || owl-or)
(def ! owl-not)

;; "long cuts" for consistency with some
(def owl-only only)

(defbmontfn object-some
  {:doc "Returns an OWL some values from restriction."
   :arglists '([property & clazzes] [ontology property & clazzes])}
  [o property class]
  (.getOWLObjectSomeValuesFrom
   (owl-data-factory)
   (ensure-object-property o property)
   (ensure-class o class)))

;; use add method because we want object-some to have independent life!
(defmethod owl-some ::object [& rest]
  (apply object-some rest))

(defbmontfn object-only
  {:doc "Returns an OWL all values from restriction."
   :arglists '([property & clazzes] [ontology property & clazzes])}
  [o property class]
  (.getOWLObjectAllValuesFrom
   (owl-data-factory)
   (ensure-object-property o property)
   (ensure-class o class)))

(defmethod only ::object [& rest]
  (apply object-only rest))

;; union, intersection
(defmontfn object-and
  "Returns an OWL intersection of restriction."
  [o & classes]
  (let [classes (flatten classes)]
    (when (> 1 (count classes))
      (throw (IllegalArgumentException. "owl-and must have at least two classes")))

    (.getOWLObjectIntersectionOf
     (owl-data-factory)
     (java.util.HashSet.
      (util/domap
       #(ensure-class o %)
       ;; flatten list for things like owl-some which return lists
       classes)))))

;; add to multi method
(defmethod owl-and ::object [& rest]
  (apply object-and rest))

(defmontfn object-or
  "Returns an OWL union of restriction."
  [o & classes]
  (let [classes (flatten classes)]
    (when (> 1 (count classes))
      (throw (IllegalArgumentException. "owl-or must have at least two classes")))

    (.getOWLObjectUnionOf
     (owl-data-factory)
     (java.util.HashSet.
      (util/domap #(ensure-class o %)
                  (flatten classes))))))

(defmethod owl-or ::object [& rest]
  (apply object-or rest))

;; lots of restrictions return a list which can be of size one. so all these
;; functions take a list but ensure that it is of size one.
(defmontfn object-not
  "Returns an OWL complement of restriction."
  [o & class]
  {:pre [(= 1
            (count (flatten class)))]}
  (.getOWLObjectComplementOf
   (owl-data-factory)
   (ensure-class o (first (flatten class)))))

(defmethod owl-not-one ::object [& rest]
  (apply object-not rest))

(defmontfn object-some-only
  "Returns an restriction combines the OWL some values from and
all values from restrictions."
  [o property & classes]
  (list
   (apply
    object-some
    o
    property classes)
   (object-only o property
                (apply object-or o classes))))

(defmethod some-only ::object [& rest]
  (apply object-some-only rest))

;; cardinality
(defmacro with-optional-class
  "Calls form as is, or adds n to it iff n is not nil.
n is evaluated only once, so can have side effects."
  [o n form]
  (let [nn (gensym "n")]
    `(let [~nn (first (flatten ~n))]
       (if (nil? ~nn)
         ~form
         ~(concat
           form
           `((ensure-class ~o ~nn)))))))


(defmontfn object-at-least
  "Returns an OWL at-least cardinality restriction."
  [o cardinality property & class]
  {:pre [(> 2
            (count (flatten class)))]}
  ;; we only take a single class here, but it could be in any form because of
  ;; the broadcasting functions
  (with-optional-class
    o class
    (.getOWLObjectMinCardinality
     (owl-data-factory) cardinality
     (ensure-object-property o property))))

(defmethod at-least ::object [& rest]
  (apply object-at-least rest))

(defmontfn object-at-most
  "Returns an OWL at-most cardinality restriction."
  [o cardinality property & class]
  {:pre [(> 2
            (count (flatten class)))]}
  (with-optional-class o class
    (.getOWLObjectMaxCardinality
     (owl-data-factory) cardinality
     (ensure-object-property o property))))

(defmethod at-most ::object [& rest]
  (apply object-at-most rest))

(defmontfn object-exactly
  "Returns an OWL exact cardinality restriction."
  [o cardinality property & class]
  {:pre [(and
          (number? cardinality)
          (> 2
             (count (flatten class))))]}
  (with-optional-class o class
    (.getOWLObjectExactCardinality
     (owl-data-factory) cardinality
     (ensure-object-property o property))))

(defmethod exactly ::object [& rest]
  (apply object-exactly rest))

(defmontfn object-oneof
  "Returns an OWL one of property restriction."
  [o & individuals]
  (.getOWLObjectOneOf
   (owl-data-factory)
   (java.util.HashSet.
    (util/domap (partial ensure-individual o)
         (flatten individuals)))))

(defmethod oneof ::individual [& rest]
  (apply object-oneof rest))

(defmontfn object-has-value
  "Adds an OWL has-value restriction."
  [o property individual]
  (.getOWLObjectHasValue (owl-data-factory)
                          (ensure-object-property o property)
                          (ensure-individual o individual)))

(defmethod has-value ::object [& rest]
  (apply object-has-value rest))

(defmontfn has-self
  "Returns an OWL has self restriction."
  [o property]
  (.getOWLObjectHasSelf (owl-data-factory)
                        (ensure-object-property o property)))

(def
  ^{:private true} owl-class-handlers
  {:subclass deprecated-add-subclass
   :sub add-subclass
   :super add-superclass
   :equivalent add-equivalent
   :disjoint add-disjoint
   :annotation add-annotation
   :haskey add-has-key
   :comment add-comment
   :label add-label})

(defdontfn owl-class-explicit
  "Creates a class in the current ontology.
Frames is a map, keyed on the frame name, value a list of items (of other
lists) containing classes. This function has a rigid syntax, and the more
flexible 'owl-class' is normally preferred. However, this function should be
slightly faster.
"
  [o name frames]
  (let [class (ensure-class o name)]
    ;; add the class
    (add-class o class)
    ;; add an name annotation
    (add-a-name-annotation o class name)
    ;; apply the handlers to the frames
    (doseq [[k f] owl-class-handlers
            :when (get frames k)]
      (f o class (get frames k)))
    ;; return the class object
    class))

(defdontfn owl-class
  "Creates a new class in the current ontology. See 'defclass' for
full details."
  [o name & frames]
  (owl-class-explicit
   o name
   (util/check-keys
    (util/hashify frames)
    (list*
     :ontology :name
     (keys owl-class-handlers)))))

(defentity defclass
  "Define a new class. Accepts a set number of frames, each marked
by a keyword :subclass, :equivalent, :annotation, :name, :comment,
:label or :disjoint. Each frame can contain an item, a list of items or any
combination of the two. The class object is stored in a var called classname."
  'tawny.owl/owl-class)

(comment
  (defmacro defclass
    "Define a new class. Accepts a set number of frames, each marked
by a keyword :subclass, :equivalent, :annotation, :name, :comment,
:label or :disjoint. Each frame can contain an item, a list of items or any
combination of the two. The class object is stored in a var called classname."
    [classname & frames]
    `(let [string-name# (name '~classname)
           class# (tawny.owl/owl-class string-name# ~@frames)]
       (intern-owl ~classname class#))))

(defdontfn disjoint-classes
  "Makes all elements in list disjoint.
All arguments must of an instance of OWLClassExpression"
  [o list]
  {:pre [(sequential? list)
         (> (count list) 1)]}
  (let [classlist
        (util/domap
         (fn [x]
           (ensure-class o x))
         list)]
    (add-axiom o
               (.getOWLDisjointClassesAxiom
                (owl-data-factory)
                ^"[Lorg.semanticweb.owlapi.model.OWLClassExpression;"
                (into-array OWLClassExpression
                            classlist)))))

(defdontfn equivalent-classes
  "Makes all elements in list equivalent.
All arguments must of an instance of OWLClassExpression"
  [o list]
  {:pre [(sequential? list)
         (> (count list) 1)]}
  (let [classlist
        (doall
         (map
          (fn [x]
            (ensure-class o x))
          list))]
    (add-axiom o
               (.getOWLEquivalentClassesAxiom
                (owl-data-factory)
                ^"[Lorg.semanticweb.owlapi.model.OWLClassExpression;"
                (into-array OWLClassExpression
                            classlist)))))

(defbdontfn add-type
  {:doc "Adds CLAZZES as a type to individual to current ontology
or ONTOLOGY if present."
   :arglists '([individual & clazzes] [o individual & clazzes])}
  [o individual clazz]
  (add-axiom o
             (.getOWLClassAssertionAxiom
              (owl-data-factory)
              (ensure-class o clazz)
              individual)))

(defbdontfn add-fact
  {:doc "Add FACTS to an INDIVIDUAL in the current ontology or
  ONTOLOGY if present. Facts are produced with `fact' and `fact-not'."
   :arglists '([individual & facts] [ontology individual & facts])}
  [o individual fact]
  (add-axiom o
             (fact individual)))

(defmulti get-fact guess-type-args)
(defmulti get-fact-not guess-type-args)

(defmontfn fact
  "Returns a fact assertion a relation by PROPERTY which can be
either an object or data property toward either an individual or literal
TO. This is the same as the function `is'."
  [o property to]
  (fn fact [from]
    (get-fact o property from to)))

(def ^{:doc "Returns a fact assertion a relation by PROPERTY which can be
either an object or data property toward either an individual or literal
TO"}
  is
  fact)

(defmontfn fact-not
  "Returns a fact asserting the lack of a relationship along PROPERTY
toward an either an individual or literal TO."
  [o property to]
  (fn fact-not [from]
    (get-fact-not o property from to)))

(defmontfn object-get-fact
  "Returns an OWL Object property assertion axiom."
  [_ property from to]
  (.getOWLObjectPropertyAssertionAxiom
   (owl-data-factory)
   property from to))

(defmethod get-fact ::object [& rest]
  (apply object-get-fact rest))

(defmontfn object-get-fact-not
  "Returns a negative OWL Object property assertion axiom."
  [_ property from to]
  (.getOWLNegativeObjectPropertyAssertionAxiom
   (owl-data-factory)
   property from to))

(defmethod get-fact-not ::object [& rest]
  (apply object-get-fact-not rest))

(defdontfn
  add-same
  {:doc "Adds all arguments as the same individual to the current ontology
or to ONTOLOGY if present."
   :arglists '([ontology & individuals] [& individuals])}
  [o & individuals]
  (let [individuals (filter (comp not nil?) (flatten individuals))]
    (when individuals
      (add-axiom o
                 (.getOWLSameIndividualAxiom
                  (owl-data-factory)
                  ^java.util.Set
                  (set individuals))))))

(defmontfn add-different
  {:doc "Adds all arguments as different individuals to the current
  ontology unless first arg is an ontology in which case this is used"}
  [o & individuals]
  (let [individuals (filter (comp not nil?) (flatten individuals))]
    (when individuals
      (add-axiom o
                 (.getOWLDifferentIndividualsAxiom
                  (owl-data-factory)
                  ^java.util.Set
                  (set individuals))))))


;; need to support all the different frames here...
;; need to use hashify -- need to convert to handlers
(def
  ^{:private true}
  individual-handlers
  {:type add-type
   :fact add-fact
   :same add-same
   :different add-different})

(defdontfn individual-explicit
  "Returns a new individual."
  [o name frames]
  (let [hframes
        (util/check-keys
         (util/hashify frames)
         [:type :fact :same :different :ontology])
        o (or (first (:ontology hframes))
              o)
        individual (ensure-individual o name)]
    (add-axiom o
               (.getOWLDeclarationAxiom (owl-data-factory) individual))
    (add-a-name-annotation o individual name)
    (doseq [[k f] individual-handlers
            :when (get frames k)]
      (f o individual (get frames k)))
    individual))

(defdontfn individual
  [o name & frames]
  (individual-explicit
   o name
   (util/check-keys
    (util/hashify frames)
    (list* :ontology
           (keys individual-handlers)))))

(defentity defindividual
  "Declare a new individual"
  'tawny.owl/individual)

(comment
  (defmacro defindividual
    "Declare a new individual."
    [individualname & frames]
    `(let [string-name# (name '~individualname)
           individual# (tawny.owl/individual string-name# ~@frames)]
       (intern-owl ~individualname individual#))))

(load "owl_data")

(defn- var-get-maybe
  "Given a var return it's value, given a value return the value."
  [var-maybe]
  (if (var? var-maybe)
    (var-get var-maybe)
    var-maybe))

(defdontfn as-disjoint
  {:doc "All entities are declared as disjoint. Entities may be
any structure and may also be a var. See also 'as-subclasses'."
   :arglists '([ontology & entities] [& entities])}
  [o & entities]
  (let [entities
        (map var-get-maybe (flatten entities))]
    (case
        (apply guess-type-args o
               (map var-get-maybe
                    (flatten
                     entities)))
      ::class
      (disjoint-classes o entities)
      ::object-property
      (disjoint-properties o entities)
      ::data-property
      (disjoint-data-properties o entities)
      (throw (IllegalArgumentException.
              "Unable to determine the type of entities.")))))

(defdontfn as-equivalent
  "Declare the properties or classes as disjoint."
  [o & entities]
  (let [entities
        (map var-get-maybe (flatten entities))]
    (case
        (apply guess-type-args o
               (map var-get-maybe
                    (flatten
                     entities)))
      ::class
      (equivalent-classes o entities)
      ::object-property
      (equivalent-properties o entities)
      ::data-property
      (equivalent-data-properties o entities)
      (throw (IllegalArgumentException.
              "Unable to determine the type of entities.")))))

(defdontfn as-inverse
  {:doc "Declare the two properties as inverse"
   :arglist '([ontology prop1 prop2] [prop1 prop2])}
  [o p1 p2]
  (add-inverse o
               (var-get-maybe p1)
               (var-get-maybe p2)))

(defdontfn
  as-subclasses
  {:doc "All classes are given the superclass.
The first item may be an ontology, followed by options.

:disjoint also sets the class disjoint.
:cover also makes the subclasses cover the superclass."
   :arglists '([ontology superclass options & classes]
                 [superclass options & classes]
                   [superclass & classes])}
  [o superclass & rest]
  (let [options (set (take-while keyword? rest))
        subclasses
        (map
         var-get-maybe
         (flatten (drop-while keyword? rest)))]
    ;; first we deal with subclasses
    (add-subclass o superclass subclasses)
    (when
        (:disjoint options)
      (disjoint-classes o subclasses))
    (when (:cover options)
      (add-equivalent o superclass
                      (owl-or o subclasses)))))

(defdontfn
  as-disjoint-subclasses
  {:doc "Declare all subclasses as disjoint"}
  [o superclass & subclasses]
  (apply as-subclasses (list* o superclass :disjoint subclasses)))

;; hmmm, now how do we do the ontology thing here?
(defmacro declare-classes
  "Declares all the classes given in args. Any args including and following
the first keyword will be interpreted as frames for all the classes. Frame
args will be evaluated multiple times so should be side-effect free.

This is mostly useful for forward declarations.

See `defclassn' to define many classes with different frames.
"
  [& args]
  (let [nk (comp not keyword?)
        names (take-while nk args)
        frames (drop-while nk args)
        ]
    `(list
      ~@(map
         (fn [x#]
           `(defclass ~x# ~@frames))
         names))))

(defmacro defclassn
  "Defines many classes at once.

Each class and associated frames should be supplied as a vector.

See `declare-classes' where frames (or just default frames) are not needed.
"
  [& classes]
  `(list ~@(map
            (fn [x#]
              `(defclass ~@x#)) classes)))

;; tree recursing
(defn- recurse-ontology-tree
  "Recurse the ontology tree starting from class and calling
f to get the neighbours."
  [o f entity]
  (loop [entities #{}
         explored #{}
         frontier (f o entity)]
    (if (empty? frontier)
      entities
      (let [v (first frontier)
            neighbours (seq (f o v))]
        (recur
         (conj entities v)
         (into explored neighbours)
         (into (rest frontier) (remove explored neighbours)))))))

;; predicates
(defdontfn direct-superclasses
  "Returns the direct superclasses of name.
Name can be either a class or a string name. Returns a list of class
expressions."
  [^OWLOntology o name]
  (let [^OWLClass clz (ensure-class o name)]
    ;; general Class expressions return empty
    (if (instance? OWLClass clz)
      (.getSuperClasses clz o)
      ())))

(defdontfn superclasses
  "Return all superclasses of class.
class is not returned unless it is explicitly stated to be a
direct or indirect superclass of itself."
  [o class]
  (recurse-ontology-tree
   o direct-superclasses class))

(defdontfn superclass?
  "Returns true if name is asserted to be a superclass."
  [o name superclass]
  (let [namecls (ensure-class o name)
        superclasscls (ensure-class o superclass)]
    (some #(.equals superclasscls %) (superclasses o name))))

(defdontfn direct-subclasses
  "Returns the direct subclasses of name."
  [^OWLOntology o name]
  (let [clz (ensure-class o name)]
    (if (instance? OWLClass clz)
      (.getSubClasses (ensure-class o name)
                      o)
      ())))

(defdontfn subclasses
  "Return all subclasses of class."
  [o class]
  (recurse-ontology-tree
   o direct-subclasses class))

(defdontfn subclass?
  "Returns true if name has subclass as a subclass."
  [o name subclass]
  (let [namecls (ensure-class o name)
        subclasscls (ensure-class o subclass)]
    (some #(.equals subclasscls %) (subclasses o name))))

(defdontfn disjoint?
  "Returns t iff entities (classes or properties) are asserted to be
  disjoint."
  [^OWLOntology o a b]
  (let [type (guess-type-args o a b)]
    (cond
     (isa? type ::class)
     (contains?
      (.getDisjointClasses ^OWLClass a o)
      b)
     ;; works for either data or object properties
     (isa? type ::property)
     (contains?
      (.getDisjointProperties ^OWLProperty a o)
      b)
     :default
     (throw
      (IllegalArgumentException.
       "Cannot determine disjoint for this form of entity")))))

(defdontfn equivalent?
  "Returns t iff classes are asserted to be equivalent."
  [^OWLOntology o a b]
  (let [type (guess-type-args o a b)]
    (cond
     (isa? type ::class)
     (contains?
      (.getEquivalentClasses ^OWLClass a o) b)
     (isa? type ::property)
     (contains?
      (.getEquivalentProperties ^OWLProperty a o)
      b)
     :default
     (throw
      (IllegalArgumentException.
       "Cannot determine equivalence for this type of entity")))))

(defdontfn inverse?
  "Returns t iff properties are asserted to be inverse"
  [^OWLOntology o ^OWLObjectProperty p1 ^OWLObjectProperty p2]
  (contains?
   (.getInverses p1 o) p2))


(defdontfn direct-superproperties
  "Return all direct superproperties of property."
  [^OWLOntology o property]
  (.getSuperProperties
   (ensure-property o property) o))

(defdontfn superproperties
  "Return all superproperties of a property."
  [o property]
  (recurse-ontology-tree
   o direct-superproperties
   (ensure-property o property)))

(defdontfn superproperty?
  "Return true if superproperty is a superproperty of property."
  [o property superproperty]
  (some #(.equals
          (ensure-property o superproperty) %)
        (superproperties o property)))

(defdontfn direct-subproperties
  "Returns all direct subproperties of property."
  [^OWLOntology o
   property]
  (.getSubProperties
   (ensure-property o property) o))

(defdontfn subproperties
  "Returns all subproperties of property."
  [o property]
  (recurse-ontology-tree
   o direct-subproperties
   (ensure-property o property)))

(defdontfn subproperty?
  "Returns true if property is a subproperty of subproperty."
  [o property subproperty]
  (some #(.equals
          (ensure-property o subproperty) %)
        (subproperties o property)))

;; some test useful macros

;; currently doesn't support an ontology argument
;; modified from with-open
(defmacro with-probe-entities
  {:doc
   "Evaluate BODY with a number of entities defined. Then delete these entities
  from the ontology. BINDINGS are a vector with similar to let. The first
  argument should evaluate to the ontology, or the current ontology will be
  used. Statements inside bindings are evaluated with the current-ontology set
  to ONTOLOGY. Entities added to ONTOLOGY are removed from ONTOLOGY; so if
  they are added to a different ontology explicitly, they will remain there
  after the completion of this form."
   :arglists '([bindings & body] [ontology bindings & body])
   }

  [& args]
  (let [o (take-while #(not (vector? %)) args)
        o (or (first o) `(get-current-ontology))
        rst (drop-while #(not (vector? %)) args)
        bindings (first rst)
        body (rest rst)
        ]
    (when-not (vector? bindings)
      (IllegalArgumentException. "with-probe-entities requires a vector"))
    (when-not (even? (count bindings))
      (IllegalArgumentException.
       "with-probe-entities requires an even number of forms in binding vector"))
    (cond
     (zero? (count bindings))
     `(do
        ~@body)
     (symbol? (bindings 0))
     `(let ~(subvec bindings 0 2)
       (with-probe-entities ~o
         ~(subvec bindings 2)
         ;; try block just so we can use finally
         (try
           ~@body
           (finally
             (tawny.owl/remove-entity ~o ~(bindings 0))))))
     :else
     (throw (IllegalArgumentException.
             "with-probe-entities only allows Symbols in bindings")))))


(defmacro with-probe-axioms
  "Evaluate the body with a number of axioms. Then
delete these axioms from the ontology.

This is mostly useful for test cases. Axioms can be added, consistency
or inconsistency can be checked then removed, leaving the ontology
effectively unchanged."
  [& args]
  (let [o (take-while #(not (vector? %)) args)
        o (or (first o) `(get-current-ontology))
        rst (drop-while #(not (vector? %)) args)
        bindings (first rst)
        body (rest rst)
        ]
    (when-not (vector? bindings)
      (IllegalArgumentException. "with-probe-axioms requires a vector"))
    (when-not (even? (count bindings))
      (IllegalArgumentException.
       "with-probe-axioms requires an even number of forms in binding vector"))
    (cond
     (zero? (count bindings))
     `(do ~@body)
     (symbol? (bindings 0))
     `(let ~(subvec bindings 0 2)
       (with-probe-axioms ~o
         ~(subvec bindings 2)
         ;; try block just so we can use finally
         (try
           ~@body
           (finally
             (tawny.owl/remove-axiom ~o ~(bindings 0))))))
     :else
     (throw (IllegalArgumentException.
             "with-probe-axioms only allows Symbols in bindings")))))

(defn owl-thing
  "Returns OWL thing."
  []
  (.getOWLThing (owl-data-factory)))

(defn owl-nothing
  "Returns OWL nothing."
  []
  (.getOWLNothing (owl-data-factory)))

;; add a prefix or suffix to contained defclass
(defn- alter-symbol-after-def-form
  "Searches for a defclass form, then changes the symbol by applying f."
  [f x]
  (cond
   (and (seq? x)
        (= (first x) 'defclass))
   `(defclass ~(f (second x))
      ~@(drop 2 x))
   :default
   x))

(defn- prefix-symbol
  "Add a prefix to a symbol and return a new symbol."
  [prefix sym]
  (symbol
   (str prefix (name sym))))

(defn- suffix-symbol
  "Add a suffix to a symbol and return a new symbol"
  [suffix sym]
  (symbol
   (str (name sym) suffix)))

(defn- alter-all-symbol-after-def-form
  "Walk over forms and applies function
f to the symbol after a defclass"
  [f x]
  (clojure.walk/postwalk
   (partial alter-symbol-after-def-form f)
   x))

(defmacro with-prefix
  "Adds a prefix to all defclass macros in scope.
This is a convenience macro and is lexically scoped."
  [prefix & body]
  (let [newbody
        (alter-all-symbol-after-def-form
         (partial prefix-symbol prefix)
         body)]
    `(list ~@newbody)))

(defmacro with-suffix
  "Adds a suffix to all defclass macros in scope.
This is a convenience macro and is lexically scoped."
  [suffix & body]
  (let [newbody
        (alter-all-symbol-after-def-form
         (partial suffix-symbol suffix)
         body)]
    `(list ~@newbody)))

(defmulti refine
  "Takes an existing definition, adds it to the current ontology, and then
adds more frames. owlentity is the OWLEntity to be refined, and frames are the
additional frames. The keys to the frames must be appropriate for the type of
entity. See 'owl-class' or 'object-property' for more details.

This is useful for two main reasons. First, to build class definitions in two
places and add frames in both of these places. For simple forward declaration
'declare-classes' is better. The second is where the same class needs to
appear in two ontologies, but with more axioms in the second. This can enable,
for example, building two interlocking ontologies with different OWL profiles.
"
  (fn [owlentity & _] (class owlentity)))

(defmethod refine OWLClass [& args]
  (apply owl-class args))

(defmethod refine OWLObjectProperty [& args]
  (apply object-property args))

(defmethod refine OWLAnnotationProperty [& args]
  (apply annotation-property args))

(defmethod refine OWLDataProperty [& args]
  (apply datatype-property args))

(defmethod refine OWLDatatype [& args]
  (apply datatype args))

(defmethod refine OWLIndividual [& args]
  (apply individual args))

(defmacro defrefineto
  "Takes an existing definition, add more frames.
The first argument should be a symbol that will hold the

See also 'refine'.
"
  [symbol & args]
  `(def
     ~(with-meta symbol
        (assoc (meta symbol)
          :owl true))
     (tawny.owl/refine ~@args)))

(defmacro defrefine
  "Takes an existing definition, add more frames.

The first element should be a namespace qualified symbol. The
unqualified part of this will be used in the current namespace.

See also 'refine'
"
  [symb & args]
  (let [newsymbol#
        (symbol (name symb))]
    `(def
       ~(with-meta newsymbol#
          (assoc (meta newsymbol#)
            :owl true))
       (tawny.owl/refine ~symb ~@args))))

(defmacro defcopy
  "Takes an existing definition from another namespace and copies it into the
current namespace with no changes in semantics. This can be useful for
convenience, where one namespace should contain all the OWLObjects of
another, or for forward declaration, where entities will be refined later.

This does not add the existing definition to the current ontology. In most
cases this will have been imported."
  [symb & args]
  (let [newsymbol#
        (symbol (name symb))]
    `(def
       ~(with-meta newsymbol#
          (assoc (meta newsymbol#)
            :owl true))
       (var-get (var ~symb)))))
;; \end{code}

;; %%
;; %% Local Variables:
;; %% lentic-init: lentic-clojure-latex-init
;; %% End:
;; %%
