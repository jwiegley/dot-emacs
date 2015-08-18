;; \chapter{The Pizza Ontology}
;; \label{sec-5}

;; Now let us see what is ahppening now  let us see what is happenign.
;; Well this is running very slowly indeed now hello hello hello hellohel
;; \section{Introduction}
;; \label{sec-5-1}

;; In this section, we will create a Pizza ontology; we choose pizzas because
;; they are simple, well-understood and compositional (see
;; \href{http://robertdavidstevens.wordpress.com/2010/01/22/why-the-pizza-ontology-tutorial/}{here}
;; for more).

;; We have described ontologies more abstractly
;; \hyperref[what_is_an_ontology]{earlier}. More concretely, in this book, an
;; ontology is a computational object, which can contain a number of different
;; objects. These objects can be of several different kinds. The most (and
;; least!) important of these are \emph{individuals}. We say that these are the
;; most important because it is these individuals that are described and
;; constrained by the other objects. We say that they are the least important
;; because, in practice, many ontologies do not explicitly describe any
;; individuals at all.

;; If this seems perverse, consider a menu in a pizza shop. We might seem
;; an item described saying "Margherita\ldots{}.£5.50". The menu makes no
;; statements at all about an individual pizza. It is saying that any
;; margherita pizza produced in this resturant is going to (or already has)
;; cost £5.50. From the menu, we have no idea how many margherita pizzas
;; have been produced or have been consumed. But, menu is still useful. The
;; menu is comprehensive, tells you something about all the pizzas that
;; exist (at least in one resturant) and the different types of pizza. This
;; is different to the bill, which describes individuals -- the pizzas that
;; have actually been provided, how many pizza and how much they all cost.
;; In ontology terms, the menu describes the \textbf{classes}, the bill describes
;; individuals \footnote{The analogy between a pizza menu and an ontology
;; is not perfect. With pizza, people are generally happy with the classes
;; (i.e. the menu) and start arguing once about the individuals (i.e. the
;; bill); with ontologies it tends to be the other way around}. OWL
;; Ontologies built with Tawny-OWL \emph{can} describe either or both of these
;; entities but in most cases focus on classes.

;; \section{Defining Classes}
;; \label{sec-5-2}

;; We start with a namespace form. This declaration is slightly different from
;; that given in \hyperref[sec-4]{Getting Started}; it includes a |:use|
;; statement for |tawny.owl| and a statement declaring a new ontology.
;; First, consider the syntax of this example, because it is shared by all
;; statements in Tawny-OWL. All expresions in Clojure are delimited by |(|
;; and |)| and Tawny-OWL follows this rule. Next, we have a name for the
;; object we wish to create -- in this case an new ontology. This starts with
;; |def| to indicate that we also want to create a new symbol which we can
;; use to refer to this entity later.

;; Finally, come a set of arguments, introduced with \emph{keywords}. These all
;; end with a |:|. In this case, |:iri| introduces the main IRI for this
;; ontology, which is a global identifier, and finally a string which is
;; the actual value of that argument.

;; \begin{code}
(ns take.wing.the-pizza-ontology
  (:use [tawny.owl]
        [tawny.reasoner])
  (:refer-clojure :only []))

(defontology pizza :iri "http://purl.org/ontolink/take-wing/pizza")
;; \end{code}


;; The semantics of this statement are quite interesting. If we had created
;; a new database, by default, the database would be considered to be empty
;; -- that is there would be no individuals in it. With an ontology, the
;; opposite is true. By default, we assume that there could be any number
;; of individuals. As of yet, we just have not said anything about these
;; individuals.

;; Next, we declare two classes. A class is a set of individuals with
;; shared characteristics. For now, we create two classes, |Pizza| and
;; |PizzaComponent|. As with our |defontology| form, have a |def| form;
;; however, in this case, we do not use any arguments. The semantics of
;; these two statements are that, there is a class called |Pizza| and
;; another called |PizzaComponent| which individuals may be members of.
;; However, we know nothing at all about the relationship between an
;; individual |Pizza| and an individual |PizzaComponent|.


;; \begin{code}
(defclass Pizza)
(defclass PizzaComponent)
;; \end{code}

;; To build an accurate ontology, we may wish to describe this relationship
;; further. We might ask the question, can an individual be both a |Pizza|
;; and a |PizzaComponent| at the same time. The answer to this is no, but
;; currently our ontology does not state this. In OWL terminology, we wish
;; to say that these two classes are \emph{disjoint}. We can achieve this by
;; adding an |as-disjoint| statement.

;; \begin{code}
(as-disjoint Pizza PizzaComponent)
;; \end{code}

;; This works well, but is a little duplicative. If we add a new class
;; which we wish to also be disjoint, it must be added in two places.
;; Instead, it is possible to do both at once \footnote{In the source code,
;; generated from this book, we are now defining both classes twice, as we
;; have two |defclass| statements for each. This will actually work okay,
;; although it is not best practice as it is somewhat dependent on the
;; implementation details of the OWL API.}. This has the advantage of
;; grouping the two classes together in the file, as well as semantically,
;; which should make the source more future-proof; should we need new
;; classes, we will automatically make them disjoint as required.

;; \begin{code}
(as-disjoint
 (defclass Pizza)
 (defclass PizzaComponent))
;; \end{code}

;; The semantics of these statements are that our ontology may have any
;; number of individuals, some of which may be |Pizza|, some of which may
;; be |PizzaComponent|, but none of which can be both |Pizza| and
;; |PizzaComponent| at the same time. Before we added the |as-disjoints|
;; statement, we would have assumed that it was possible to be both.

;; As well as describing that two classes are different, we may also wish
;; to describe that they are closely related, or that they are
;; \emph{subclasses}. Where one class is a subclass of another, we are saying
;; that everything that is true of the superclass is also true of the
;; subclass. Or, in terms of individuals, that every individual of the
;; subclass is also an individual of the superclass.

;; Next, we add two more classes and include the statement that they have
;; |PizzaComponent| as a superclass. We do this by adding a |:super|
;; argument or \emph{frame} to our |defclass| statement. In Tawny-OWL the frames
;; can all be read in the same way. Read forwards, we can say |PizzaBase|
;; has a superclass |PizzaComponent|, or backwards |PizzaComponent| is a
;; superclass of |PizzaBase|. Earlier, we say the |:iri| frame for
;; |defontology| which is read similarly -- |pizza| has the given IRI.

;; As every individual of, for example, |PizzaBase| is |PizzaComponent|, and no
;; |PizzaComponent| individual can also be a |Pizza| this also implies that no
;; |PizzaBase| is a |Pizza|. In otherwords, the disjointness is inherited
;; \footnote{In this ontology, we use a naming scheme using CamelCase, upper case
;; names for classes and, later, lower case properties. As with many parts of
;; ontology development, opinions differ as to whether this is good. With
;; Tawny-OWL it has the fortuitous advantage that it syntax-highlights nicely,
;; because it looks like Java}

;; \begin{code}
(defclass PizzaBase
  :super PizzaComponent)
(defclass PizzaTopping
  :super PizzaComponent)
;; \end{code}

;; As with the disjoint statement, this is little long winded; we have to name
;; the |PizzaComponent| superclass twice. Tawny-OWL provides a short cut for
;; this, with the |as-subclasses| function.

;; \begin{code}
(as-subclasses
 PizzaComponent
 (defclass PizzaBase)
 (defclass PizzaTopping))
;; \end{code}

;; We are still not complete; we asked the question previously, can you be both a
;; |Pizza| and a |PizzaComponent|, to which the answer is no. We can apply the
;; same question, and get the same answer to a |PizzaBase| and |PizzaTopping|.
;; These two, therefore, should also be disjoint. However, we can make a stronger
;; statement still. The only kind of |PizzaComponent| that there are either a
;; |PizzaBase| or a |PizzaTopping|. We say that the |PizzaComponent| class is
;; \emph{covered} by its two subclasses. We can add both of these statements to the
;; ontology also.

;; \begin{code}
(as-subclasses
 PizzaComponent
 :disjoint :cover
 (defclass PizzaBase)
 (defclass PizzaTopping))
;; \end{code}

;; We now have the basic classes that we need to describe a pizza.


;; \section{Properties}
;; \label{sec-5-3}

;; Now, we wish to describe more about |Pizza|; in particular, we want to say
;; more about the relationship between |Pizza| and two |PizzaComponent| classes.
;; OWL provides a rich mechanism for describing relationships between individuals
;; and, in turn, how individuals of classes are related to each other. As well as
;; there being many different types of individuals, there are can be many
;; different types of relationships. It is the relationships to other classes or
;; individuals that allow us to describe classes, and it is for this reason that
;; the different types of relationships are called \emph{properties}.

;; A |Pizza| is built from one or more |PizzaComponent| individuals; we first
;; define two properties \footnote{Actually, two \emph{object} properties, hence
;; |defoproperty|. We can also define \emph{data} properties, which we will see later}
;; to relate these two together, which we call |hasComponent| and
;; |isComponentOf|. The semantics of this statement is to say that we now have
;; two properties that we can use between individuals.

;; \begin{code}
(defoproperty hasComponent)
(defoproperty isComponentOf)
;; \end{code}

;; As with classes, there is more that we can say about these properties. In this
;; case, the properties are natual opposites or inverses of each other. The
;; semantics of this statement is that for an individual |i| which |hasComponent|
;; |j|, we can say that |j| |isComponentOf| |i| also. 

;; \begin{code}
(as-inverse
 (defoproperty hasComponent)
 (defoproperty isComponentOf))
;; \end{code}

;; Again, the semantics here are actually between individuals, rather than
;; classes. This has an important consequence with the inverses. We might make
;; the statement that |Pizza| |hasComponent| |PizzaComponent|, but this does not
;; allow us to infer that |PizzaComponent| |isComponentOf| |Pizza|. Using an
;; every day analogy, just because all bicycles have wheels, we can not assume
;; that all wheels are parts of a bike; we \textbf{can} assume that where a bike has a
;; wheel, that wheel is part of a bike. This form of semantics is quite subtle,
;; and is an example of where statements made in OWL are saying less than most
;; people would assume footnote:[We will see examples of the opposite also --
;; statements which are stronger in OWL than the intuitive interpretation].
;; We now move on to describe the relationships between |Pizza| and both of
;; |PizzaBase| and |PizzaTopping|. For this, we will introduce three new parts of
;; OWL: subproperties, domain and range constraints and property characteristics,
;; which we define in Tawny-OWL as follows:

;; \begin{code}
(defoproperty hasTopping
  :super hasComponent
  :range PizzaTopping
  :domain Pizza)

(defoproperty hasBase
  :super hasComponent
  :characteristic :functional
  :range PizzaBase
  :domain Pizza)
;; \end{code}


;; First, we consider sub-properties, which are fairly analogous to sub-classes.
;; For example, if two individuals |i| and |j| are related so that
;; |i hasTopping j|, then it is also true that |i hasComponent j|.

;; Domain and range constraints describe the kind of entity that be at either end
;; of the property. So, for example, considering |hasTopping|, we say that the
;; domain is |Pizza|, so only instances of |Pizza| can have a topping, while the
;; range is |PizzaTopping| so only instances of |PizzaTopping| can be a topping. 

;; Finally, we introduce a \emph{characteristic}. OWL has quite a few different
;; characteristics which will introduce over time; in this case \emph{functional}
;; means means that there can be only one of these, so an individual has only a
;; single base.


;; \section{Populating the Ontology}
;; \label{sec-5-4}

;; We now have enough expressivity to describe quite a lot about pizzas. So, we
;; can now set about creating a larger set of toppings for our pizzas. First, we
;; describe some top level categories of types of topping. As before, we use
;; |as-subclasses| function and state further that all of these classes are
;; disjoint. Here, we have not used the |:cover| option. This is deliberate,
;; because we cannot be sure that these classes describe all of the different
;; toppings we might have; there might be toppings which fall into none of these
;; categories. 

;; \begin{code}
(as-subclasses
 PizzaTopping
 :disjoint
 (defclass CheeseTopping)
 (defclass FishTopping)
 (defclass FruitTopping)
 (defclass HerbSpiceTopping)
 (defclass MeatTopping)
 (defclass NutTopping)
 (defclass SauceTopping)
 (defclass VegetableTopping))
;; \end{code}

;; When defining a large number of classes at once, Tawny-OWL also offers a
;; shortcut, which we now use to define a large number of classes at once, which
;; is |declare-classes|. While this can be useful in a few specific
;; circumstances, these are quite limited because it does not allow addition of
;; any other attributes at the same time, and in particular labels which most
;; classes will need. In this case, we can generate a lot of classes in a short
;; space, which is useful in a tutorial document.

;; Neither |MeatTopping| nor |FruitTopping| are declared as |:disjoint| because
;; we have only put a single example.

;; \begin{code}
(as-subclasses
 CheeseTopping
 :disjoint

 (declare-classes
  GoatsCheeseTopping
  GorgonzolaTopping
  MozzarellaTopping
  ParmesanTopping))

(as-subclasses
 VegetableTopping
 :disjoint

 (declare-classes
  PepperTopping
  GarlicTopping
  PetitPoisTopping
  AsparagusTopping
  TomatoTopping
  ChilliPepperTopping))

(as-subclasses
 FruitTopping
 (defclass PineappleTopping))

(as-subclasses
 MeatTopping
 :disjoint
 (defclass HamTopping)
 (defclass PepperoniTopping))
;; \end{code}

;; \section{Describing a Pizza}
;; \label{sec-5-5}

;; And, now finally, we have the basic concepts that we need to build a pizza.
;; First, we start off with a generic description of a pizza; we have already
;; defined the class above, so we want to extend the definition rather than
;; create a new one. We can achieve this using the |class| function:

;; \begin{code}
(owl-class Pizza
           :super
           (owl-some hasTopping PizzaTopping)
           (owl-some hasBase PizzaBase))
;; \end{code}

;; This introduces several new features of Tawny-OWL:
;; \begin{itemize}
;; \item this use of |class| requires that |Pizza| already be defined. In other
;; words, we are extending an existing definition. If |Pizza| is not deined,
;; this form will crash.
;; \item a new function |some|
;; \item we create out first \emph{unnamed} classes from a class expression -- in this
;; case |(owl-some hasTopping PizzaTopping)|.
;; \end{itemize}

;; The semantics of the last two of these are a little complex. Like a named
;; class (all of those we have seen so far), an unnamed class defines a set of
;; individuals, but it does so by combining other parts of the ontology. The
;; |owl-some| restriction describes a class of individuals with at least one
;; relationship of a particular type. So
;; |(owl-some hasTopping PizzaTopping)| describes the set of all individuals
;; related by the |hasTopping| relationship to at least one
;; |PizzaTopping|. Or alternatively, each |Pizza| must have a
;; |PizzaTopping|. Or, alternatively again, for each |Pizza| there must
;; exist one |PizzaTopping|; it is for this reason that this form of class
;; is also known as an \emph{existential restriction}.

;; We combine the two statements to say that a |Pizza| must have at least one
;; base and at least one topping. Actually, we earlier defined |hasBase| with the
;; |:functional| characteristic, so together this says that a |Pizza| must have
;; exactly one base.

;; Finally, we can build a specific pizza, and we start with one of the simplest
;; pizza, that is the margherita. This has two toppings, mozzarella and tomato.
;; The definition for this is as follows:

;; \begin{code}
(defclass MargheritaPizza
  :super
  Pizza
  (owl-some hasTopping MozzarellaTopping)
  (owl-some hasTopping TomatoTopping)
  (only hasTopping (owl-or MozzarellaTopping TomatoTopping)))
;; \end{code}

;; The first part of this definition is similar to |Pizza|. It says that a
;; |MargheritaPizza| is a |Pizza| with two toppings, mozzarella and tomato. The
;; second part of the definition adds two new features of Tawny-OWL:

;; \begin{itemize}
;; \item |only| a new function which returns a \emph{universal restriction}
;; \item |owl-or| which returns a \emph{union restriction}
;; \end{itemize}

;; The |owl-or| statement defines the set of individuals that is either
;; |MozzarellaTopping| or |TomatoTopping|. The |only| statement
;; defines the set of individuals whose toppings are either
;; |MozzarellaTopping| or |TomatoTopping|. One important sting in the
;; tail of |only| is that it does \textbf{NOT} state that these individuals
;; have any toppings at all. So |(only hasTopping MozzarellaTopping)| would
;; cover a |Pizza| with only |MozzarellaTopping|, but also many other
;; things, including things which are not |Pizza| at all. Logically, this
;; makes sense, but it is counter-intuitive \footnote{Except to logicians,
;;   obviously, to whom it all makes perfect sense.}.

;; For completeness, we also define |HawaiianPizza| \footnote{Pizza names are, sadly,
;; not standardized between countries or resturants, so I've picked on which is
;; quite widely known. Apologies to any Italian readers for this and any other
;; culinary disasters which this book implies really are pizza.}.

;; \begin{code}
(defclass HawaiianPizza
  :super
  Pizza
  (owl-some hasTopping MozzarellaTopping)
  (owl-some hasTopping TomatoTopping)
  (owl-some hasTopping HamTopping)
  (owl-some hasTopping PineappleTopping)
  (only hasTopping
        (owl-or MozzarellaTopping TomatoTopping HamTopping PineappleTopping)))
;; \end{code}

;; We can now check that this works as expected by using the |subclass?| and
;; |subclasses| functions at the REPL.

;; \begin{verbatim}
;; take.wing.the-pizza-ontology> (subclass? Pizza MargheritaPizza)
;; true
;; take.wing.the-pizza-ontology> (subclasses Pizza)
;; #{#<OWLClassImpl <http://purl.org/ontolink/take-wing/pizza#HawaiianPizza>>
;;   #<OWLClassImpl <http://purl.org/ontolink/take-wing/pizza#MargheritaPizza>>}
;; \end{verbatim}

;; \section{A simple pattern}
;; \label{sec-5-6}

;; The last definition is rather unsatisfying for two reasons. Firstly, the
;; multiple uses of |(owl-some hasTopping)| and secondly because the toppings are
;; duplicated between the universal and existential restrictions. Two features of
;; Tawny-OWL enable us to work around these problems. 

;; Firstly, the |owl-some| function is \emph{variadic} and take a single property but any
;; number of classes. We use this feature to shorten the definition of
;; |AmericanPizza|. 

;; \begin{code}
(defclass AmericanPizza
  :super
  Pizza
  (owl-some hasTopping MozzarellaTopping
            TomatoTopping PepperoniTopping)
  (only hasTopping (owl-or MozzarellaTopping TomatoTopping PepperoniTopping)))
;; \end{code}

;; The single |some| function call here expands to three existential
;; restrictions, each of which becomes a super class of |AmericanPizza| --
;; mirroring the definition of |HawaiianPizza|.

;; This definition, however, still leaves the duplication between the two sets of
;; restrictions. This pattern is frequent enough that Tawny-OWL provides special
;; support for it in the form of the |some-only| function, which we use to define
;; the next pizza.

;; \begin{code}
(defclass AmericanHotPizza
  :super
  Pizza
  (some-only hasTopping MozzarellaTopping TomatoTopping
             PepperoniTopping ChilliPepperTopping))
;; \end{code}

;; The |some-only| function is Tawny-OWL's implementation of the \emph{closure} axiom.
;; Similarly, the use of |:cover| described earlier implements the \emph{covering}
;; axiom. These are the only two patterns which are directly supported by the
;; core of Tawny-OWL (i.e. the namespace |tawny.owl|). In later sections, though,
;; we will see how to exploit the programmatic nature of Tawny-OWL to build
;; arbitrary new patterns for yourself.


;; \section{Defined Classes}
;; \label{sec-5-7}
;; \label{defined}

;; So far all of the classes that we have written are \emph{primitive}. Rather than a
;; statement about complexity, this means that as they stand, they cannot be used
;; to infer new facts. So, for example, we know that a individual
;; |MargheritaPizza| will have a |MozzarellaTopping| and a |TomatoTopping|, but
;; given an arbitrary pizza we cannot determine whether it is a margherita. Or,
;; mozzarella and tomato toppings are \emph{necessary} for a margherita, but they are
;; not sufficient.

;; Defined classes allow us to take advantage of the power of computational
;; reasoning. Let us try a simple example:

;; \begin{code}
(defclass VegetarianPizza
  :equivalent
  (owl-and Pizza
           (only hasTopping
                 (owl-not (owl-or MeatTopping FishTopping)))))
;; \end{code}

;; Here, we define a |VegetarianPizza| as a |Pizza| with only
;; |MeatTopping| or |FishTopping|. The two key point about this
;; definition is that we have marked it as |:equivalent| rather than |:super| and
;; that there is no stated relationship between |VegetarianPizza| and
;; |MargheritaPizza|. We can confirm this at the shell. 


;; \begin{verbatim}
;; (subclasses VegetarianPizza)
;; => #{}
;; (subclass? VegetarianPizza MargheritaPizza)
;; => false
;; \end{verbatim}

;; However, now let us ask the same question of a reasoner. First, we choose a
;; reasoner to use (in this case HermiT), and then ask the same questions of
;; Tawny-OWL but now using the versions of functions prefixed with an |i| (for
;; inferred). Now, we see a different result. A |MargheritaPizza| is a subclass
;; of |VegetarianPizza|.

;; \begin{verbatim}
;; (reasoner-factory :hermit)
;; => #<ReasonerFactory org.semanticweb.HermiT.Reasoner$ReasonerFactory@4b8a8782>
;; (isubclasses VegetarianPizza)
;; => #{#<OWLClassImpl <http://purl.org/ontolink/take-wing/pizza#MargheritaPizza>>}
;; (isubclass? VegetarianPizza MargheritaPizza)
;; => true
;; \end{verbatim}

;; The reasoner can infer this using the following chain of logic:

;; \begin{itemize}
;; \item |MargheritaPizza| has only |MozzarellaTopping| or |TomatoTopping|
;; \item |MozzarellaTopping| is a |CheeseTopping|
;; \item |TomatoTopping| is a |VegetableTopping|
;; \item |CheeseTopping| is disjoint from |MeatTopping| and |FishTopping|
;; \item Likewise, |TomatoTopping| is not a |MeatTopping| or |FishTopping|
;; \item Therefore, |MargheritaPizza| has only toppings which are not
;;   |MeatTopping| or |FishTopping|.
;; \item A |VegetarianPizza| is any |Pizza| which has only toppings which are not
;;   |MeatTopping| or |FishTopping|.
;; \item So, a |MargheritaPizza| is a |VegetarianPizza|.
;; \end{itemize}

;; Even for this example, the chain of logic that we need to draw our inference
;; is quite long. The version of the pizza ontology presented here is quite
;; small, so while we can follow and reproduce this inference easily by hand for
;; this ontology, for a larger ontology it would be a lot harder, especially,
;; when we start to make greater use of the expressivity of OWL.

;; Many of the statements that we have made about pizza's are needed to make this
;; inference. For example, if we had not added |:disjoint:| to the subclasses of
;; |PizzaTopping|, we could not make this inference; even though we would know
;; that, for example, a |MozzarellaTopping| was a |CheeseTopping|, by default,
;; the reasoner would not assume that |CheeseTopping| was not a |MeatTopping|,
;; since these two could overlap. There are also some statements in the ontology
;; that we do not use to make this inference. For example, the reasoner does not

;; need to know that a |MargheritaPizza| actually has a |MozzarellaTopping| (the
;; statement |(some hasTopping MozzarellaTopping)|, just that if the pizza has
;; toppings at all, they are only mozzarella or tomato. The semantics of OWL can
;; be subtle, but allow us to draw extremely powerful conclusions.

;; \section{Recap}

;; In this chapter, we have described:

;; \begin{itemize}
;; \item The basic syntax of Tawny-OWL
;; \item New ontologies are created with |defontology|
;; \item Ontologies consist of classes and properties
;; \item Classes describe a set of individuals
;; \item Properties describe relationships between individuals
;; \item Defined classes allow us to make inferences using comptutational
;;   reasoning.
;; \end{itemize}

;; In addition, we have introduced the following semantic statements:
;; \begin{itemize}
;; \item Subclass relationships
;; \item Disjoint classes
;; \item Covering axioms
;; \item Inverse properties
;; \item Domain and range constraints
;; \item Functional characteristics
;; \item |some| and |only| restrictions, and the |some-only| pattern
;; \item |or| and |not| restrictions
;; \end{itemize}

;; %%
;; %% Local Variables:
;; %% lentic-init: lentic-clojure-latex-init
;; %% End:
;; %%
