## Type system overview

This is a compact `typ.el` type system model overview.  
It is heavilly based on official ["Programming types"](https://www.gnu.org/software/emacs/manual/html_node/elisp/Programming-Types.html#Programming-Types) documentation.

### Kinds of types

**Simple type** - concrete value type (can also be viewed as "primitive type").  
Represented with `keyword`.

**Abstract type** - type that have no direct instances.  
Abstract type tells about object interface and never about it's concrete type.  
Represented with `keyword`.  
Example: `(string-to-number x)` => `:number`  
At the *run time*, type is either `:integer` or `:float`,  
but we can not select appropriate type for that expression during *compile time*,
so `:number` is the closest one that can be safely selected.

**Parametric type** - mostly related to sequence types.
Parametric types have primary type and a single parameter type.  
Represented with a `cons` with `car` set to primary type and `cdr`
set to parameter type.  
Example: `(list 1 2)` => `(cons :list :integer)`  
Example: `(list (list 1) (list 2))` => `(cons :list (cons :list :integer))`  

### Terminology

#### Type tag

Keyword object that represents type unique ID.

- **Simple** and **abstract** types are tags themselves
- Primary type of **abstract**, i.e. `(car type)`

#### Type implementation

**Abstract** type always have one or more **implementations**.

Abstract type can implement other abstract type, if it's
operation set is a superset of implemented type **interface**.
For example, `:array` implements `:sequence`.

In type tree below, implementations are shown below the abstract type,
with 3 space padding.

#### Type interface

A set of operations that is defined over **abstract**.

For example, arithmetic operations are defined for `:number` type.  
Both `:float` and `:integer` implement that.

### Type tree

```elisp
:number
   :integer
   :float
(:sequence . T)
   (:list . T)
   (:array . T)
      :bool-vector
      :string
      (:vector . T)
:hash-table
:symbol
:boolean
:nil
```

In the tree above, **simple** and **parametric** types are always the leaves.  
The **abstract** types are always a root of some other types.

There is no `:character` type because `:integer` is enough ([characters](https://www.gnu.org/software/emacs/manual/html_node/elisp/Character-Type.html#Character-Type) are
represented as integers in Emacs Lisp).

### Special cases

1. Type `:nil` serves as a return type of `void`-like functions (called "procedures" in some languages).  
   `nil` and `()` literals has `:nil` type, not `(cons :list nil)`.

2. If no type can be inferred, `nil` is reported.  
   There is no `:undefined` or `:any` type.

3. `:string` can be represented as `(:array . :integer)` and `(:sequence . :integer)`.

4. `:bool-vector` can be represented as `(:array . :boolean)` and `(:sequence . :boolean)`.
