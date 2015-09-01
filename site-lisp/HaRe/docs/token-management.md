

One of the most important aspects of a refactorer is that it must work
with real world source code. This means that when a user requests a
particular change, they expect ONLY that change to be made, and no
other changes to the source file or its layout.

On the other side, in order to reliably make the changes, the
refactorer needs to make use of the AST, also using the analysis the
compiler has done to resolve which names are the same and what the
types are.

Most compilers throw away the tokens once the AST is built.

GHC, via the GHC API, makes the rich token stream available. For each
token, this provides its location in the original source file in terms
of line,col start and end, and the original string in the source file
making up the token. This token stream includes non-trivial whitespace
such as comments.

Passing this rich token list to the appropriate function recreates the
original source file (except for a minor bug:
<http://hackage.haskell.org/trac/ghc/ticket/7351> which is easily
worked around.

The AST is well annotated with `SrcSpan`s tying it up to the original
rich token stream.

Theoretically it should be possible to perform the refactoring based
on the located AST, and relatively easily tie up the corresponding
tokens.

### Problems

There are some problems with this.

The first problem we face is that the locations in the AST refer to
the start and end of the specific tokens making up the syntactic
features parsed to create the AST element, e.g. a function or data
declaration. They do not take into account the comment tokens that are
also in the stream. This becomes particularly important if we are
moving things around, as people get upset if their comments suddenly
disappear, or their layout style changes.

The second problem is that Haskell is a layout sensitive language.
This means white space is important, and a module can fail to compile if
the layout is not handled properly.

Renaming a variable can make the resulting token and hence locations larger or
smaller, and influence layout.  e.g. in

```haskell
--Layout rule applies after 'where','let','do' and 'of'
--In this Example: rename 'sq' to 'square'.

sumSquares x y= sq x + sq y where sq x= x^pow
  --There is a comment.
                                  pow=2
```

the entire subordinate where clause needs to shift right to compensate
for the longer name.

```haskell
sumSquares x y= square x + square y where square x= x^pow
  --There is a comment.
                                          pow=2
```

The third problem is that the very close tie up between the AST and
the token stream only holds before any changes are made, and the token
output function expects the tokens to be in increasing order.  This
means that if a declaration is lifted to the top level, or demoted
from the top level to inside the declaration where it is used, the
locations in the AST and in the tokens need to be updated.

The fourth problem is more of a design goal. It should be possible to
perform refactorings by making changes to the AST, and the tokens
should automatically be taken care of. This is particularly important
as the detailed token and layout management is some of the fiddliest
code in the base, it needs to be taken care of once comprehensively
rather than generating an endless stream of stupid niggles.

### Solutions

Before presenting solutions, a brief disclaimer: I am more of a
practical programmer than a theoretical one, particularly when I am
still feeling my way through the problem space.

As such, the current implementation can probably be cleaned up
considerably as it contains the wreckage of various false starts.

#### Annotated AST

The most obvious solution is to annotate the AST with the tokens.

Although I would love to do this, it requires some deep dives into
some pretty hairy type level programming to achieve, mainly because
the AST is a large set of mutually recursive types, rather than a
single type.

There is some promise in using the `Annotations` package, based on the
paper 'Generic Selections of Subexpressions' by M van Steenbergen,
which I have been experimenting with here
<https://github.com/alanz/annotations-play>, the problem is coming up
with a means of actually generating all the required boilerplate.

Some attempts at generating the required multirec instances are here
<https://github.com/alanz/ghc-multirec>.

In the longer term I think this approach holds promise, but I have
taken a more pragmatic approach in the mean time.

#### Automatically maintain AST and tokens

The API design goal is that the refactoring can be specified in terms
of the AST only, and the tokens are automatically brought along for
the ride.

Because the token stream is separate from the AST, and I have not come
up with a practical way to stitch them back together again, this
requires some fiddly bookkeeping to keep everything lined up.

In particular, the following kinds of operation can take place

  1. Remove an AST element and its associated tokens.
  2. Edit a removed element in some way
  3. Add the edited element back in a different part of the AST
  4. Construct a brand new AST element, and generate fresh tokens for
     it

The only linkage we have from the AST to the tokens is via a GHC
SrcSpan, which specifies a start and end (row,col) value, each of
which is captured in a Haskell Int.

#### LayoutTree structure

A GHC Int in the 32-bit compiler has 32 bits, and we have chosen to
work within this limit to maintain backward compatibility until 64
bits is completely universal.

The linkage is managed through the row value, by setting high bits
according to the following scheme (see
Language.Haskell.Refact.Utils.TokenUtilsTypes).

```haskell
data ForestLine = ForestLine
                  { flSpanLengthChanged :: !Bool -- ^The length of the
                                                 -- span may have
                                                 -- changed due to
                                                 -- updated tokens.
                  , flTreeSelector  :: !Int
                  , flInsertVersion :: !Int
                  , flLine          :: !Int
                  } -- deriving (Eq)
```

The meanings of these fields is as follows

The `flSpanLengthChanged` flag is set if the length of the span may
have changed due to tokens being added, removed, or replaced with
similar but having different lengths, as in renaming a variable.

The `flTreeSelector` is used to select which tree in the overall token
tree forest this span belongs too. The forest structure is described
below.

The `flInsertVersion` is used to track spans that are inserted between
two existing spans. Instead of re-sequencing the entire token tree and
AST at that point, every time a new span is added the next higher
version number is used. So the original span will have a version of 0,
the first one inserted will have a 1, and so on.


##### Converting a ForestLine to a GHC row

The `ForestLine` structure is converted to a GHC SrcSpan by packing
bits as follows

The `flSpanLengthChanged` field occupies the top (non-sign) bit
The `flTreeSelector` field takes the next 5 bits
The `flInsertVersion` takes the next 5 bits
The `flLine` is the bottom 20 bits, and corresponds to the original
line number.


##### ForestSpan and SrcSpan

The `ForestLine` is wrapped up into a ForestSpan, which can be converted to/from a
GHC SrcSpan


```haskell
type ForestPos = (ForestLine,Int)

-- |Match a SrcSpan, using a ForestLine as the marker
type ForestSpan = (ForestPos,ForestPos)
```

#### LayoutTree

Since the AST is a tree, the tokens need to be stored in a tree too,
called a LayoutTree. A Rose Tree is used for this, where the label
value is of type Entry defined as follows

```haskell
-- | An entry in the data structure for a particular srcspan.
data Entry = Entry !ForestSpan -- The source span contained in this
                                  -- Node
                   !Layout     -- How the sub-elements nest
                   ![PosToken] -- ^The tokens for the SrcSpan if
                               --  subtree is empty
           | Deleted !ForestSpan -- The source span has been deleted
                     RowOffset   -- prior gap in lines
                     SimpPos     -- ^The gap between this span end and
                                 --  the start of the next in the
                                 --  fringe of the tree.

```

The Layout structure keeps track of whether the orignal AST element
was the beginning of layout, introduced by where / let / do according
to the Haskell syntax.

This is defined as

```haskell
data Layout = Above EndOffset (Row,Col) (Row,Col) EndOffset
            -- ^ Initial offset from token before the
            -- stacked list of items, the (r,c) of the first
            -- non-comment token, the (r,c) of the end of the last non-comment
            -- token in the stacked list to be able to calculate the
            -- (RowOffset,ColOffset) between the last token and the
            -- start of the next item.
            | NoChange
            deriving (Show,Eq)

data EndOffset = None
               | SameLine ColOffset
               | FromAlignCol (RowOffset, ColOffset)
               deriving (Show,Eq)

```

The LayoutTree carries tokens at the leaf nodes only, so either the
token list is populated or the sub-tree.

One last wrinkle is that the SrcSpans in the AST are according to the
first and last non-comment tokens. The tokens for a leading or
trailing comment need to be kept in the appropriate place, so the
ForestSpan in the token tree refers to non-comment tokens only.

#### Initializing the LayoutTree

Because the haskell syntax layout rules are explicitly captured in the
LayoutTree, this needs to be built when the AST is first loaded, prior
to any refactoring.

A GHC TypeCheckedModule contains values for the parsed, renamed and
typechecked source.

Each of these has been processed more than the prior one, and in the
process becomes further from the original source.

In particular, the ParsedSource AST is still in ascending SrcSpan
order, where the individual syntax element types are simply tagged.

The RenamedSource collects the various elements together, so all binds
are together, all type classes, instance declarations, etc.

So the token allocation is done based on the ParsedSource, and the
whole file is processed to make sure that every token, and in
particular every comment, is allocated to some AST SrcSpan.

This is done in `Language.Haskell.Refact.Utils.Layout` by the function
`allocTokens`.

This has been laboriously hand-crafted, to ensure that
the layout rules are honoured and the GHC type holes are avoided. It
can probably be simplified in future by making use of the appropriate
generic programming technique.


### TokenCache

The overall set of evolving tokens is stored in a structure called a
`TokenCache`, and there is one per module loaded.

```haskell
data TokenCache = TK
  { tkCache :: !(Map.Map TreeId (Tree Entry))
  , tkLastTreeId :: !TreeId
  }
```

The `TreeId` is simply a tagged positive Int, and is used to keep
track of scratchpad token sets, or ones that have been removed from
the main AST as the result of a delete operation.

The primary tokens are stored against TreeId 0, and this is the
default tree operated against unless another one is specified.

### API Linkage

The AST manipulation API functions are exposed from
`Language.Haskell.Refact.Utils.MonadFunctions` and are available once
a given module has been loaded into a refactoring session.

Each of these functions is responsible for capturing an individual
change to the AST, and keeping the tokens in line.

For example, consider the `putDeclToksAfterSpan` function

```haskell
-- |Add tokens after a designated GHC.SrcSpan, and update the AST
-- fragment to reflect it
putDeclToksAfterSpan :: (SYB.Data t) => GHC.SrcSpan -> GHC.Located t -> Positioning -> [PosToken] -> RefactGhc (GHC.Located t)
putDeclToksAfterSpan oldSpan t pos toks = do
  logm $ "putDeclToksAfterSpan " ++ (showGhc oldSpan) ++ ":" ++ (show (showSrcSpanF oldSpan,pos,toks))
  st <- get
  let Just tm = rsModule st
  let forest = getTreeFromCache oldSpan (rsTokenCache tm)
  let (forest',_newSpan, t') = addDeclToksAfterSrcSpan forest oldSpan pos toks t
  let tk' = replaceTreeInCache oldSpan forest' (rsTokenCache tm)
  let rsModule' = Just (tm {rsTokenCache = tk', rsStreamModified = True})
  put $ st { rsModule = rsModule' }
  return t'
```

This function takes the original GHC SrcSpan, an AST fragment, a value
indicating how the new fragment should be placed relative to the
existing one, and the tokens belonging to the new fragment.

These tokens would either have been generated freshly from a new AST
fragment, or come about from prior API calls.

It fetches the appropriate tree from the TokenCache structure, a
process which first converts the GHC SrcSpan to a ForestSpan, and then
uses the embedded tree selector as an index into the TokenCache.

It then calls `addDeclToksAfterSrcSpan` which inserts a new node into
the LayoutTree, having the same start position as the original one but
having a version incremented by one. Every SrcSpan in the AST fragment
being added is then adjusted to reflect the new origin span in the
tree, including the version number. Any row,col offsets are adjusted
as required.

The updated AST fragment and LayoutTree are returned to the monadic
code, which updates the stored state to reflect the new tokens in
their cache, and returns the modified AST element.

It is up to the calling code to keep track of the AST element, as this
call would typically just be a single step in a whole refactoring.

### Final Output

Once the refactoring is complete, the results can be written out. For
this only the main tree in the token cache is required.

This tree is potentially a complex structure, having had a sequence of
additions, deletions, resizings and so on performed on it.

Order is imposed on this by making use of a `DualTree` to manage
constraints upwards and downwards in constructing the final output.

The downwards constraints are layout rules which require for example
each part of a let declaration to start in the same column.

The upwards constraints are line and column numbers that change as
lines are added, removed, or whole syntax fragments are indented or
dedented.

#### Dual Tree structure

Some background on the dual tree structure can be found here
[Monoids: Theme and Variations](http://www.cis.upenn.edu/~byorgey/pub/monoid-pearl.pdf)

Essentially it is a rose tree which has been extended to have an
element that propagates down the tree calculated from the root to the
leaves, and another one that is calculated from the leaves to the root
and proceeds up the tree.

The module managing the Dual Tree is (unsurprisingly)
`Language.Haskell.Refact.Utils.DualTree`

The up value is defined as

```haskell
data Up = Up Span Alignment (NE.NonEmpty Line) [DeletedSpan]
        | UDeleted [DeletedSpan]
        deriving Show

data Span = Span (Row,Col) (Row,Col)
          deriving (Show,Eq)

data Line = Line Row Col RowOffset Source LineOpt [PosToken]

data Alignment = ANone | AVertical
               deriving (Show,Eq)
```

The final result we care about is the NoneEmpty list of Line values
that will propagate from the leaves to the root of the tree and
represents the final output.

The down value is a `Transformation` which is inserted when a node
initiates layout rules on the ones below it in the tree.

The specific dual tree structure is defined as

```haskell
-- | The main data structure for this module
type SourceTree = DUALTree Transformation Up Annot Prim
```

From
<http://hackage.haskell.org/package/dual-tree-0.2.0.3/docs/Data-Tree-DUAL.html>

`data DUALTree d u a l`

  Rose (n-ary) trees with both upwards- (i.e. cached) and
  downwards-traveling (i.e. accumulating) monoidal annotations.
  Abstractly, a DUALTree is a rose (n-ary) tree with data (of type l) at
  leaves, data (of type a) at internal nodes, and two types of monoidal
  annotations, one (of type u) travelling "up" the tree and one (of type
  d) traveling "down".

In practice we only use an annotation of

    ASubtree ForestSpan

Which simply captures the boundaries of the subtree at this point.

The Prim structure captures the tokens for a specific line, which
carries either the tokens for the line or is marked as deleted.

```haskell
data Prim = PToks [PosToken]
          | PDeleted ForestSpan RowOffset SimpPos
          deriving Show
```

#### Conversion of LayoutTree to DualTree

The first step is to convert the tokens as captured in the modified
LayoutTree, which is oriented purely toward SrcSpan (and equivalently
ForestSpan) values, to the DualTree which is oriented towards line at
a time values.

The `layoutTreeToSourceTree` function converts any SourceTree leaf
value (identified by carrying tokens only, no subtree) into a DualTree
leaf carrying a NonEmpty list of lines, constructed by grouping the
tokens by line.

Any SourceTree node marked as Deleted is converted into an equivalent
SourceTree leaf.

Internal LayoutTree entries are either passed through with an
annotation as to the enclosed span, or processed specially if they
carry layout.

If an internal LayoutTree carries layout, it triggers an `applyD`
transformation in the dual tree which propagates a constraint
downwards, namely the requirement for layout.

#### Dual Tree Magic

The Dual Tree magic happens in the monoidal combination of the upward
and downward elements.  This happens automatically when required, we
simply have to specify the operations to be performed.


The most important of these is the `combineUps` function, which is
defined as the SemiGroup `<>` operator between `Up` elements.

This is called whenever two nodes are being combined as the dual tree
is being constructed from the leaf nodes towards the root.

Any given `Up` entry has lines in it, of which the first and last line
may be partial, containing a fragment of a line which must be combined
with the matching fragment of the incoming element.

Also, one or both of the elements may indicate a range has been
deleted from the original tree, indicating that the balance of the
lines must be moved up.

The gory details can be examined in the source.

The other important one is the Action Transformation instance for Up.

This defines how the alignment action should be applied to an `Up`
value to yield a modified `Up` value.

```haskell
instance (Action Transformation Up) where
  act (TAbove _co _bo _p1 _p2 _eo) (Up sspan _a s ds) = (Up sspan a' s' ds)
    where
      a' = AVertical
      s' = NE.map (\(Line r c o ss _f toks) -> (Line r c o ss OGroup toks)) s

  act (TAbove _co _bo _p1 _p2 _eo) (UDeleted ds) = UDeleted ds
```

It basically says that the layout style should change to `Vertical`,
and the corresponding lines should be marked as belonging to a group,
so they will be moved as a unit if column changes are required.

When this process is complete the root element of the SourceTree has
an `Up` value that captures all the constraints of layout in the
original LayoutTree, and has one entry per line.

This `Up` entry is extracted by the `retrieveLines` function which
returns a list of `Line` values.

    data Line = Line Row Col RowOffset Source LineOpt [PosToken]

    data Source = SOriginal
                | SAdded
                | SWasAdded
                deriving (Show,Eq)

    data LineOpt = ONone
                 -- | This line needs to be grouped with the next in terms
                 -- of layout, so any column offsets need to be propagated
                 | OGroup
                 deriving (Show,Eq)

#### Rendering the lines

One last transformation is required to generate actual source lines,
which is performed by the `renderLines` function.

This takes a list of Line values and places them correctly in the
output stream.

Each Line has an absolute row and col associated with it. The output
function inserts appropriate newline and space values into the stream
to ensure that each line starts at the required spot.

## All done.

It is a very complicated transformation, but it is broken down into a
number of steps, each of which does a specific required function.

To recap


  1. Allocate tokens to a LayoutTree, capturing all SrcSpans and
     starts of syntax layout.
  2. Manipulate the LayoutTree to achieve the refactoring, working at
     the SrcSpan level.
  3. Convert the LayoutTree to a SourceTree, operating at the line
     level, and resolving layout constraints downward against
     add/del/move/resize constraints upward.
  4. Convert the absolute line entries back into a stream of
     characters as the modified source code.



