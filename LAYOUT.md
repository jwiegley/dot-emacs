Notes around layout, and adjusting it.
--------------------------------------

Resources

  * <http://en.wikibooks.org/wiki/Haskell/Indentation>
  * <http://www.haskell.org/onlinereport/haskell2010/haskellch10.html#x17-17800010.3>

## Layout keywords

The layout keywords are `let`, `where`, `of` and `do`. The expressions
introduced by them need to be kept indented at the same level.

## AST Items for layout keywords.

(gleaned from Parser.y.pp in the ghc sources)

`let`


```
  HsLet
    HsLet (HsLocalBinds id) (LHsExpr id) :: HsExpr id
              ^^keep aligned

  LetStmt
    LetStmt (HsLocalBindsLR idL idR) :: StmtLR idL idR
                ^^keep aligned
```

`where`

```
  HsModule
    -- not relevant to layout

  ClassDecl :: TyClDecl
    ClassDecl ....

  ClsInstD :: InstDecl
    ClsInstD typ binds sigs [fam_insts]
            ^^the binds, sigs, fam_insts should all align

  GRHSs
    GRHS [LStmt id] (LHsExpr id)
           ^^keep aligned

  TyDecl ::  TyClDecl
    TyDecl name vars defn fvs
                      ^^keep aligned
      [The `where` is in the defn]

  FamInstDecl
    FamInstDecl tycon pats defn fvs
                            ^^keep aligned
      [The `where` is in the defn]
```

`of`

```
  HsCase :: HsExpr
    HsCase (LHsExpr id) (MatchGroup id)
                           ^^keep aligned
```

`do`

```
  DoExpr :: HsExpr
    HsDo (HsStmtContext Name) [LStmt id] PostTcType
                                 ^^keep aligned
```


## General approach

Perform bottom-up traversal, ensuring that each of the above elements
is aligned in its column.


## The braces / semicolon insertion algorithm is as follows


The effect of layout is specified in this section by describing how to
add braces and semicolons to a laid-out program. The specification
takes the form of a function L that performs the translation. The
input to L is:

  * A stream of lexemes as specified by the lexical syntax in the
    Haskell report, with the following additional tokens:

    * If a `let`, `where`, `do`, or `of` keyword is not followed by
      the lexeme `{`, the token `{n}` is inserted after the keyword,
      where n is the indentation of the next lexeme if there is one,
      or 0 if the end of file has been reached.

    * If the first lexeme of a module is not `{` or module, then it is
      preceded by `{n}` where n is the indentation of the lexeme.
      Where the start of a lexeme is preceded only by white space on
      the same line, this lexeme is preceded by < n > where n is the
      indentation of the lexeme, provided that it is not, as a
      consequence of the first two rules, preceded by {n}. (NB: a
      string literal may span multiple lines – Section 2.6. So in
      the fragment

         f = ("Hello \
                  \Bill", "Jake")

      There is no < n > inserted before the \Bill, because it is not
      the beginning of a complete lexeme; nor before the ,, because
      it is not preceded only by white space.)


Algorithm

    L (< n >: ts) (m : ms) =  ; : (L ts (m : ms))      -- if m = n
                           =  } : (L (< n >: ts) ms)   -- if n < m

    L (< n >: ts) ms        = L ts ms

    L ({n} : ts) (m : ms)   = { : (L ts (n : m : ms))   -- if n > m (Note 1)

    L ({n} : ts) []         = { : (L ts [n])                -- if n > 0 (Note 1)
    L ({n} : ts) ms         = { : }  :  (L (< n >: ts) ms) -- (Note 2)

    L (} : ts) (0 : ms)     = } : (L ts ms)               -- (Note 3)
    L (} : ts) ms           = parse-error                 -- (Note 3)
    L ({ : ts) ms           = { : (L ts (0 : ms))         -- (Note 4)
    L (t : ts) (m : ms)     = } : (L (t : ts) ms)         -- if m /= 0 and parse-error(t)
                                                          -- (Note 5)
    L (t : ts) ms           = t : (L ts ms)
    L [] []                 = []
    L [] (m : ms)           = } : L [] ms                 -- if m /= 0 (Note 6)


Note 1

A nested context must be further indented than the enclosing context
(n > m). If not, L fails, and the compiler should indicate a layout
error.

Note 2

If the first token after a where (say) is not indented more than the
enclosing layout context, then the block must be empty, so empty
braces are inserted. The {n} token is replaced by < n >, to mimic the
situation if the empty braces had been explicit.

Note 3

By matching against 0 for the current layout context, we ensure that
an explicit close brace can only match an explicit open brace. A parse
error results if an explicit close brace matches an implicit open
brace.

Note 4

This clause means that all brace pairs are treated as explicit layout
contexts, including labelled construction and update (Section 3.15).
This is a difference between this formulation and Haskell 1.4.

Note 5

The side condition parse-error(t) is to be interpreted as follows: if
the tokens generated so far by L together with the next token t
represent an invalid prefix of the Haskell grammar, and the tokens
generated so far by L followed by the token “}” represent a valid
prefix of the Haskell grammar, then parse-error(t) is true.

The test m /= 0 checks that an implicitly-added closing brace would
match an implicit open brace.

Note 6

At the end of the input, any pending close-braces are inserted. It is
an error at this point to be within a non-layout context (i.e. m = 0).

