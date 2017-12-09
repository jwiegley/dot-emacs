// To run these tests, left-justify then indent each line and visually
// observe that the indentation level has not changed and no emacs errors
// were thrown.  Be sure to check 'Messages' before exiting.
// Tests assume default settings for js3-mode

function commaFirstStyle () {
  /* cases for comma-first, operator-first, and dot-first style */

  /* BASIC CASES */

  //test c1
  //commas line up under 'r' in 'var'
  var a = "ape"
    , b = "bat"
    , c = "cat"
    , d = "dog"
    , e = "elf"
    , f = "fly"
    , g = "gnu"
    , h = "hat"
    , i = "ibu"
    , j = "joe"
    , k = "kit"
    , l = "lay"
    , m = "man"
    , n = "now"
    , aPrettyLongVariableName

  //test c2
  //operators line up under '='
  a = b
    + c
    - d
    * e
    / f
    % g
    < h
    > i
    & j
    ^ k
    | l
    ? m
    : n

  //test c3
  //operators and ')' line up under '('
  a = ( b
      + c
      )

  //test c4
  //commas and '}' line up under '{'
  a = { b : c
      , d : e
      }

  //test c5
  //dot lines up under dot if js3-indent-dots is t
  a.b
  .c()

  //test c6
  //commas lined up under 'n' in 'return'.
  //please don't ever do this
  if (a) {
    return 1
         , 2
         , 3
         , 4 // returns the last value, 4
  }

  //test c7
  //commas and ']' lined up under '['
  if (b) {
    return [ 1
           , 2
           , 3
           , 4
           ]
  }

  //test c8
  //function call - line up commas and ')' under '('
  a( b
   , c
   )

  /* OTHER CASES */
  /* This section contains cases which have historically been problematic,
   * or which illustrate past issues
   */

  //test c9
  //Double-quoted strings containing problematic characters
  a( aPrettyLongVariableName
   , "A string, which \"has some useful information"
   , "If you put these all together, it'd be too long"
   , { a: "is for antelope", b: "is for bat" }
   , 42
   )

  //test c10
  //Single-quoted strings containing problematic characters
  a( aPrettyLongVariableName
   , 'A string, which \'has some useful information'
   , 'If you put these all together, it\'d be too long'
   , { a: 'is for antelope', b: 'is for bat' }
   , 42
   )

  //test c11
  //line up with correct dot if js3-indent-dots is t
  a.b( c.d )
  .e()

  //test c12
  //line up with correct brace
  a = { b: { c: d
           , e: f
           }
      , c: d
      }

  //test c13
  //line up with correct paren
  a = ( b + ( c
            / d
            )
          * e
      )

  //test c14
  //2-dimensional array
  a = [ [ b
        , c
        ]
      , [d, e]
      , f
      ]

  //test c15
  //skip multiline comment and line up comma and '}' under '{'
  //issue #6
  a = { b: c /*multiline { ,
               comment*/
      , d: e
      }

  //test c16
  //line up operators under first operator on line in same subexpression
  //issue #7
  var zoomThumbHtml = '<a target="_blank" id="zoomThumbnailLink"'
                    + '   title="Click to see full-size"'
                    + '   href="' + Ext.BLANK_IMAGE_URL + '">'
                    + '<img src="' + Ext.BLANK_IMAGE_URL + '"'

  //test c16
  //line up operators without trailing spaces
  //issue #11
  function test() {
    var x
    x.report("test1"
            +"test2"
            )
  }

  //test c17
  //properly ignoring '{' in strings
  //issue #12
  var foo = { prop: '{baz'
            }
    , bar

  //test c18
  //'+ e' should line up with ': c'
  //issue #21
  a = { b : c + d
          + e
      }

  //test c19
  //function expression in object literal
  //function body should be indented one step from beginning of property name
  //issue #22
  a = { f: function () {
          var a = g
                + h

          return [ a
                 , g
                 ]
        }
      }

  //test c20
  //a big jumble of different things
  var rv = { a: [ b
                , ( c
                  + d
                  )
                , e
                ]
           , f: function ( g /* silly multiline
                                comment */
                         , h
                         ) {
               var a = g
                     + h

               return [ a
                      , g
                      ]
             }
           }
    , rv2 = a

  //test c21
  // ? : operators
  // : should line up with open paren
  a = ( b ? c
      : d ? e
      : f
      )

  //test c22
  //comma should line up with the r in var
  //issue #32
  var x = require("./test/test").something
    , y = require('./test2')

  //test c23
  //The function body should probably be indented past the paren, since there
  // are multiple arguments.  However, in the general case of passing only
  // one function to a method, one would normally want it to indent
  // only one indent for convenience.
  // Just make functions take a first argument that's not a function to fix
  //issue #31

  something({ value: "data"
            , errback: function(code, e) {
                var u = new Something(user_data)
                u.method( function(data) {
                  res.json(data)
                }
                        , function(data) {
                            res.json(data)
                          }
                        )
              }
            , callback: function(data){
                res.json()
              }
            })
  res.writeHead(201)

  //test c24
  // && should line up properly with (
  // set back one character so args line up
  //issue #29

  x = ( a != b
     && c != d
      )

  //test c25
  //, should line up with var
  //issue #30

  var boolReg = '^(' + boolFields.join('|') + ')$'
    , ignoreReg = '^(' + ignoreFields.join('|') + ')$'

  //test c26
  //comma should line up with the ( even though it's a weird case.
  //issue #33

  foo( a
     + b
     , c
     + d
     )

  //test c27
  // * g should line up with - e
  // + h should line up with & d
  // & i should line up with | c
  // | j should line up with = b
  // this is a weird but consistent case - to avoid, use parens.

  a = b | c & d - e * f
                * g
            + h
        & i
    | j

  //test c28
  //similar to test c27
  //all operators should line up with parens

  a = ( b | ( c & ( d - ( e * f
                        * g
                        )
                  + h
                  )
            & i
            )
      | j
      )

  //test c29
  //logical operators and such
  //  = should line up vertically
  // || should line up vertically
  // && should line up vertically

  a = b
    = c
    = d < e || f > g
            || h < i && j < k
                     && l > m
            || n < b

  //test c30
  //comparison operators
  //again, looks strange without parens
  //>= i should line up under !==f
  // !== j === k != l == m should all line up under = b
  a = b == c != d === e !== f >= g <= h
                         >= i
  !== j
  === k
   != l
   == m

  //tests c31-c33
  //various nice lining up of dots
  //from gist https://gist.github.com/1128152 (HT isaacs)

  var someKindOfObject = {}

  //test c31
  //dots should line up if js3-indent-dots is t

  var xyz = someKindOfObject.foo("asdf")
            .bar("bloo")
            .bloo("blerg")

  //test c32
  //dots should be indented once from the object name if js3-indent-dots is t

  var xyx = someKindOfObject
            .foo("asdf")
            .bar("bloo")

  //test c33
  //dots should line up if js3-indent-dots is t

  someKindOfObject.doSomething()
  .doSomethingElse()
  .yetAnotherSomething()

  //test c34
  //function body should be indented once past 'function' keyword
  //issue #35
  function myThing (args, cb) {
    getData( args
           , function (er, data) {
               if ( er ) {
                 return log.er( cb, "Couldn't get data" )(er)
               }
               return doSomethingElse( data, cb )
             }
           )
  }

  //test c35
  // comma before logStream should line up with 'r' in 'var'
  //issue #37

  var options = { flags: 'a'
                , mode: 0644
                }
    , logStream = fs.createWriteStream(argv.log, options)

  //test c36
  // comma in object literal should line up with opening bracket
  //issue #37
  var logStream = fs.createWriteStream(argv.log, { flags: 'a'
                                                 , mode: 0644
                                                 })

  //test c37
  // this issue actually appears in non-comma-first too
  // 'var' in the function should line up appropriately with 'function'
  //issue #40

  var text = text.replace( /https?\:\/\/[^"\s\<\>]*[^.,;'">\:\s\<\>\)\]\!]/g
                         , function (wholeMatch,matchIndex) {
                             var left = text.slice(0, matchIndex)
                               , right = text.slice(matchIndex)
                           }
                         )

  //test c38
  // the comma before 'function' should line up with the parens for '.bind',
  // not the parens for '.e'
  //issue #42
  var player = Crafty.e( '2D'
                       , 'DOM'
                       )
               .bind( 'enterframe'
                    , function (e) {})

  //test c39
  // the function body should be intended past 'function' keyword
  // (according to assumptions of current implementation)
  //issue #41
  Crafty.load(['sprite.png'], function () {
    Crafty.scene('main')
  })

  //test c40
  // the function bodies should be indented consistently
  // and .bind should be indented equivalent to this
  //issue #43
  //issue #44
  this.bind('enterframe', function () {
    return 1;
  })
  .bind('keydown', function (e) {
    return 2;
  })

  //test c41
  // line up leading semicolons properly in a continued for loop def
  // the semicolons should line up with the parens
  for ( i = 0
      ; i < 5
      ; i ++
      ) foo()

  //end comma-first tests

  return 1
}

function commaLastStyle () {
  /* Cases for comma-last, operator-last, and dot-last style */
  /* BASIC CASES */

  //test s1
  //indent to one space after 'var', so 'a' lines up with 'b'
  var a = "ape",
      b = "bat",
      c = "cat",
      d = "dog",
      e = "elf",
      f = "fly",
      g = "gnu",
      h = "hat",
      i = "ibu",
      j = "joe",
      k = "kit",
      l = "lay",
      m = "man",
      n = "now",
      aPrettyLongVariableName

  //test s2
  //indent continued expressions by one level
  a = b +
    c -
    d *
    e /
    f %
    g <
    h >
    i &
    j ^
    k |
    l ?
    m :
    n

  //test s3
  //continued statements are indented one level,
  //and ')' lines up with beginning of line containing '('
  a = (
    b +
      c
  )

  //test s4
  //object literals are indented one level
  //and '}' lines up with beginning of line containing '{'
  a = {
    b : c,
    d : e
  }

  //test s5
  //continued dot expression indents one level
  a.b.
    c()

  //test s6
  //in square brackets, indent one level
  //and ']' lines up with beginning of line containing '['
  if (a) {
    return [
      1,
      2,
      3,
      4
    ]
  }

  //test s7
  //function call - indent one level
  //and ')' lines up with line containing '('
  a(
    b,
    c
  )

  /* OTHER CASES */
  /* This section contains cases which have historically been problematic,
   * or which illustrate past issues
   */

  //test s8
  //the second line should not even temporarily be indented past the first line
  //issue #18
  var a1
  var b1

  //end comma-last tests

  return 1
}

function otherTests () {
  /* Cases that affect all style types */

  //test t1
  //the function body should be indented one step from beginning of line
  //and the closing brace should be on the same level as beginning of line
  //Issue #26
  var function_name = function () {
    return 1
  }

  //test t2
  //the case statements should be indented one indent from the
  //beginning of the switch statement, + js3-label-indent-offset
  //(default 0)
  //Issue #99
  function qux () {
    function_name(function(bar) {
      switch (bar) {
        case "1":
        case "2":
      }
    });
  }

  //end other tests

  return 1;
}

function hybridLazyTests () {
  /* Cases that work with the new auto-detect lazy commas mode */

  //test h1
  // Object literals
  // The first line starting with `, bar` should be indented
  //  back two spaces from `foo`.
  // The second line starting with ', bar' should be indented so that
  //  the comma lines up with the opening brace on the previous line
  // Issue #60
  Foo = Backbone.View.extend({
    foo: function(){
      var a = { foo: 1
              , bar: 2
              }
    }
  , bar: function(){
      var a = { foo: 1
              , bar: 2
              }
    }
  })

  //test h2
  // Array literals
  // Without extra space given by js3-square-indent-offset,
  //  both closing square braces should line up.
  //  3 is indented one step from the opening brace, and
  //  `, 4` is indented back two spaces from 3.
  var a = [ 1
          , 2
          , [
            3
          , 4
          , 5
          ]
          ]

  //test h3
  // function args
  // for function b, the commas should line up under the parens.
  // for function d, `e` should be indented one step
  //  and `, f` should be indented back two spaces from `e`.
  function b ( a
             , b
             , c
             ) {
    function d (
      e
    , f
    , g
    ) {}
  }

  //test h4
  // function call
  // Without extra space given by js3-paren-indent-offset,
  //  both closing parens should line up.
  //  3 is indented one step from the opening paren, and
  //  `, 4` is indented back two spaces from 3.
  var c = b( 1
           , 2
           , b(
             3
           , 4
           , 5
           )
           )

  //end hybrid tests

  return 1;

}

//test z1
//operator should be indented to column 0 - emacs should not throw an error
//possibly related to Issue #28
//Edit: the following is no longer supported - indentation of '+' is undefined
//Rationale: this is never useful JS code
1
                                         + 2

//test z2
//comma should be indented to column 0 - emacs should not throw an error
//possibly related to Issue #28
//Edit: the following is no longer supported - indentation of ',' is undefined
//Rationale: this is never useful JS code
1
                                         , 2

//test z3
//+ should correctly indent to first column without throwing an error
//related to fix for Issue #29
( 1
+ 2
)

//test z4
//both for loop bodies should be indented one step from the for loop start
//Issue #58
var i,j

for (i = 0; i < 10; i++)
  alert('hi')

function foo () {
  for (j = 0; j < 10; j++)
    alert('hi')
}
