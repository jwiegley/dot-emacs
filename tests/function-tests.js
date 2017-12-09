/* global Crafty */

function functionTests () {
  /* cases for function indentation */

  //test f1
  // basic function declaration
  //function body should be indented one step past 'function'
  function test() {
    var x
  }

  //test f2
  //function expression in object literal
  //function body should be indented one step from beginning of property name
  var a = { function_name: function () {
              var b = 1
            }
          , other_function: function () {
              var c = 1
            }
          }

  //test f3
  //function on first line of method call
  //function body should be indented one step
  a.addEvent('click', function (e) {
    var c = 1
  })

  //test f4
  //function on subsequent line of method call
  //function body should be indented one step from beginning of function keyword
  a.addEvent( 'click'
            , function (e) {
                var c = 1
              }
            )

  //test f5
  //just making sure this still works - silly regex
  //function body should be indented one step from function keyword
  var text = text.replace( /https?\:\/\/[^"\s\<\>]*[^.,;'">\:\s\<\>\)\]\!]/g
                         , function (wholeMatch,matchIndex) {
                             var left = text.slice(0, matchIndex)
                           }
                         )

  //test f6
  //var keyword special case
  //compromise: function body is indented one step past function name
  var function_name = function () {
        return 1
      }
    , function_2 = function () {
        return 2
      }

  //test f7
  //function expression
  //In pretty much all other cases, function expressions should indent
  // one step from the beginning of the 'function' keyword
  // except in the special case of ;( starting the line, in which case
  // ;( is effectively considered part of the function keyword.
  ;(function () {
    var a = 1
  })()
  , (function () {
       var b = 2
     })()

  //test f8
  // = function special case
  // function body should be indented one step from the start of the expression
  // this case is defined where a function is simply assigned -
  // the function body should be indented one step from the
  //  beginning of the assignment expression.
  //Issue #45
  window.onload = function () {
    Crafty.keys.RA = Crafty.keys.RIGHT_ARROW
    Crafty.keys.LA = Crafty.keys.LEFT_ARROW
  }

  //test f9
  //return function special case
  // body of function should be indented one step,
  // not lined up with function keyword
  function foo () {
    return function () {
      return 1
    }
  }

  //test f10
  //future var keyword special cases
  // FIXME: if you are only declaring one variable, indent function body once.
  var f1 = function () {
        foo()
      }
    , f2 = function () {
        foo()
      }
  var f3 = function () {
    foo()
  }

  //end function tests

  return 1
}
