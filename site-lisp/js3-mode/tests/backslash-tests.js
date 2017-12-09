/* In the first case, pressing enter after the backslash should put
 * you on the next line with a backslash.
 */
var a = "foo \
\
"

/* In the second case, pressing enter inside the string should put a
 * string concatenation on the next line.
 */
var b = "foo"
      + ""
