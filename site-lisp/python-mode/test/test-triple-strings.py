# Source:
# http://launchpadlibrarian.net/22565844/test-triple-strings.py
# Author: Ed Loper

# This file tests python-mode's ability to handle triple-quoted
# string.  Here's how to tell if python-mode's doing the right thing:
#
# - All dashes (-) should *not* be marked as strings.
# - All Os, Xs, <s, and >s should be marked as strings.
# - None of the quote marks around O's should be marked as strings.
# - Quote marks that are between angle brackets (<...>) should be
#   marked as strings.  Think of "X" as a pair of angle brackets
#   right next to one another.  Also, quotes to the left of >s
#   and the right of <s should be marked as strings.
#
# (note: replacing -,O,X,<,> with other characters should not affect
# the fontificatin any; these characters were just used to make it
# easier to see what the intended colorization is.)

# Some easy cases:
"O" 'O' "<'>" '<">'
 "O"   'O'   "<'>"   '<">'
 " O "   ' O '   " < ' > "   ' < " > '
"""O""" '''O''' "<<<'>>>" '''<">'''

# Some harder cases:
"""<">""" '''<'>'''

# Some tricky cases with backslashes.
'''<'>''' '''<\'''>''' '''<\\'''

# Some tricky cases with more than 3 quotes in a row.
"O""" "O"
"""">"""
"""">>"""
""""X">"""
""""X"">"""
"""O""""O" ""
"""O""""" "O"
"""O""""""<">"""
"""O"""""""X">"""
"""O""""""""X">"""
"""O""" "<<<>>>>"
"""""""""O""" "O"
"""O""""O""O""O"""
"""">"""    """">>"""    """">>>"""
""""">"""   """"">>"""   """"">>>"""
""""">>>""""O"   """"">>>"""""
"""""""""<""X"X"">"""

# One version had a bug with comments ending in string markers: "
"""O"""

 "" ""

"""<">""" '''<'>'''

# Spanning multiple lines:

"<
>"

'<
>'

"""
<
<
<
<
'
X
X
X
"
>
>
"""
