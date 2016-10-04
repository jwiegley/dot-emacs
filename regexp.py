# Copyright (C) 2013 Marko Bencun
#
# This file is part of visual-regexp-steroids
#
# visual-regexp-steroids is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# visual-regexp-steroids is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with visual-regexp-steroids.  If not, see <http://www.gnu.org/licenses/>.

import sys, re, base64

# True if we are running on Python 3.
PY3 = sys.version_info[0] == 3

if not PY3:
    import codecs
    sys.stdout = codecs.getwriter('utf-8')(sys.stdout)
    sys.stdin = codecs.getreader('utf-8')(sys.stdin)

argv = sys.argv

# not using argparse because it is not in the stdlib of python2.7/3.1.
BOOL_ARGS = ('--eval', '--feedback', '--backwards')
STR_ARGS = ('--regexp', '--replace', )
INT_ARGS = ('--feedback-limit', )
def parse_arg(arg, required=True):
    if not required and arg not in sys.argv:
        return None
    if arg in BOOL_ARGS:
        return arg in sys.argv
    def lookahead():
        try:
            return sys.argv[sys.argv.index(arg)+1]
        except ValueError:
            raise Exception("Argument missing: %s" % arg)
    if arg in STR_ARGS:
        return lookahead()
    if arg in INT_ARGS:
        return int(lookahead())
    raise Exception("Unrecognized argument: %s" % arg)

def escape(s):
    return base64.b64encode(s.encode('utf8')).decode('utf8')

def message(msg):
    sys.stdout.write(escape(msg))
    sys.stdout.write('\n')

if argv[1] == 'matches':
    # output positions of matches

    regexp = parse_arg('--regexp')
    region = sys.stdin.read()

    if not PY3:
        regexp = regexp.decode('utf-8')

    feedback_limit = parse_arg('--feedback-limit', required=False)
    try:
        matches = list(re.finditer(regexp, region))
        if parse_arg('--backwards'):
            matches.reverse()
        for i, match in enumerate(matches):
            if feedback_limit is not None and i >= feedback_limit:
                break
            # show only if match length is nonzero
            #if match.start() != match.end():
            sys.stdout.write(' '.join("%s %s" % span for span in match.regs))
            sys.stdout.write('\n')
        if matches:
            message("%d matches" % len(matches))
        else:
            message("no match")
    except re.error as e:
        message("Invalid: %s" % e)

elif argv[1] == "replace":
    regexp = parse_arg('--regexp')
    replace = parse_arg('--replace')
    do_eval = parse_arg('--eval')
    feedback = parse_arg('--feedback')
    feedback_limit = parse_arg('--feedback-limit', required=False)
    region = sys.stdin.read()

    if not PY3:
        regexp = regexp.decode('utf-8')
        replace = replace.decode('utf-8')

    if do_eval:
        # use \1, \2 instead of m.group(0), m.group(1), ...
        replace = re.sub(r'\\(\d+)', r'm.group(\1)', replace)
    match_counter = [0]

    def eval_replace(match):
        _globals = {}
        # those variables can be used in the replacement expression
        _locals = {
            'm': match,
            'i': match_counter[0],
            }

        if do_eval:
            replacement = (str if PY3 else unicode)(eval(replace, _globals, _locals))
        else:
            replacement = match.expand(replace)
        # output one replacement per line
        #if not feedback or match.start() != match.end():
        sys.stdout.write("%s %s " % match.span())
        sys.stdout.write(escape(replacement))
        sys.stdout.write('\n')

        match_counter[0] += 1

        # return does not really matter, we are using re.sub only to have a callback on each match.
        return match.group(0)

    try:
        # call eval_replace on each match.
        # we cannot loop through and replace matches one by one (regexp replacing match.group(0))  because zero-width patterns (i.e. "(A(?=B))")
        # are not part of match.group(0) and the regexp would not match again.
        re.sub(regexp, eval_replace, region, count=feedback_limit if feedback and feedback_limit else 0)
        # this line is only for counting matches
        matches = len(list(re.finditer(regexp, region)))
        if feedback:
            if matches:
                message("%d matches" % matches)
            else:
                message("no match")
        else:
            message("replaced %d matches" % matches)
    except Exception as e:
        message("Invalid: %s" % e)
