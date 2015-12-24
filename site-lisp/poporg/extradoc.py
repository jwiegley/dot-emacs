#!/usr/bin/env python

"""\
Extract documentation from one or more Python sources.
Documentation lies in all unprefixed, sextuple-quoted strings.

Usage: extradoc.py [OPTION]... [SOURCE]...

Options:
  -c PREFIX     Common prefix for all output files.
  -s            Split output in directory PREFIX, obey #+FILE directives.
  -h            Produce an HTML file, either PREFIX.html or PREFIX/NAME.html.
  -o            Produce an Org file, either PREFIX.org or PREFIX/NAME.org.
  -p            Produce a PDF file, either PREFIX.pdf or PREFIX/NAME.pdf.
  -t            Produce a translation file, name will be PREFIX.pot.
  -v            Be verbose and repeat all of Emacs output.
  -D SYM        Define SYMbol as being True
  -D SYM=EXPR   Define SYMbol with the value of EXPR.
  -I TAGS       Only include sections having one of TAGS in their header.
  -X TAGS       Exclude sections having one of TAGS in their header.

If no SOURCE are given, the program reads and process standard input.
Option -c is mandatory.  If -h or -p are used and -o is not, file PREFIX.org
should not pre-exist, as the program internally writes it and then deletes it.

Some non-standard Org directives are recognized:
  #+FILE: NAME.org   Switch output to NAME.org, also requires -s.
  #+IF EXPR          Produce following lines only if EXPR is true, else skip.
  #+ELIF EXPR        Expected meaning within an #+IF block.
  #+ELSE             Expected meaning within an #+IF block.
  #+ENDIF            Expected meaning to end an #+IF block.

EXPRs above are Python expressions, eval context comes from -D options.
TAGS represents a comma-separated list of Org tags.  To get through, a line
should go through the #+IF system, not be within an excluded section, and if
any included sections is specified, then either be part of one of them or
within the introduction (that is, before the first header).
"""

import codecs
import os
import polib
import re
import sys
import tokenize

encoding = 'UTF-8'

# Within an #+IF [#+ELIF]... [#+ELSE] #+ENDIF structure, the state may
# vary between FALSE, TRUE and SKIP.  The state before the structure is
# saved on entry, and restored on exit.  The state is TRUE at the
# beginning of a file.  If the state before stacking was TRUE, it starts
# as FALSE within the structure; otherwise, the state starts as SKIP.
# States may only go from FALSE to any other state; or else, necessarily
# to SKIP.  Within a structure, the state can be TRUE at most once,
# indicating that the tested condition was true.  It can be FALSE
# earlier in the structure, and may only be SKIP after the TRUE segment.
FALSE, TRUE, SKIP = range(3)


class Main:
    prefix = None
    html = False
    org = False
    pdf = False
    pot = False
    split = False
    verbose = False
    included = set()
    excluded = set()

    def main(self, *arguments):

        # Decode options.
        self.context = Context()
        import getopt
        options, arguments = getopt.getopt(arguments, 'D:I:X:c:hopstv')
        for option, value in options:
            if option == '-D':
                if '=' in value:
                    sym, expr = value.split('=', 1)
                    self.context[sym.strip()] = eval(value, None, self.context)
                else:
                    self.context[value.strip()] = True
            elif option == '-I':
                self.included = set(tag.strip() for tag in value.split(','))
            elif option == '-X':
                self.excluded = set(tag.strip() for tag in value.split(','))
            elif option == '-c':
                self.prefix = value
            elif option == '-d':
                self.split = True
            elif option == '-h':
                self.html = True
            elif option == '-o':
                self.org = True
            elif option == '-p':
                self.pdf = True
            elif option == '-s':
                self.split = True
            elif option == '-t':
                self.pot = True
            elif option == '-v':
                self.verbose = True
        if not self.prefix:
            sys.exit("Option -c is mandatory.")
        if ((self.html or self.pdf) and not self.org
                and os.path.exists(self.prefix + '.org')):
            sys.exit("File %s.org exists and -o not specified." % self.prefix)

        # Prepare the work.
        if not self.split and (self.html or self.org or self.pdf):
            self.org_file = codecs.open(self.prefix + '.org', 'w', encoding)
        else:
            self.org_file = None
        if self.pot:
            self.po = polib.POFile()
            self.po.metadata = {
                'Project-Id-Version': '1.0',
                'Report-Msgid-Bugs-To': 'you@example.com',
                'POT-Creation-Date': '2007-10-18 14:00+0100',
                'PO-Revision-Date': '2007-10-18 14:00+0100',
                'Last-Translator': 'you <you@example.com>',
                'Language-Team': 'English <yourteam@example.com>',
                'MIME-Version': '1.0',
                'Content-Type': 'text/plain; charset=%s' % encoding,
                'Content-Transfer-Encoding': '8bit',
            }

        # Process all source files.
        if arguments:
            for argument in arguments:
                self.extract_org_fragments(
                    codecs.open(argument, 'r', encoding),
                    argument)
        else:
            self.extract_org_fragments(sys.stdin, '<stdin>')

        # Complete the work.
        if self.pot:
            self.po.save(self.prefix + '.pot')
        if self.org_file is not None:
            self.org_file.close()
        if not self.split:
            if self.html:
                self.launch_emacs([
                    self.prefix + '.org',
                    '--eval', '(setq org-export-allow-BIND t)',
                    '--eval', '(org-export-as-html nil)'])
            if self.pdf:
                self.launch_emacs([
                    self.prefix + '.org',
                    '--eval', '(setq org-export-allow-BIND t)',
                    '--eval', '(org-export-as-pdf nil)'])
            if (self.html or self.pdf) and not self.org:
                os.remove(self.prefix + '.org')

    def extract_org_fragments(self, file, name):
        # LEVEL not None means inhibit copy from that header level on.
        level = None
        for line in self.each_org_line(file, name):
            if line.startswith('#+FILE:'):
                if self.split:
                    if self.html or self.org or self.pdf:
                        name = line[7:].strip()
                        self.org_file = codecs.open(
                            '%s/%s' % (self.prefix, name), 'w', encoding)
                level = None
                continue
            if line.startswith('*'):
                match = re.match('^(\\*+).*?((:[a-z]+)+:)?$', line)
                if match:
                    here_level = len(match.group(1))
                    if level is None or here_level <= level:
                        if match.group(2):
                            tags = set(match.group(2).strip(':').split(':'))
                        else:
                            tags = set()
                        if tags & self.excluded:
                            level = here_level
                        elif self.included and not (tags & self.included):
                            level = here_level
                        else:
                            level = None
            if level is None and self.org_file is not None:
                self.org_file.write(line + '\n')

    def each_org_line(self, file, name):

        def if_bool(value):
            return (FALSE, TRUE)[bool(value)]

        def warn(diagnostic):
            sys.stderr.write('%s:%s %s\n' % (name, line_no, diagnostic))

        self.stack = []
        self.state = TRUE
        for (code, text, (line_no, _), _, _
             ) in tokenize.generate_tokens(file.readline):
            if code == tokenize.STRING:
                if text.startswith('"""'):
                    text = text[3:-3].replace('\\\n', '')
                    if self.pot:
                        self.po.append(polib.POEntry(
                            msgid=text,
                            occurrences=[(name, str(line_no))]))
                    for line in text.splitlines():
                        if line.startswith('#+IF '):
                            self.stack.append(self.state)
                            if self.state == TRUE:
                                value = eval(line[5:], self.context)
                                self.state = if_bool(value)
                            else:
                                self.state = SKIP
                        elif line.startswith('#+ELIF '):
                            if self.state == FALSE:
                                value = eval(line[7:], self.context)
                                self.state = if_bool(value)
                            else:
                                self.state = SKIP
                        elif line == '#+ELSE':
                            if self.state == FALSE:
                                self.state = TRUE
                            else:
                                self.state = SKIP
                        elif line == '#+ENDIF':
                            if self.stack:
                                self.state = self.stack.pop()
                            else:
                                warn("Spurious #+ENDIF line.")
                        elif self.state == TRUE:
                            if line.startswith('#+FILE:') and not self.split:
                                warn("#+FILE directive, and not -s.")
                            yield line
        if self.stack:
            sys.stderr.write("%s: Some #+ENDIF might be missing.\n" % name)

    def launch_emacs(self, args):
        import subprocess
        for raw in subprocess.Popen(
                ['emacs', '--batch'] + args,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT).stdout:
            try:
                line = raw.decode(encoding)
            except UnicodeDecodeError:
                line = raw.decode('ISO-8859-1')
            if not self.verbose:
                match = re.match('^Loading .*/([^/]+)\\.cache\\.\\.\\.$',
                                 line)
                if match:
                    sys.stderr.write("%s\n" % match.group(1))
                    continue
                if line.startswith((
                        # Common
                        'Loading ',
                        'OVERVIEW',
                        'Saving file ',
                        'Wrote ',
                        # PDF
                        'Exporting to ',
                        'LaTeX export done, ',
                        'Processing LaTeX file ',
                        # Web
                        '(No changes need to be saved)',
                        '(Shell command succeeded ',
                        'Exporting...',
                        'HTML export done, ',
                        'Publishing file ',
                        'Resetting org-publish-cache',
                        'Skipping unmodified file ')):
                    continue
            sys.stderr.write(line)


class Context(dict):
    "dict type which defaults to either builtin objects or False."

    def __getitem__(self, key):
        try:
            return dict.__getitem__(self, key)
        except KeyError:
            try:
                return getattr(__builtins__, key)
            except AttributeError:
                return False


run = Main()
main = run.main

if __name__ == '__main__':
    main(*sys.argv[1:])
