;;; python-mode-test.el --- tests for Emacs python-mode.el

;; Copyright (C) 2011  Andreas Roehler

;; Author: Andreas Roehler <andreas.roehler@online.de>
;; Keywords: lisp, languages

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; A couple of test cases for python-mode.el

;;; Code:

;; (require 'cl-macs.el)
;; delivers "assert"
(load "~/emacs-23.3/lisp/emacs-lisp/cl-macs.el")

(setq python-mode-syntax-tests
      (list
       'erste-tqs-syntax-test))

(defun py-run-syntax-tests (&optional arg)
  (interactive "p")
  (dolist (ele python-mode-syntax-tests)
    (funcall ele arg)))

(defun py-bug-tests-intern (testname &optional arg teststring)
  (if arg
      (progn
        (set-buffer (get-buffer-create (replace-regexp-in-string "-base$" "-test" (prin1-to-string testname))))
        (switch-to-buffer (current-buffer))
        (erase-buffer)
        (insert teststring)
        (fundamental-mode)
        ;; (message "%s" "fundamental mode")
        (python-mode)
        (funcall testname)
        (message "%s" (concat (replace-regexp-in-string "-base$" "-test" (prin1-to-string testname)) " passed"))
        (unless (< 1 arg)
          (set-buffer-modified-p 'nil)
          (cond ((processp (get-process "Python3")) (kill-process "Python3"))
                ((processp (get-process "Python2")) (kill-process "Python2"))
                ((processp (get-process "Python")) (kill-process "Python")))
          (kill-buffer (current-buffer))))
    (with-temp-buffer
      (let ((font-lock-verbose nil))
        (insert teststring)
        (funcall testname)))))

(defun erste-tqs-syntax-test (&optional arg load-branch-function)
  (interactive "p")
  (let ((teststring "# commands.py - command processing for mercurial
#
# Copyright 2005-2007 Matt Mackall <mpm@selenic.com>
#
# This software may be used and distributed according to the terms of the
# GNU General Public License version 2 or any later version.

from node import hex, bin, nullid, nullrev, short
from lock import release
from i18n import _, gettext
import os, re, difflib, time, tempfile, errno
import hg, scmutil, util, revlog, extensions, copies, error, bookmarks
import patch, help, url, encoding, templatekw, discovery
import archival, changegroup, cmdutil, hbisect
import sshserver, hgweb, hgweb.server, commandserver
import merge as mergemod
import minirst, revset, fileset
import dagparser, context, simplemerge
import random, setdiscovery, treediscovery, dagutil

table = {}

command = cmdutil.command(table)

# common command options

globalopts = [
    ('R', 'repository', '',
     _('repository root directory or name of overlay bundle file'),
     _('REPO')),
    ('', 'cwd', '',
     _('change working directory'), _('DIR')),
    ('y', 'noninteractive', None,
     _('do not prompt, assume \\'yes\\' for any required answers')),
    ('q', 'quiet', None, _('suppress output')),
    ('v', 'verbose', None, _('enable additional output')),
    ('', 'config', [],
     _('set/override config option (use \\'section.name=value\\')'),
     _('CONFIG')),
    ('', 'debug', None, _('enable debugging output')),
    ('', 'debugger', None, _('start debugger')),
    ('', 'encoding', encoding.encoding, _('set the charset encoding'),
     _('ENCODE')),
    ('', 'encodingmode', encoding.encodingmode,
     _('set the charset encoding mode'), _('MODE')),
    ('', 'traceback', None, _('always print a traceback on exception')),
    ('', 'time', None, _('time how long the command takes')),
    ('', 'profile', None, _('print command execution profile')),
    ('', 'version', None, _('output version information and exit')),
    ('h', 'help', None, _('display help and exit')),
]

dryrunopts = [('n', 'dry-run', None,
               _('do not perform actions, just print output'))]

remoteopts = [
    ('e', 'ssh', '',
     _('specify ssh command to use'), _('CMD')),
    ('', 'remotecmd', '',
     _('specify hg command to run on the remote side'), _('CMD')),
    ('', 'insecure', None,
     _('do not verify server certificate (ignoring web.cacerts config)')),
]

walkopts = [
    ('I', 'include', [],
     _('include names matching the given patterns'), _('PATTERN')),
    ('X', 'exclude', [],
     _('exclude names matching the given patterns'), _('PATTERN')),
]

commitopts = [
    ('m', 'message', '',
     _('use text as commit message'), _('TEXT')),
    ('l', 'logfile', '',
     _('read commit message from file'), _('FILE')),
]

commitopts2 = [
    ('d', 'date', '',
     _('record the specified date as commit date'), _('DATE')),
    ('u', 'user', '',
     _('record the specified user as committer'), _('USER')),
]

templateopts = [
    ('', 'style', '',
     _('display using template map file'), _('STYLE')),
    ('', 'template', '',
     _('display with template'), _('TEMPLATE')),
]

logopts = [
    ('p', 'patch', None, _('show patch')),
    ('g', 'git', None, _('use git extended diff format')),
    ('l', 'limit', '',
     _('limit number of changes displayed'), _('NUM')),
    ('M', 'no-merges', None, _('do not show merges')),
    ('', 'stat', None, _('output diffstat-style summary of changes')),
] + templateopts

diffopts = [
    ('a', 'text', None, _('treat all files as text')),
    ('g', 'git', None, _('use git extended diff format')),
    ('', 'nodates', None, _('omit dates from diff headers'))
]

diffopts2 = [
    ('p', 'show-function', None, _('show which function each change is in')),
    ('', 'reverse', None, _('produce a diff that undoes the changes')),
    ('w', 'ignore-all-space', None,
     _('ignore white space when comparing lines')),
    ('b', 'ignore-space-change', None,
     _('ignore changes in the amount of white space')),
    ('B', 'ignore-blank-lines', None,
     _('ignore changes whose lines are all blank')),
    ('U', 'unified', '',
     _('number of lines of context to show'), _('NUM')),
    ('', 'stat', None, _('output diffstat-style summary of changes')),
]

similarityopts = [
    ('s', 'similarity', '',
     _('guess renamed files by similarity (0<=s<=100)'), _('SIMILARITY'))
]

subrepoopts = [
    ('S', 'subrepos', None,
     _('recurse into subrepositories'))
]

# Commands start here, listed alphabetically

@command('^add',
    walkopts + subrepoopts + dryrunopts,
    _('[OPTION]... [FILE]...'))
def add(ui, repo, \*pats, \*\*opts):
    \"\"\"add the specified files on the next commit

    Schedule files to be version controlled and added to the
    repository.

    The files will be added to the repository at the next commit. To
    undo an add before that, see :hg:`forget`.

    If no names are given, add all files to the repository.

    .. container:: verbose

       An example showing how new (unknown) files are added
       automatically by :hg:`add`::

         \$ ls
         foo.c
         \$ hg status
         ? foo.c
         \$ hg add
         adding foo.c
         \$ hg status
         A foo.c

    Returns 0 if all files are successfully added.
    \"\"\"

    m = scmutil.match(repo[None], pats, opts)
    rejected = cmdutil.add(ui, repo, m, opts.get('dry_run'),
                           opts.get('subrepos'), prefix=\"\")
    return rejected and 1 or 0

@command('addremove',
    similarityopts + walkopts + dryrunopts,
    _('[OPTION]... [FILE]...'))
def addremove(ui, repo, \*pats, \*\*opts):
    \"\"\"add all new files, delete all missing files

    Add all new files and remove all missing files from the
    repository.

    New files are ignored if they match any of the patterns in
    ``.hgignore``. As with add, these changes take effect at the next
    commit.

    Use the -s/--similarity option to detect renamed files. With a
    parameter greater than 0, this compares every removed file with
    every added file and records those similar enough as renames. This
    option takes a percentage between 0 (disabled) and 100 (files must
    be identical) as its parameter. Detecting renamed files this way
    can be expensive. After using this option, :hg:`status -C` can be
    used to check which files were identified as moved or renamed.

    Returns 0 if all files are successfully added.
    \"\"\"
    try:
        sim = float(opts.get('similarity') or 100)
    except ValueError:
        raise util.Abort(_('similarity must be a number'))
    if sim < 0 or sim > 100:
        raise util.Abort(_('similarity must be between 0 and 100'))
    return scmutil.addremove(repo, pats, opts, similarity=sim / 100.0)

@command('^annotate|blame',
    [('r', 'rev', '', _('annotate the specified revision'), _('REV')),
    ('', 'follow', None,
     _('follow copies/renames and list the filename (DEPRECATED)')),
    ('', 'no-follow', None, _(\"don't follow copies and renames\")),
    ('a', 'text', None, _('treat all files as text')),
    ('u', 'user', None, _('list the author (long with -v)')),
    ('f', 'file', None, _('list the filename')),
    ('d', 'date', None, _('list the date (short with -q)')),
    ('n', 'number', None, _('list the revision number (default)')),
    ('c', 'changeset', None, _('list the changeset')),
    ('l', 'line-number', None, _('show line number at the first appearance'))
    ] + walkopts,
    _('[-r REV] [-f] [-a] [-u] [-d] [-n] [-c] [-l] FILE...'))
def annotate(ui, repo, \*pats, \*\*opts):
    \"\"\"show changeset information by line for each file

    List changes in files, showing the revision id responsible for
    each line

    This command is useful for discovering when a change was made and
    by whom.

    Without the -a/--text option, annotate will avoid processing files
    it detects as binary. With -a, annotate will annotate the file
    anyway, although the results will probably be neither useful
    nor desirable.

    Returns 0 on success.
    \"\"\"
    if opts.get('follow'):
        # --follow is deprecated and now just an alias for -f/--file
        # to mimic the behavior of Mercurial before version 1.5
        opts['file'] = True

    datefunc = ui.quiet and util.shortdate or util.datestr
    getdate = util.cachefunc(lambda x: datefunc(x[0].date()))

    if not pats:
        raise util.Abort(_('at least one filename or pattern is required'))

    opmap = [('user', ' ', lambda x: ui.shortuser(x[0].user())),
             ('number', ' ', lambda x: str(x[0].rev())),
             ('changeset', ' ', lambda x: short(x[0].node())),
             ('date', ' ', getdate),
             ('file', ' ', lambda x: x[0].path()),
             ('line_number', ':', lambda x: str(x[1])),
            ]

    if (not opts.get('user') and not opts.get('changeset')
        and not opts.get('date') and not opts.get('file')):
        opts['number'] = True

    linenumber = opts.get('line_number') is not None
    if linenumber and (not opts.get('changeset')) and (not opts.get('number')):
        raise util.Abort(_('at least one of -n/-c is required for -l'))

    funcmap = [(func, sep) for op, sep, func in opmap if opts.get(op)]
    funcmap[0] = (funcmap[0][0], '') # no separator in front of first column

    def bad(x, y):
        raise util.Abort(\"%s: %s\" % (x, y))

    ctx = scmutil.revsingle(repo, opts.get('rev'))
    m = scmutil.match(ctx, pats, opts)
    m.bad = bad
    follow = not opts.get('no_follow')
    for abs in ctx.walk(m):
        fctx = ctx[abs]
        if not opts.get('text') and util.binary(fctx.data()):
            ui.write(_(\"%s: binary file\\n\") % ((pats and m.rel(abs)) or abs))
            continue

        lines = fctx.annotate(follow=follow, linenumber=linenumber)
        pieces = []

        for f, sep in funcmap:
            l = [f(n) for n, dummy in lines]
            if l:
                sized = [(x, encoding.colwidth(x)) for x in l]
                ml = max([w for x, w in sized])
                pieces.append([\"%s%s%s\" % (sep, ' ' \* (ml - w), x)
                               for x, w in sized])

        if pieces:
            for p, l in zip(zip(\*pieces), lines):
                ui.write(\"%s: %s\" % (\"\".join(p), l[1]))

@command('archive',
    [('', 'no-decode', None, _('do not pass files through decoders')),
    ('p', 'prefix', '', _('directory prefix for files in archive'),
     _('PREFIX')),
    ('r', 'rev', '', _('revision to distribute'), _('REV')),
    ('t', 'type', '', _('type of distribution to create'), _('TYPE')),
    ] + subrepoopts + walkopts,
    _('[OPTION]... DEST'))
def archive(ui, repo, dest, \*\*opts):
    '''create an unversioned archive of a repository revision

    By default, the revision used is the parent of the working
    directory; use -r/--rev to specify a different revision.

    The archive type is automatically detected based on file
    extension (or override using -t/--type).

    Valid types are:

    :``files``: a directory full of files (default)
    :``tar``:   tar archive, uncompressed
    :``tbz2``:  tar archive, compressed using bzip2
    :``tgz``:   tar archive, compressed using gzip
    :``uzip``:  zip archive, uncompressed
    :``zip``:   zip archive, compressed using deflate

    The exact name of the destination archive or directory is given
    using a format string; see :hg:`help export` for details.

    Each member added to an archive file has a directory prefix
    prepended. Use -p/--prefix to specify a format string for the
    prefix. The default is the basename of the archive, with suffixes
    removed.

    Returns 0 on success.
    '''

    ctx = scmutil.revsingle(repo, opts.get('rev'))
    if not ctx:
        raise util.Abort(_('no working directory: please specify a revision'))
    node = ctx.node()
    dest = cmdutil.makefilename(repo, dest, node)
    if os.path.realpath(dest) == repo.root:
        raise util.Abort(_('repository root cannot be destination'))

    kind = opts.get('type') or archival.guesskind(dest) or 'files'
    prefix = opts.get('prefix')

    if dest == '-':
        if kind == 'files':
            raise util.Abort(_('cannot archive plain files to stdout'))
        dest = cmdutil.makefileobj(repo, dest)
        if not prefix:
            prefix = os.path.basename(repo.root) + '-%h'

    prefix = cmdutil.makefilename(repo, prefix, node)
    matchfn = scmutil.match(ctx, [], opts)
    archival.archive(repo, dest, node, kind, not opts.get('no_decode'),
                     matchfn, prefix, subrepos=opts.get('subrepos'))

@command('backout',
    [('', 'merge', None, _('merge with old dirstate parent after backout')),
    ('', 'parent', '', _('parent to choose when backing out merge'), _('REV')),
    ('t', 'tool', '', _('specify merge tool')),
    ('r', 'rev', '', _('revision to backout'), _('REV')),
    ] + walkopts + commitopts + commitopts2,
    _('[OPTION]... [-r] REV'))
def backout(ui, repo, node=None, rev=None, \*\*opts):
    '''reverse effect of earlier changeset

    Prepare a new changeset with the effect of REV undone in the
    current working directory.

    If REV is the parent of the working directory, then this new changeset
    is committed automatically. Otherwise, hg needs to merge the
    changes and the merged result is left uncommitted.

    By default, the pending changeset will have one parent,
    maintaining a linear history. With --merge, the pending changeset
    will instead have two parents: the old parent of the working
    directory and a new child of REV that simply undoes REV.

    Before version 1.7, the behavior without --merge was equivalent to
    specifying --merge followed by :hg:`update --clean .` to cancel
    the merge and leave the child of REV as a head to be merged
    separately.

    See :hg:`help dates` for a list of formats valid for -d/--date.

    Returns 0 on success.
    '''
    if rev and node:
        raise util.Abort(_(\"please specify just one revision\"))

    if not rev:
        rev = node

    if not rev:
        raise util.Abort(_(\"please specify a revision to backout\"))

    date = opts.get('date')
    if date:
        opts['date'] = util.parsedate(date)

    cmdutil.bailifchanged(repo)
    node = scmutil.revsingle(repo, rev).node()

    op1, op2 = repo.dirstate.parents()
    a = repo.changelog.ancestor(op1, node)
    if a != node:
        raise util.Abort(_('cannot backout change on a different branch'))

    p1, p2 = repo.changelog.parents(node)
    if p1 == nullid:
        raise util.Abort(_('cannot backout a change with no parents'))
    if p2 != nullid:
        if not opts.get('parent'):
            raise util.Abort(_('cannot backout a merge changeset without '
                               '--parent'))
        p = repo.lookup(opts['parent'])
        if p not in (p1, p2):
            raise util.Abort(_('%s is not a parent of %s') %
                             (short(p), short(node)))
        parent = p
    else:
        if opts.get('parent'):
            raise util.Abort(_('cannot use --parent on non-merge changeset'))
        parent = p1

    # the backout should appear on the same branch
    branch = repo.dirstate.branch()
    hg.clean(repo, node, show_stats=False)
    repo.dirstate.setbranch(branch)
    revert_opts = opts.copy()
    revert_opts['date'] = None
    revert_opts['all'] = True
    revert_opts['rev'] = hex(parent)
    revert_opts['no_backup'] = None
    revert(ui, repo, \*\*revert_opts)
    if not opts.get('merge') and op1 != node:
        try:
            ui.setconfig('ui', 'forcemerge', opts.get('tool', ''))
            return hg.update(repo, op1)
        finally:
            ui.setconfig('ui', 'forcemerge', '')

    commit_opts = opts.copy()
    commit_opts['addremove'] = False
    if not commit_opts['message'] and not commit_opts['logfile']:
        # we don't translate commit messages
        commit_opts['message'] = \"Backed out changeset %s\" % short(node)
        commit_opts['force_editor'] = True
    commit(ui, repo, \*\*commit_opts)
    def nice(node):
        return '%d:%s' % (repo.changelog.rev(node), short(node))
    ui.status(_('changeset %s backs out changeset %s\\n') %
              (nice(repo.changelog.tip()), nice(node)))
    if opts.get('merge') and op1 != node:
        hg.clean(repo, op1, show_stats=False)
        ui.status(_('merging with changeset %s\\n')
                  % nice(repo.changelog.tip()))
        try:
            ui.setconfig('ui', 'forcemerge', opts.get('tool', ''))
            return hg.merge(repo, hex(repo.changelog.tip()))
        finally:
            ui.setconfig('ui', 'forcemerge', '')
    return 0

@command('bisect',
    [('r', 'reset', False, _('reset bisect state')),
    ('g', 'good', False, _('mark changeset good')),
    ('b', 'bad', False, _('mark changeset bad')),
    ('s', 'skip', False, _('skip testing changeset')),
    ('e', 'extend', False, _('extend the bisect range')),
    ('c', 'command', '', _('use command to check changeset state'), _('CMD')),
    ('U', 'noupdate', False, _('do not update to target'))],
    _(\"[-gbsr] [-U] [-c CMD] [REV]\"))
def bisect(ui, repo, rev=None, extra=None, command=None,
               reset=None, good=None, bad=None, skip=None, extend=None,
               noupdate=None):
    \"\"\"subdivision search of changesets

    This command helps to find changesets which introduce problems. To
    use, mark the earliest changeset you know exhibits the problem as
    bad, then mark the latest changeset which is free from the problem
    as good. Bisect will update your working directory to a revision
    for testing (unless the -U/--noupdate option is specified). Once
    you have performed tests, mark the working directory as good or
    bad, and bisect will either update to another candidate changeset
    or announce that it has found the bad revision.

    As a shortcut, you can also use the revision argument to mark a
    revision as good or bad without checking it out first.

    If you supply a command, it will be used for automatic bisection.
    Its exit status will be used to mark revisions as good or bad:
    status 0 means good, 125 means to skip the revision, 127
    (command not found) will abort the bisection, and any other
    non-zero exit status means the revision is bad.

    Returns 0 on success.
    \"\"\"
    def extendbisectrange(nodes, good):
        # bisect is incomplete when it ends on a merge node and
        # one of the parent was not checked.
        parents = repo[nodes[0]].parents()
        if len(parents) > 1:
            side = good and state['bad'] or state['good']
            num = len(set(i.node() for i in parents) & set(side))
            if num == 1:
                return parents[0].ancestor(parents[1])
        return None

    def print_result(nodes, good):
        displayer = cmdutil.show_changeset(ui, repo, {})
        if len(nodes) == 1:
            # narrowed it down to a single revision
            if good:
                ui.write(_(\"The first good revision is:\\n\"))
            else:
                ui.write(_(\"The first bad revision is:\\n\"))
            displayer.show(repo[nodes[0]])
            extendnode = extendbisectrange(nodes, good)
            if extendnode is not None:
                ui.write(_('Not all ancestors of this changeset have been'
                           ' checked.\\nUse bisect --extend to continue the '
                           'bisection from\\nthe common ancestor, %s.\\n')
                         % extendnode)
        else:
            # multiple possible revisions
            if good:
                ui.write(_(\"Due to skipped revisions, the first \"
                        \"good revision could be any of:\\n\"))
            else:
                ui.write(_(\"Due to skipped revisions, the first \"
                        \"bad revision could be any of:\\n\"))
            for n in nodes:
                displayer.show(repo[n])
        displayer.close()

    def check_state(state, interactive=True):
        if not state['good'] or not state['bad']:
            if (good or bad or skip or reset) and interactive:
                return
            if not state['good']:
                raise util.Abort(_('cannot bisect (no known good revisions)'))
            else:
                raise util.Abort(_('cannot bisect (no known bad revisions)'))
        return True

    # backward compatibility
    if rev in \"good bad reset init\".split():
        ui.warn(_(\"(use of 'hg bisect <cmd>' is deprecated)\\n\"))
        cmd, rev, extra = rev, extra, None
        if cmd == \"good\":
            good = True
        elif cmd == \"bad\":
            bad = True
        else:
            reset = True
    elif extra or good + bad + skip + reset + extend + bool(command) > 1:
        raise util.Abort(_('incompatible arguments'))

    if reset:
        p = repo.join(\"bisect.state\")
        if os.path.exists(p):
            os.unlink(p)
        return

    state = hbisect.load_state(repo)

    if command:
        changesets = 1
        try:
            while changesets:
                # update state
                status = util.system(command, out=ui.fout)
                if status == 125:
                    transition = \"skip\"
                elif status == 0:
                    transition = \"good\"
                # status < 0 means process was killed
                elif status == 127:
                    raise util.Abort(_(\"failed to execute %s\") % command)
                elif status < 0:
                    raise util.Abort(_(\"%s killed\") % command)
                else:
                    transition = \"bad\"
                ctx = scmutil.revsingle(repo, rev)
                rev = None # clear for future iterations
                state[transition].append(ctx.node())
                ui.status(_('Changeset %d:%s: %s\\n') % (ctx, ctx, transition))
                check_state(state, interactive=False)
                # bisect
                nodes, changesets, good = hbisect.bisect(repo.changelog, state)
                # update to next check
                cmdutil.bailifchanged(repo)
                hg.clean(repo, nodes[0], show_stats=False)
        finally:
            hbisect.save_state(repo, state)
        print_result(nodes, good)
        return

    # update state

    if rev:
        nodes = [repo.lookup(i) for i in scmutil.revrange(repo, [rev])]
    else:
        nodes = [repo.lookup('.')]

    if good or bad or skip:
        if good:
            state['good'] += nodes
        elif bad:
            state['bad'] += nodes
        elif skip:
            state['skip'] += nodes
        hbisect.save_state(repo, state)

    if not check_state(state):
        return

    # actually bisect
    nodes, changesets, good = hbisect.bisect(repo.changelog, state)
    if extend:
        if not changesets:
            extendnode = extendbisectrange(nodes, good)
            if extendnode is not None:
                ui.write(_(\"Extending search to changeset %d:%s\\n\"
                         % (extendnode.rev(), extendnode)))
                if noupdate:
                    return
                cmdutil.bailifchanged(repo)
                return hg.clean(repo, extendnode.node())
        raise util.Abort(_(\"nothing to extend\"))

    if changesets == 0:
        print_result(nodes, good)
    else:
        assert len(nodes) == 1 # only a single node can be tested next
        node = nodes[0]
        # compute the approximate number of remaining tests
        tests, size = 0, 2
        while size <= changesets:
            tests, size = tests + 1, size \* 2
        rev = repo.changelog.rev(node)
        ui.write(_(\"Testing changeset %d:%s \"
                   \"(%d changesets remaining, ~%d tests)\\n\")
                 % (rev, short(node), changesets, tests))
        if not noupdate:
            cmdutil.bailifchanged(repo)
            return hg.clean(repo, node)

@command('bookmarks',
    [('f', 'force', False, _('force')),
    ('r', 'rev', '', _('revision'), _('REV')),
    ('d', 'delete', False, _('delete a given bookmark')),
    ('m', 'rename', '', _('rename a given bookmark'), _('NAME')),
    ('i', 'inactive', False, _('do not mark a new bookmark active'))],
    _('hg bookmarks [-f] [-d] [-i] [-m NAME] [-r REV] [NAME]'))
def bookmark(ui, repo, mark=None, rev=None, force=False, delete=False,
             rename=None, inactive=False):
    '''track a line of development with movable markers

    Bookmarks are pointers to certain commits that move when
    committing. Bookmarks are local. They can be renamed, copied and
    deleted. It is possible to use bookmark names in :hg:`merge` and
    :hg:`update` to merge and update respectively to a given bookmark.

    You can use :hg:`bookmark NAME` to set a bookmark on the working
    directory's parent revision with the given name. If you specify
    a revision using -r REV (where REV may be an existing bookmark),
    the bookmark is assigned to that revision.

    Bookmarks can be pushed and pulled between repositories (see :hg:`help
    push` and :hg:`help pull`). This requires both the local and remote
    repositories to support bookmarks. For versions prior to 1.8, this means
    the bookmarks extension must be enabled.
    '''
    hexfn = ui.debugflag and hex or short
    marks = repo._bookmarks
    cur = repo.changectx('.').node()

    if rename:
        if rename not in marks:
            raise util.Abort(_(\"bookmark '%s' does not exist\") % rename)
        if mark in marks and not force:
            raise util.Abort(_(\"bookmark '%s' already exists \"
                               \"(use -f to force)\") % mark)
        if mark is None:
            raise util.Abort(_(\"new bookmark name required\"))
        marks[mark] = marks[rename]
        if repo._bookmarkcurrent == rename and not inactive:
            bookmarks.setcurrent(repo, mark)
        del marks[rename]
        bookmarks.write(repo)
        return

    if delete:
        if mark is None:
            raise util.Abort(_(\"bookmark name required\"))
        if mark not in marks:
            raise util.Abort(_(\"bookmark '%s' does not exist\") % mark)
        if mark == repo._bookmarkcurrent:
            bookmarks.setcurrent(repo, None)
        del marks[mark]
        bookmarks.write(repo)
        return

    if mark is not None:
        if \"\\n\" in mark:
            raise util.Abort(_(\"bookmark name cannot contain newlines\"))
        mark = mark.strip()
        if not mark:
            raise util.Abort(_(\"bookmark names cannot consist entirely of \"
                               \"whitespace\"))
        if inactive and mark == repo._bookmarkcurrent:
            bookmarks.setcurrent(repo, None)
            return
        if mark in marks and not force:
            raise util.Abort(_(\"bookmark '%s' already exists \"
                               \"(use -f to force)\") % mark)
        if ((mark in repo.branchtags() or mark == repo.dirstate.branch())
            and not force):
            raise util.Abort(
                _(\"a bookmark cannot have the name of an existing branch\"))
        if rev:
            marks[mark] = repo.lookup(rev)
        else:
            marks[mark] = repo.changectx('.').node()
        if not inactive and repo.changectx('.').node() == marks[mark]:
            bookmarks.setcurrent(repo, mark)
        bookmarks.write(repo)
        return

    if mark is None:
        if rev:
            raise util.Abort(_(\"bookmark name required\"))
        if len(marks) == 0:
            ui.status(_(\"no bookmarks set\\n\"))
        else:
            for bmark, n in sorted(marks.iteritems()):
                current = repo._bookmarkcurrent
                if bmark == current and n == cur:
                    prefix, label = '\*', 'bookmarks.current'
                else:
                    prefix, label = ' ', ''

                if ui.quiet:
                    ui.write(\"%s\\n\" % bmark, label=label)
                else:
                    ui.write(\" %s %-25s %d:%s\\n\" % (
                        prefix, bmark, repo.changelog.rev(n), hexfn(n)),
                        label=label)
        return

@command('branch',
    [('f', 'force', None,
     _('set branch name even if it shadows an existing branch')),
    ('C', 'clean', None, _('reset branch name to parent branch name'))],
    _('[-fC] [NAME]'))
def branch(ui, repo, label=None, \*\*opts):
    \"\"\"set or show the current branch name

    With no argument, show the current branch name. With one argument,
    set the working directory branch name (the branch will not exist
    in the repository until the next commit). Standard practice
    recommends that primary development take place on the 'default'
    branch.

    Unless -f/--force is specified, branch will not let you set a
    branch name that already exists, even if it's inactive.

    Use -C/--clean to reset the working directory branch to that of
    the parent of the working directory, negating a previous branch
    change.

    Use the command :hg:`update` to switch to an existing branch. Use
    :hg:`commit --close-branch` to mark this branch as closed.

    .. note::

       Branch names are permanent. Use :hg:`bookmark` to create a
       light-weight bookmark instead. See :hg:`help glossary` for more
       information about named branches and bookmarks.

    Returns 0 on success.
    \"\"\"

    if opts.get('clean'):
        label = repo[None].p1().branch()
        repo.dirstate.setbranch(label)
        ui.status(_('reset working directory to branch %s\\n') % label)
    elif label:
        if not opts.get('force') and label in repo.branchtags():
            if label not in [p.branch() for p in repo.parents()]:
                raise util.Abort(_('a branch of the same name already exists'),
                                 # i18n: \"it\" refers to an existing branch
                                 hint=_(\"use 'hg update' to switch to it\"))
        repo.dirstate.setbranch(label)
        ui.status(_('marked working directory as branch %s\\n') % label)
    else:
        ui.write(\"%s\\n\" % repo.dirstate.branch())

@command('branches',
    [('a', 'active', False, _('show only branches that have unmerged heads')),
    ('c', 'closed', False, _('show normal and closed branches'))],
    _('[-ac]'))
def branches(ui, repo, active=False, closed=False):
    \"\"\"list repository named branches

    List the repository's named branches, indicating which ones are
    inactive. If -c/--closed is specified, also list branches which have
    been marked closed (see :hg:`commit --close-branch`).

    If -a/--active is specified, only show active branches. A branch
    is considered active if it contains repository heads.

    Use the command :hg:`update` to switch to an existing branch.

    Returns 0.
    \"\"\"

    hexfunc = ui.debugflag and hex or short
    activebranches = [repo[n].branch() for n in repo.heads()]
    def testactive(tag, node):
        realhead = tag in activebranches
        open = node in repo.branchheads(tag, closed=False)
        return realhead and open
    branches = sorted([(testactive(tag, node), repo.changelog.rev(node), tag)
                          for tag, node in repo.branchtags().items()],
                      reverse=True)

    for isactive, node, tag in branches:
        if (not active) or isactive:
            if ui.quiet:
                ui.write(\"%s\\n\" % tag)
            else:
                hn = repo.lookup(node)
                if isactive:
                    label = 'branches.active'
                    notice = ''
                elif hn not in repo.branchheads(tag, closed=False):
                    if not closed:
                        continue
                    label = 'branches.closed'
                    notice = _(' (closed)')
                else:
                    label = 'branches.inactive'
                    notice = _(' (inactive)')
                if tag == repo.dirstate.branch():
                    label = 'branches.current'
                rev = str(node).rjust(31 - encoding.colwidth(tag))
                rev = ui.label('%s:%s' % (rev, hexfunc(hn)), 'log.changeset')
                tag = ui.label(tag, label)
                ui.write(\"%s %s%s\\n\" % (tag, rev, notice))

@command('bundle',
    [('f', 'force', None, _('run even when the destination is unrelated')),
    ('r', 'rev', [], _('a changeset intended to be added to the destination'),
     _('REV')),
    ('b', 'branch', [], _('a specific branch you would like to bundle'),
     _('BRANCH')),
    ('', 'base', [],
     _('a base changeset assumed to be available at the destination'),
     _('REV')),
    ('a', 'all', None, _('bundle all changesets in the repository')),
    ('t', 'type', 'bzip2', _('bundle compression type to use'), _('TYPE')),
    ] + remoteopts,
    _('[-f] [-t TYPE] [-a] [-r REV]... [--base REV]... FILE [DEST]'))
def bundle(ui, repo, fname, dest=None, \*\*opts):
    \"\"\"create a changegroup file

    Generate a compressed changegroup file collecting changesets not
    known to be in another repository.

    If you omit the destination repository, then hg assumes the
    destination will have all the nodes you specify with --base
    parameters. To create a bundle containing all changesets, use
    -a/--all (or --base null).

    You can change compression method with the -t/--type option.
    The available compression methods are: none, bzip2, and
    gzip (by default, bundles are compressed using bzip2).

    The bundle file can then be transferred using conventional means
    and applied to another repository with the unbundle or pull
    command. This is useful when direct push and pull are not
    available or when exporting an entire repository is undesirable.

    Applying bundles preserves all changeset contents including
    permissions, copy/rename information, and revision history.

    Returns 0 on success, 1 if no changes found.
    \"\"\"
    revs = None
    if 'rev' in opts:
        revs = scmutil.revrange(repo, opts['rev'])

    if opts.get('all'):
        base = ['null']
    else:
        base = scmutil.revrange(repo, opts.get('base'))
    if base:
        if dest:
            raise util.Abort(_(\"--base is incompatible with specifying \"
                               \"a destination\"))
        common = [repo.lookup(rev) for rev in base]
        heads = revs and map(repo.lookup, revs) or revs
    else:
        dest = ui.expandpath(dest or 'default-push', dest or 'default')
        dest, branches = hg.parseurl(dest, opts.get('branch'))
        other = hg.peer(repo, opts, dest)
        revs, checkout = hg.addbranchrevs(repo, other, branches, revs)
        heads = revs and map(repo.lookup, revs) or revs
        common, outheads = discovery.findcommonoutgoing(repo, other,
                                                        onlyheads=heads,
                                                        force=opts.get('force'))

    cg = repo.getbundle('bundle', common=common, heads=heads)
    if not cg:
        ui.status(_(\"no changes found\\n\"))
        return 1

    bundletype = opts.get('type', 'bzip2').lower()
    btypes = {'none': 'HG10UN', 'bzip2': 'HG10BZ', 'gzip': 'HG10GZ'}
    bundletype = btypes.get(bundletype)
    if bundletype not in changegroup.bundletypes:
        raise util.Abort(_('unknown bundle type specified with --type'))

    changegroup.writebundle(cg, fname, bundletype)

@command('cat',
    [('o', 'output', '',
     _('print output to file with formatted name'), _('FORMAT')),
    ('r', 'rev', '', _('print the given revision'), _('REV')),
    ('', 'decode', None, _('apply any matching decode filter')),
    ] + walkopts,
    _('[OPTION]... FILE...'))
def cat(ui, repo, file1, \*pats, \*\*opts):
    \"\"\"output the current or given revision of files

    Print the specified files as they were at the given revision. If
    no revision is given, the parent of the working directory is used,
    or tip if no revision is checked out.

    Output may be to a file, in which case the name of the file is
    given using a format string. The formatting rules are the same as
    for the export command, with the following additions:

    :``%s``: basename of file being printed
    :``%d``: dirname of file being printed, or '.' if in repository root
    :``%p``: root-relative path name of file being printed

    Returns 0 on success.
    \"\"\"
    ctx = scmutil.revsingle(repo, opts.get('rev'))
    err = 1
    m = scmutil.match(ctx, (file1,) + pats, opts)
    for abs in ctx.walk(m):
        fp = cmdutil.makefileobj(repo, opts.get('output'), ctx.node(),
                                 pathname=abs)
        data = ctx[abs].data()
        if opts.get('decode'):
            data = repo.wwritedata(abs, data)
        fp.write(data)
        fp.close()
        err = 0
    return err

@command('^clone',
    [('U', 'noupdate', None,
     _('the clone will include an empty working copy (only a repository)')),
    ('u', 'updaterev', '', _('revision, tag or branch to check out'), _('REV')),
    ('r', 'rev', [], _('include the specified changeset'), _('REV')),
    ('b', 'branch', [], _('clone only the specified branch'), _('BRANCH')),
    ('', 'pull', None, _('use pull protocol to copy metadata')),
    ('', 'uncompressed', None, _('use uncompressed transfer (fast over LAN)')),
    ] + remoteopts,
    _('[OPTION]... SOURCE [DEST]'))
def clone(ui, source, dest=None, \*\*opts):
    \"\"\"make a copy of an existing repository

    Create a copy of an existing repository in a new directory.

    If no destination directory name is specified, it defaults to the
    basename of the source.

    The location of the source is added to the new repository's
    ``.hg/hgrc`` file, as the default to be used for future pulls.

    See :hg:`help urls` for valid source format details.

    It is possible to specify an ``ssh://`` URL as the destination, but no
    ``.hg/hgrc`` and working directory will be created on the remote side.
    Please see :hg:`help urls` for important details about ``ssh://`` URLs.

    A set of changesets (tags, or branch names) to pull may be specified
    by listing each changeset (tag, or branch name) with -r/--rev.
    If -r/--rev is used, the cloned repository will contain only a subset
    of the changesets of the source repository. Only the set of changesets
    defined by all -r/--rev options (including all their ancestors)
    will be pulled into the destination repository.
    No subsequent changesets (including subsequent tags) will be present
    in the destination.

    Using -r/--rev (or 'clone src#rev dest') implies --pull, even for
    local source repositories.

    For efficiency, hardlinks are used for cloning whenever the source
    and destination are on the same filesystem (note this applies only
    to the repository data, not to the working directory). Some
    filesystems, such as AFS, implement hardlinking incorrectly, but
    do not report errors. In these cases, use the --pull option to
    avoid hardlinking.

    In some cases, you can clone repositories and the working directory
    using full hardlinks with ::

      \$ cp -al REPO REPOCLONE

    This is the fastest way to clone, but it is not always safe. The
    operation is not atomic (making sure REPO is not modified during
    the operation is up to you) and you have to make sure your editor
    breaks hardlinks (Emacs and most Linux Kernel tools do so). Also,
    this is not compatible with certain extensions that place their
    metadata under the .hg directory, such as mq.

    Mercurial will update the working directory to the first applicable
    revision from this list:

    a) null if -U or the source repository has no changesets
    b) if -u . and the source repository is local, the first parent of
       the source repository's working directory
    c) the changeset specified with -u (if a branch name, this means the
       latest head of that branch)
    d) the changeset specified with -r
    e) the tipmost head specified with -b
    f) the tipmost head specified with the url#branch source syntax
    g) the tipmost head of the default branch
    h) tip

    Returns 0 on success.
    \"\"\"
    if opts.get('noupdate') and opts.get('updaterev'):
        raise util.Abort(_(\"cannot specify both --noupdate and --updaterev\"))

    r = hg.clone(ui, opts, source, dest,
                 pull=opts.get('pull'),
                 stream=opts.get('uncompressed'),
                 rev=opts.get('rev'),
                 update=opts.get('updaterev') or not opts.get('noupdate'),
                 branch=opts.get('branch'))

    return r is None

@command('^commit|ci',
    [('A', 'addremove', None,
     _('mark new/missing files as added/removed before committing')),
    ('', 'close-branch', None,
     _('mark a branch as closed, hiding it from the branch list')),
    ] + walkopts + commitopts + commitopts2,
    _('[OPTION]... [FILE]...'))
def commit(ui, repo, \*pats, \*\*opts):
    \"\"\"commit the specified files or all outstanding changes

    Commit changes to the given files into the repository. Unlike a
    centralized SCM, this operation is a local operation. See
    :hg:`push` for a way to actively distribute your changes.

    If a list of files is omitted, all changes reported by :hg:`status`
    will be committed.

    If you are committing the result of a merge, do not provide any
    filenames or -I/-X filters.

    If no commit message is specified, Mercurial starts your
    configured editor where you can enter a message. In case your
    commit fails, you will find a backup of your message in
    ``.hg/last-message.txt``.

    See :hg:`help dates` for a list of formats valid for -d/--date.

    Returns 0 on success, 1 if nothing changed.
    \"\"\"
    extra = {}
    if opts.get('close_branch'):
        if repo['.'].node() not in repo.branchheads():
            # The topo heads set is included in the branch heads set of the
            # current branch, so it's sufficient to test branchheads
            raise util.Abort(_('can only close branch heads'))
        extra['close'] = 1
    e = cmdutil.commiteditor
    if opts.get('force_editor'):
        e = cmdutil.commitforceeditor

    def commitfunc(ui, repo, message, match, opts):
        return repo.commit(message, opts.get('user'), opts.get('date'), match,
                           editor=e, extra=extra)

    branch = repo[None].branch()
    bheads = repo.branchheads(branch)

    node = cmdutil.commit(ui, repo, commitfunc, pats, opts)
    if not node:
        stat = repo.status(match=scmutil.match(repo[None], pats, opts))
        if stat[3]:
            ui.status(_(\"nothing changed (%d missing files, see 'hg status')\\n\")
                      % len(stat[3]))
        else:
            ui.status(_(\"nothing changed\\n\"))
        return 1

    ctx = repo[node]
    parents = ctx.parents()

    if bheads and not [x for x in parents
                       if x.node() in bheads and x.branch() == branch]:
        ui.status(_('created new head\\n'))
        # The message is not printed for initial roots. For the other
        # changesets, it is printed in the following situations:
        #
        # Par column: for the 2 parents with ...
        #   N: null or no parent
        #   B: parent is on another named branch
        #   C: parent is a regular non head changeset
        #   H: parent was a branch head of the current branch
        # Msg column: whether we print \"created new head\" message
        # In the following, it is assumed that there already exists some
        # initial branch heads of the current branch, otherwise nothing is
        # printed anyway.
        #
        # Par Msg Comment
        # NN y additional topo root
        #
        # BN y additional branch root
        # CN y additional topo head
        # HN n usual case
        #
        # BB y weird additional branch root
        # CB y branch merge
        # HB n merge with named branch
        #
        # CC y additional head from merge
        # CH n merge with a head
        #
        # HH n head merge: head count decreases

    if not opts.get('close_branch'):
        for r in parents:
            if r.extra().get('close') and r.branch() == branch:
                ui.status(_('reopening closed branch head %d\\n') % r)

    if ui.debugflag:
        ui.write(_('committed changeset %d:%s\\n') % (int(ctx), ctx.hex()))
    elif ui.verbose:
        ui.write(_('committed changeset %d:%s\\n') % (int(ctx), ctx))

@command('copy|cp',
    [('A', 'after', None, _('record a copy that has already occurred')),
    ('f', 'force', None, _('forcibly copy over an existing managed file')),
    ] + walkopts + dryrunopts,
    _('[OPTION]... [SOURCE]... DEST'))
def copy(ui, repo, \*pats, \*\*opts):
    \"\"\"mark files as copied for the next commit

    Mark dest as having copies of source files. If dest is a
    directory, copies are put in that directory. If dest is a file,
    the source must be a single file.

    By default, this command copies the contents of files as they
    exist in the working directory. If invoked with -A/--after, the
    operation is recorded, but no copying is performed.

    This command takes effect with the next commit. To undo a copy
    before that, see :hg:`revert`.

    Returns 0 on success, 1 if errors are encountered.
    \"\"\"
    wlock = repo.wlock(False)
    try:
        return cmdutil.copy(ui, repo, pats, opts)
    finally:
        wlock.release()

@command('debugancestor', [], _('[INDEX] REV1 REV2'))
def debugancestor(ui, repo, \*args):
    \"\"\"find the ancestor revision of two revisions in a given index\"\"\"
    if len(args) == 3:
        index, rev1, rev2 = args
        r = revlog.revlog(scmutil.opener(os.getcwd(), audit=False), index)
        lookup = r.lookup
    elif len(args) == 2:
        if not repo:
            raise util.Abort(_(\"there is no Mercurial repository here \"
                               \"(.hg not found)\"))
        rev1, rev2 = args
        r = repo.changelog
        lookup = repo.lookup
    else:
        raise util.Abort(_('either two or three arguments required'))
    a = r.ancestor(lookup(rev1), lookup(rev2))
    ui.write(\"%d:%s\\n\" % (r.rev(a), hex(a)))

@command('debugbuilddag',
    [('m', 'mergeable-file', None, _('add single file mergeable changes')),
    ('o', 'overwritten-file', None, _('add single file all revs overwrite')),
    ('n', 'new-file', None, _('add new file at each rev'))],
    _('[OPTION]... [TEXT]'))
def debugbuilddag(ui, repo, text=None,
                  mergeable_file=False,
                  overwritten_file=False,
                  new_file=False):
    \"\"\"builds a repo with a given DAG from scratch in the current empty repo

    The description of the DAG is read from stdin if not given on the
    command line.

    Elements:

     - \"+n\" is a linear run of n nodes based on the current default parent
     - \".\" is a single node based on the current default parent
     - \"\$\" resets the default parent to null (implied at the start);
           otherwise the default parent is always the last node created
     - \"<p\" sets the default parent to the backref p
     - \"\*p\" is a fork at parent p, which is a backref
     - \"\*p1/p2\" is a merge of parents p1 and p2, which are backrefs
     - \"/p2\" is a merge of the preceding node and p2
     - \":tag\" defines a local tag for the preceding node
     - \"@branch\" sets the named branch for subsequent nodes
     - \"#...\\\\n\" is a comment up to the end of the line

    Whitespace between the above elements is ignored.

    A backref is either

     - a number n, which references the node curr-n, where curr is the current
       node, or
     - the name of a local tag you placed earlier using \":tag\", or
     - empty to denote the default parent.

    All string valued-elements are either strictly alphanumeric, or must
    be enclosed in double quotes (\"...\"), with \"\\\\\" as escape character.
    \"\"\"

    if text is None:
        ui.status(_(\"reading DAG from stdin\\n\"))
        text = ui.fin.read()

    cl = repo.changelog
    if len(cl) > 0:
        raise util.Abort(_('repository is not empty'))

    # determine number of revs in DAG
    total = 0
    for type, data in dagparser.parsedag(text):
        if type == 'n':
            total += 1

    if mergeable_file:
        linesperrev = 2
        # make a file with k lines per rev
        initialmergedlines = [str(i) for i in xrange(0, total \* linesperrev)]
        initialmergedlines.append(\"\")

    tags = []

    tr = repo.transaction(\"builddag\")
    try:

        at = -1
        atbranch = 'default'
        nodeids = []
        ui.progress(_('building'), 0, unit=_('revisions'), total=total)
        for type, data in dagparser.parsedag(text):
            if type == 'n':
                ui.note('node %s\\n' % str(data))
                id, ps = data

                files = []
                fctxs = {}

                p2 = None
                if mergeable_file:
                    fn = \"mf\"
                    p1 = repo[ps[0]]
                    if len(ps) > 1:
                        p2 = repo[ps[1]]
                        pa = p1.ancestor(p2)
                        base, local, other = [x[fn].data() for x in pa, p1, p2]
                        m3 = simplemerge.Merge3Text(base, local, other)
                        ml = [l.strip() for l in m3.merge_lines()]
                        ml.append(\"\")
                    elif at > 0:
                        ml = p1[fn].data().split(\"\\n\")
                    else:
                        ml = initialmergedlines
                    ml[id \* linesperrev] += \" r%i\" % id
                    mergedtext = \"\\n\".join(ml)
                    files.append(fn)
                    fctxs[fn] = context.memfilectx(fn, mergedtext)

                if overwritten_file:
                    fn = \"of\"
                    files.append(fn)
                    fctxs[fn] = context.memfilectx(fn, \"r%i\\n\" % id)

                if new_file:
                    fn = \"nf%i\" % id
                    files.append(fn)
                    fctxs[fn] = context.memfilectx(fn, \"r%i\\n\" % id)
                    if len(ps) > 1:
                        if not p2:
                            p2 = repo[ps[1]]
                        for fn in p2:
                            if fn.startswith(\"nf\"):
                                files.append(fn)
                                fctxs[fn] = p2[fn]

                def fctxfn(repo, cx, path):
                    return fctxs.get(path)

                if len(ps) == 0 or ps[0] < 0:
                    pars = [None, None]
                elif len(ps) == 1:
                    pars = [nodeids[ps[0]], None]
                else:
                    pars = [nodeids[p] for p in ps]
                cx = context.memctx(repo, pars, \"r%i\" % id, files, fctxfn,
                                    date=(id, 0),
                                    user=\"debugbuilddag\",
                                    extra={'branch': atbranch})
                nodeid = repo.commitctx(cx)
                nodeids.append(nodeid)
                at = id
            elif type == 'l':
                id, name = data
                ui.note('tag %s\\n' % name)
                tags.append(\"%s %s\\n\" % (hex(repo.changelog.node(id)), name))
            elif type == 'a':
                ui.note('branch %s\\n' % data)
                atbranch = data
            ui.progress(_('building'), id, unit=_('revisions'), total=total)
        tr.close()
    finally:
        ui.progress(_('building'), None)
        tr.release()

    if tags:
        repo.opener.write(\"localtags\", \"\".join(tags))

@command('debugbundle', [('a', 'all', None, _('show all details'))], _('FILE'))
def debugbundle(ui, bundlepath, all=None, \*\*opts):
    \"\"\"lists the contents of a bundle\"\"\"
    f = url.open(ui, bundlepath)
    try:
        gen = changegroup.readbundle(f, bundlepath)
        if all:
            ui.write(\"format: id, p1, p2, cset, delta base, len(delta)\\n\")

            def showchunks(named):
                ui.write(\"\\n%s\\n\" % named)
                chain = None
                while True:
                    chunkdata = gen.deltachunk(chain)
                    if not chunkdata:
                        break
                    node = chunkdata['node']
                    p1 = chunkdata['p1']
                    p2 = chunkdata['p2']
                    cs = chunkdata['cs']
                    deltabase = chunkdata['deltabase']
                    delta = chunkdata['delta']
                    ui.write(\"%s %s %s %s %s %s\\n\" %
                             (hex(node), hex(p1), hex(p2),
                              hex(cs), hex(deltabase), len(delta)))
                    chain = node

            chunkdata = gen.changelogheader()
            showchunks(\"changelog\")
            chunkdata = gen.manifestheader()
            showchunks(\"manifest\")
            while True:
                chunkdata = gen.filelogheader()
                if not chunkdata:
                    break
                fname = chunkdata['filename']
                showchunks(fname)
        else:
            chunkdata = gen.changelogheader()
            chain = None
            while True:
                chunkdata = gen.deltachunk(chain)
                if not chunkdata:
                    break
                node = chunkdata['node']
                ui.write(\"%s\\n\" % hex(node))
                chain = node
    finally:
        f.close()

@command('debugcheckstate', [], '')
def debugcheckstate(ui, repo):
    \"\"\"validate the correctness of the current dirstate\"\"\"
    parent1, parent2 = repo.dirstate.parents()
    m1 = repo[parent1].manifest()
    m2 = repo[parent2].manifest()
    errors = 0
    for f in repo.dirstate:
        state = repo.dirstate[f]
        if state in \"nr\" and f not in m1:
            ui.warn(_(\"%s in state %s, but not in manifest1\\n\") % (f, state))
            errors += 1
        if state in \"a\" and f in m1:
            ui.warn(_(\"%s in state %s, but also in manifest1\\n\") % (f, state))
            errors += 1
        if state in \"m\" and f not in m1 and f not in m2:
            ui.warn(_(\"%s in state %s, but not in either manifest\\n\") %
                    (f, state))
            errors += 1
    for f in m1:
        state = repo.dirstate[f]
        if state not in \"nrm\":
            ui.warn(_(\"%s in manifest1, but listed as state %s\") % (f, state))
            errors += 1
    if errors:
        error = _(\".hg/dirstate inconsistent with current parent's manifest\")
        raise util.Abort(error)

@command('debugcommands', [], _('[COMMAND]'))
def debugcommands(ui, cmd='', \*args):
    \"\"\"list all available commands and options\"\"\"
    for cmd, vals in sorted(table.iteritems()):
        cmd = cmd.split('|')[0].strip('^')
        opts = ', '.join([i[1] for i in vals[1]])
        ui.write('%s: %s\\n' % (cmd, opts))

@command('debugcomplete',
    [('o', 'options', None, _('show the command options'))],
    _('[-o] CMD'))
def debugcomplete(ui, cmd='', \*\*opts):
    \"\"\"returns the completion list associated with the given command\"\"\"

    if opts.get('options'):
        options = []
        otables = [globalopts]
        if cmd:
            aliases, entry = cmdutil.findcmd(cmd, table, False)
            otables.append(entry[1])
        for t in otables:
            for o in t:
                if \"(DEPRECATED)\" in o[3]:
                    continue
                if o[0]:
                    options.append('-%s' % o[0])
                options.append('--%s' % o[1])
        ui.write(\"%s\\n\" % \"\\n\".join(options))
        return

    cmdlist = cmdutil.findpossible(cmd, table)
    if ui.verbose:
        cmdlist = [' '.join(c[0]) for c in cmdlist.values()]
    ui.write(\"%s\\n\" % \"\\n\".join(sorted(cmdlist)))

@command('debugdag',
    [('t', 'tags', None, _('use tags as labels')),
    ('b', 'branches', None, _('annotate with branch names')),
    ('', 'dots', None, _('use dots for runs')),
    ('s', 'spaces', None, _('separate elements by spaces'))],
    _('[OPTION]... [FILE [REV]...]'))
def debugdag(ui, repo, file_=None, \*revs, \*\*opts):
    \"\"\"format the changelog or an index DAG as a concise textual description

    If you pass a revlog index, the revlog's DAG is emitted. If you list
    revision numbers, they get labelled in the output as rN.

    Otherwise, the changelog DAG of the current repo is emitted.
    \"\"\"
    spaces = opts.get('spaces')
    dots = opts.get('dots')
    if file_:
        rlog = revlog.revlog(scmutil.opener(os.getcwd(), audit=False), file_)
        revs = set((int(r) for r in revs))
        def events():
            for r in rlog:
                yield 'n', (r, list(set(p for p in rlog.parentrevs(r) if p != -1)))
                if r in revs:
                    yield 'l', (r, \"r%i\" % r)
    elif repo:
        cl = repo.changelog
        tags = opts.get('tags')
        branches = opts.get('branches')
        if tags:
            labels = {}
            for l, n in repo.tags().items():
                labels.setdefault(cl.rev(n), []).append(l)
        def events():
            b = \"default\"
            for r in cl:
                if branches:
                    newb = cl.read(cl.node(r))[5]['branch']
                    if newb != b:
                        yield 'a', newb
                        b = newb
                yield 'n', (r, list(set(p for p in cl.parentrevs(r) if p != -1)))
                if tags:
                    ls = labels.get(r)
                    if ls:
                        for l in ls:
                            yield 'l', (r, l)
    else:
        raise util.Abort(_('need repo for changelog dag'))

    for line in dagparser.dagtextlines(events(),
                                       addspaces=spaces,
                                       wraplabels=True,
                                       wrapannotations=True,
                                       wrapnonlinear=dots,
                                       usedots=dots,
                                       maxlinewidth=70):
        ui.write(line)
        ui.write(\"\\n\")

@command('debugdata',
    [('c', 'changelog', False, _('open changelog')),
     ('m', 'manifest', False, _('open manifest'))],
    _('-c|-m|FILE REV'))
def debugdata(ui, repo, file_, rev = None, \*\*opts):
    \"\"\"dump the contents of a data file revision\"\"\"
    if opts.get('changelog') or opts.get('manifest'):
        file_, rev = None, file_
    elif rev is None:
        raise error.CommandError('debugdata', _('invalid arguments'))
    r = cmdutil.openrevlog(repo, 'debugdata', file_, opts)
    try:
        ui.write(r.revision(r.lookup(rev)))
    except KeyError:
        raise util.Abort(_('invalid revision identifier %s') % rev)

@command('debugdate',
    [('e', 'extended', None, _('try extended date formats'))],
    _('[-e] DATE [RANGE]'))
def debugdate(ui, date, range=None, \*\*opts):
    \"\"\"parse and display a date\"\"\"
    if opts[\"extended\"]:
        d = util.parsedate(date, util.extendeddateformats)
    else:
        d = util.parsedate(date)
    ui.write(\"internal: %s %s\\n\" % d)
    ui.write(\"standard: %s\\n\" % util.datestr(d))
    if range:
        m = util.matchdate(range)
        ui.write(\"match: %s\\n\" % m(d[0]))

@command('debugdiscovery',
    [('', 'old', None, _('use old-style discovery')),
    ('', 'nonheads', None,
     _('use old-style discovery with non-heads included')),
    ] + remoteopts,
    _('[-l REV] [-r REV] [-b BRANCH]... [OTHER]'))
def debugdiscovery(ui, repo, remoteurl=\"default\", \*\*opts):
    \"\"\"runs the changeset discovery protocol in isolation\"\"\"
    remoteurl, branches = hg.parseurl(ui.expandpath(remoteurl), opts.get('branch'))
    remote = hg.peer(repo, opts, remoteurl)
    ui.status(_('comparing with %s\\n') % util.hidepassword(remoteurl))

    # make sure tests are repeatable
    random.seed(12323)

    def doit(localheads, remoteheads):
        if opts.get('old'):
            if localheads:
                raise util.Abort('cannot use localheads with old style discovery')
            common, _in, hds = treediscovery.findcommonincoming(repo, remote,
                                                                force=True)
            common = set(common)
            if not opts.get('nonheads'):
                ui.write(\"unpruned common: %s\\n\" % \" \".join([short(n)
                                                            for n in common]))
                dag = dagutil.revlogdag(repo.changelog)
                all = dag.ancestorset(dag.internalizeall(common))
                common = dag.externalizeall(dag.headsetofconnecteds(all))
        else:
            common, any, hds = setdiscovery.findcommonheads(ui, repo, remote)
        common = set(common)
        rheads = set(hds)
        lheads = set(repo.heads())
        ui.write(\"common heads: %s\\n\" % \" \".join([short(n) for n in common]))
        if lheads <= common:
            ui.write(\"local is subset\\n\")
        elif rheads <= common:
            ui.write(\"remote is subset\\n\")

    serverlogs = opts.get('serverlog')
    if serverlogs:
        for filename in serverlogs:
            logfile = open(filename, 'r')
            try:
                line = logfile.readline()
                while line:
                    parts = line.strip().split(';')
                    op = parts[1]
                    if op == 'cg':
                        pass
                    elif op == 'cgss':
                        doit(parts[2].split(' '), parts[3].split(' '))
                    elif op == 'unb':
                        doit(parts[3].split(' '), parts[2].split(' '))
                    line = logfile.readline()
            finally:
                logfile.close()

    else:
        remoterevs, _checkout = hg.addbranchrevs(repo, remote, branches,
                                                 opts.get('remote_head'))
        localrevs = opts.get('local_head')
        doit(localrevs, remoterevs)

@command('debugfileset', [], ('REVSPEC'))
def debugfileset(ui, repo, expr):
    '''parse and apply a fileset specification'''
    if ui.verbose:
        tree = fileset.parse(expr)[0]
        ui.note(tree, \"\\n\")

    for f in fileset.getfileset(repo[None], expr):
        ui.write(\"%s\\n\" % f)

@command('debugfsinfo', [], _('[PATH]'))
def debugfsinfo(ui, path = \".\"):
    \"\"\"show information detected about current filesystem\"\"\"
    util.writefile('.debugfsinfo', '')
    ui.write('exec: %s\\n' % (util.checkexec(path) and 'yes' or 'no'))
    ui.write('symlink: %s\\n' % (util.checklink(path) and 'yes' or 'no'))
    ui.write('case-sensitive: %s\\n' % (util.checkcase('.debugfsinfo')
                                and 'yes' or 'no'))
    os.unlink('.debugfsinfo')

@command('debuggetbundle',
    [('H', 'head', [], _('id of head node'), _('ID')),
    ('C', 'common', [], _('id of common node'), _('ID')),
    ('t', 'type', 'bzip2', _('bundle compression type to use'), _('TYPE'))],
    _('REPO FILE [-H|-C ID]...'))
def debuggetbundle(ui, repopath, bundlepath, head=None, common=None, \*\*opts):
    \"\"\"retrieves a bundle from a repo

    Every ID must be a full-length hex node id string. Saves the bundle to the
    given file.
    \"\"\"
    repo = hg.peer(ui, opts, repopath)
    if not repo.capable('getbundle'):
        raise util.Abort(\"getbundle() not supported by target repository\")
    args = {}
    if common:
        args['common'] = [bin(s) for s in common]
    if head:
        args['heads'] = [bin(s) for s in head]
    bundle = repo.getbundle('debug', \*\*args)

    bundletype = opts.get('type', 'bzip2').lower()
    btypes = {'none': 'HG10UN', 'bzip2': 'HG10BZ', 'gzip': 'HG10GZ'}
    bundletype = btypes.get(bundletype)
    if bundletype not in changegroup.bundletypes:
        raise util.Abort(_('unknown bundle type specified with --type'))
    changegroup.writebundle(bundle, bundlepath, bundletype)

@command('debugignore', [], '')
def debugignore(ui, repo, \*values, \*\*opts):
    \"\"\"display the combined ignore pattern\"\"\"
    ignore = repo.dirstate._ignore
    if hasattr(ignore, 'includepat'):
        ui.write(\"%s\\n\" % ignore.includepat)
    else:
        raise util.Abort(_(\"no ignore patterns found\"))

@command('debugindex',
    [('c', 'changelog', False, _('open changelog')),
     ('m', 'manifest', False, _('open manifest')),
     ('f', 'format', 0, _('revlog format'), _('FORMAT'))],
    _('[-f FORMAT] -c|-m|FILE'))
def debugindex(ui, repo, file_ = None, \*\*opts):
    \"\"\"dump the contents of an index file\"\"\"
    r = cmdutil.openrevlog(repo, 'debugindex', file_, opts)
    format = opts.get('format', 0)
    if format not in (0, 1):
        raise util.Abort(_(\"unknown format %d\") % format)

    generaldelta = r.version & revlog.REVLOGGENERALDELTA
    if generaldelta:
        basehdr = ' delta'
    else:
        basehdr = '  base'

    if format == 0:
        ui.write(\"   rev offset length \" + basehdr + \" linkrev\"
                 \" nodeid p1 p2\\n\")
    elif format == 1:
        ui.write(\"   rev flag offset length\"
                 \"     size \" + basehdr + \"   link p1 p2 nodeid\\n\")

    for i in r:
        node = r.node(i)
        if generaldelta:
            base = r.deltaparent(i)
        else:
            base = r.chainbase(i)
        if format == 0:
            try:
                pp = r.parents(node)
            except:
                pp = [nullid, nullid]
            ui.write(\"% 6d % 9d % 7d % 6d % 7d %s %s %s\\n\" % (
                    i, r.start(i), r.length(i), base, r.linkrev(i),
                    short(node), short(pp[0]), short(pp[1])))
        elif format == 1:
            pr = r.parentrevs(i)
            ui.write(\"% 6d %04x % 8d % 8d % 8d % 6d % 6d % 6d % 6d %s\\n\" % (
                    i, r.flags(i), r.start(i), r.length(i), r.rawsize(i),
                    base, r.linkrev(i), pr[0], pr[1], short(node)))

@command('debugindexdot', [], _('FILE'))
def debugindexdot(ui, repo, file_):
    \"\"\"dump an index DAG as a graphviz dot file\"\"\"
    r = None
    if repo:
        filelog = repo.file(file_)
        if len(filelog):
            r = filelog
    if not r:
        r = revlog.revlog(scmutil.opener(os.getcwd(), audit=False), file_)
    ui.write(\"digraph G {\\n\")
    for i in r:
        node = r.node(i)
        pp = r.parents(node)
        ui.write(\"\\t%d -> %d\\n\" % (r.rev(pp[0]), i))
        if pp[1] != nullid:
            ui.write(\"\\t%d -> %d\\n\" % (r.rev(pp[1]), i))
    ui.write(\"}\\n\")

@command('debuginstall', [], '')
def debuginstall(ui):
    '''test Mercurial installation

    Returns 0 on success.
    '''

    def writetemp(contents):
        (fd, name) = tempfile.mkstemp(prefix=\"hg-debuginstall-\")
        f = os.fdopen(fd, \"wb\")
        f.write(contents)
        f.close()
        return name

    problems = 0

    # encoding
    ui.status(_(\"Checking encoding (%s)...\\n\") % encoding.encoding)
    try:
        encoding.fromlocal(\"test\")
    except util.Abort, inst:
        ui.write(\" %s\\n\" % inst)
        ui.write(_(\" (check that your locale is properly set)\\n\"))
        problems += 1

    # compiled modules
    ui.status(_(\"Checking installed modules (%s)...\\n\")
              % os.path.dirname(__file__))
    try:
        import bdiff, mpatch, base85, osutil
    except Exception, inst:
        ui.write(\" %s\\n\" % inst)
        ui.write(_(\" One or more extensions could not be found\"))
        ui.write(_(\" (check that you compiled the extensions)\\n\"))
        problems += 1

    # templates
    ui.status(_(\"Checking templates...\\n\"))
    try:
        import templater
        templater.templater(templater.templatepath(\"map-cmdline.default\"))
    except Exception, inst:
        ui.write(\" %s\\n\" % inst)
        ui.write(_(\" (templates seem to have been installed incorrectly)\\n\"))
        problems += 1

    # editor
    ui.status(_(\"Checking commit editor...\\n\"))
    editor = ui.geteditor()
    cmdpath = util.findexe(editor) or util.findexe(editor.split()[0])
    if not cmdpath:
        if editor == 'vi':
            ui.write(_(\" No commit editor set and can't find vi in PATH\\n\"))
            ui.write(_(\" (specify a commit editor in your configuration\"
                       \" file)\\n\"))
        else:
            ui.write(_(\" Can't find editor '%s' in PATH\\n\") % editor)
            ui.write(_(\" (specify a commit editor in your configuration\"
                       \" file)\\n\"))
            problems += 1

    # check username
    ui.status(_(\"Checking username...\\n\"))
    try:
        ui.username()
    except util.Abort, e:
        ui.write(\" %s\\n\" % e)
        ui.write(_(\" (specify a username in your configuration file)\\n\"))
        problems += 1

    if not problems:
        ui.status(_(\"No problems detected\\n\"))
    else:
        ui.write(_(\"%s problems detected,\"
                   \" please check your install!\\n\") % problems)

    return problems

@command('debugknown', [], _('REPO ID...'))
def debugknown(ui, repopath, \*ids, \*\*opts):
    \"\"\"test whether node ids are known to a repo

    Every ID must be a full-length hex node id string. Returns a list of 0s and 1s
    indicating unknown/known.
    \"\"\"
    repo = hg.peer(ui, opts, repopath)
    if not repo.capable('known'):
        raise util.Abort(\"known() not supported by target repository\")
    flags = repo.known([bin(s) for s in ids])
    ui.write(\"%s\\n\" % (\"\".join([f and \"1\" or \"0\" for f in flags])))

@command('debugpushkey', [], _('REPO NAMESPACE [KEY OLD NEW]'))
def debugpushkey(ui, repopath, namespace, \*keyinfo, \*\*opts):
    '''access the pushkey key/value protocol

    With two args, list the keys in the given namespace.

    With five args, set a key to new if it currently is set to old.
    Reports success or failure.
    '''

    target = hg.peer(ui, {}, repopath)
    if keyinfo:
        key, old, new = keyinfo
        r = target.pushkey(namespace, key, old, new)
        ui.status(str(r) + '\\n')
        return not r
    else:
        for k, v in target.listkeys(namespace).iteritems():
            ui.write(\"%s\\t%s\\n\" % (k.encode('string-escape'),
                                   v.encode('string-escape')))

@command('debugrebuildstate',
    [('r', 'rev', '', _('revision to rebuild to'), _('REV'))],
    _('[-r REV] [REV]'))
def debugrebuildstate(ui, repo, rev=\"tip\"):
    \"\"\"rebuild the dirstate as it would look like for the given revision\"\"\"
    ctx = scmutil.revsingle(repo, rev)
    wlock = repo.wlock()
    try:
        repo.dirstate.rebuild(ctx.node(), ctx.manifest())
    finally:
        wlock.release()

@command('debugrename',
    [('r', 'rev', '', _('revision to debug'), _('REV'))],
    _('[-r REV] FILE'))
def debugrename(ui, repo, file1, \*pats, \*\*opts):
    \"\"\"dump rename information\"\"\"

    ctx = scmutil.revsingle(repo, opts.get('rev'))
    m = scmutil.match(ctx, (file1,) + pats, opts)
    for abs in ctx.walk(m):
        fctx = ctx[abs]
        o = fctx.filelog().renamed(fctx.filenode())
        rel = m.rel(abs)
        if o:
            ui.write(_(\"%s renamed from %s:%s\\n\") % (rel, o[0], hex(o[1])))
        else:
            ui.write(_(\"%s not renamed\\n\") % rel)

@command('debugrevlog',
    [('c', 'changelog', False, _('open changelog')),
     ('m', 'manifest', False, _('open manifest')),
     ('d', 'dump', False, _('dump index data'))],
     _('-c|-m|FILE'))
def debugrevlog(ui, repo, file_ = None, \*\*opts):
    \"\"\"show data and statistics about a revlog\"\"\"
    r = cmdutil.openrevlog(repo, 'debugrevlog', file_, opts)

    if opts.get(\"dump\"):
        numrevs = len(r)
        ui.write(\"# rev p1rev p2rev start end deltastart base p1 p2\"
                 \" rawsize totalsize compression heads\\n\")
        ts = 0
        heads = set()
        for rev in xrange(numrevs):
            dbase = r.deltaparent(rev)
            if dbase == -1:
                dbase = rev
            cbase = r.chainbase(rev)
            p1, p2 = r.parentrevs(rev)
            rs = r.rawsize(rev)
            ts = ts + rs
            heads -= set(r.parentrevs(rev))
            heads.add(rev)
            ui.write(\"%d %d %d %d %d %d %d %d %d %d %d %d %d\\n\" %
                     (rev, p1, p2, r.start(rev), r.end(rev),
                      r.start(dbase), r.start(cbase),
                      r.start(p1), r.start(p2),
                      rs, ts, ts / r.end(rev), len(heads)))
        return 0

    v = r.version
    format = v & 0xFFFF
    flags = []
    gdelta = False
    if v & revlog.REVLOGNGINLINEDATA:
        flags.append('inline')
    if v & revlog.REVLOGGENERALDELTA:
        gdelta = True
        flags.append('generaldelta')
    if not flags:
        flags = ['(none)']

    nummerges = 0
    numfull = 0
    numprev = 0
    nump1 = 0
    nump2 = 0
    numother = 0
    nump1prev = 0
    nump2prev = 0
    chainlengths = []

    datasize = [None, 0, 0L]
    fullsize = [None, 0, 0L]
    deltasize = [None, 0, 0L]

    def addsize(size, l):
        if l[0] is None or size < l[0]:
            l[0] = size
        if size > l[1]:
            l[1] = size
        l[2] += size

    numrevs = len(r)
    for rev in xrange(numrevs):
        p1, p2 = r.parentrevs(rev)
        delta = r.deltaparent(rev)
        if format > 0:
            addsize(r.rawsize(rev), datasize)
        if p2 != nullrev:
            nummerges += 1
        size = r.length(rev)
        if delta == nullrev:
            chainlengths.append(0)
            numfull += 1
            addsize(size, fullsize)
        else:
            chainlengths.append(chainlengths[delta] + 1)
            addsize(size, deltasize)
            if delta == rev - 1:
                numprev += 1
                if delta == p1:
                    nump1prev += 1
                elif delta == p2:
                    nump2prev += 1
            elif delta == p1:
                nump1 += 1
            elif delta == p2:
                nump2 += 1
            elif delta != nullrev:
                numother += 1

    numdeltas = numrevs - numfull
    numoprev = numprev - nump1prev - nump2prev
    totalrawsize = datasize[2]
    datasize[2] /= numrevs
    fulltotal = fullsize[2]
    fullsize[2] /= numfull
    deltatotal = deltasize[2]
    deltasize[2] /= numrevs - numfull
    totalsize = fulltotal + deltatotal
    avgchainlen = sum(chainlengths) / numrevs
    compratio = totalrawsize / totalsize

    basedfmtstr = '%%%dd\\n'
    basepcfmtstr = '%%%dd %s(%%5.2f%%%%)\\n'

    def dfmtstr(max):
        return basedfmtstr % len(str(max))
    def pcfmtstr(max, padding=0):
        return basepcfmtstr % (len(str(max)), ' ' \* padding)

    def pcfmt(value, total):
        return (value, 100 \* float(value) / total)

    ui.write('format : %d\\n' % format)
    ui.write('flags : %s\\n' % ', '.join(flags))

    ui.write('\\n')
    fmt = pcfmtstr(totalsize)
    fmt2 = dfmtstr(totalsize)
    ui.write('revisions : ' + fmt2 % numrevs)
    ui.write('    merges : ' + fmt % pcfmt(nummerges, numrevs))
    ui.write('    normal : ' + fmt % pcfmt(numrevs - nummerges, numrevs))
    ui.write('revisions : ' + fmt2 % numrevs)
    ui.write('    full : ' + fmt % pcfmt(numfull, numrevs))
    ui.write('    deltas : ' + fmt % pcfmt(numdeltas, numrevs))
    ui.write('revision size : ' + fmt2 % totalsize)
    ui.write('    full : ' + fmt % pcfmt(fulltotal, totalsize))
    ui.write('    deltas : ' + fmt % pcfmt(deltatotal, totalsize))

    ui.write('\\n')
    fmt = dfmtstr(max(avgchainlen, compratio))
    ui.write('avg chain length : ' + fmt % avgchainlen)
    ui.write('compression ratio : ' + fmt % compratio)

    if format > 0:
        ui.write('\\n')
        ui.write('uncompressed data size (min/max/avg) : %d / %d / %d\\n'
                 % tuple(datasize))
    ui.write('full revision size (min/max/avg) : %d / %d / %d\\n'
             % tuple(fullsize))
    ui.write('delta size (min/max/avg) : %d / %d / %d\\n'
             % tuple(deltasize))

    if numdeltas > 0:
        ui.write('\\n')
        fmt = pcfmtstr(numdeltas)
        fmt2 = pcfmtstr(numdeltas, 4)
        ui.write('deltas against prev : ' + fmt % pcfmt(numprev, numdeltas))
        if numprev > 0:
            ui.write('    where prev = p1 : ' + fmt2 % pcfmt(nump1prev, numprev))
            ui.write('    where prev = p2 : ' + fmt2 % pcfmt(nump2prev, numprev))
            ui.write('    other : ' + fmt2 % pcfmt(numoprev, numprev))
        if gdelta:
            ui.write('deltas against p1 : ' + fmt % pcfmt(nump1, numdeltas))
            ui.write('deltas against p2 : ' + fmt % pcfmt(nump2, numdeltas))
            ui.write('deltas against other : ' + fmt % pcfmt(numother, numdeltas))

@command('debugrevspec', [], ('REVSPEC'))
def debugrevspec(ui, repo, expr):
    '''parse and apply a revision specification'''
    if ui.verbose:
        tree = revset.parse(expr)[0]
        ui.note(tree, \"\\n\")
        newtree = revset.findaliases(ui, tree)
        if newtree != tree:
            ui.note(newtree, \"\\n\")
    func = revset.match(ui, expr)
    for c in func(repo, range(len(repo))):
        ui.write(\"%s\\n\" % c)

@command('debugsetparents', [], _('REV1 [REV2]'))
def debugsetparents(ui, repo, rev1, rev2=None):
    \"\"\"manually set the parents of the current working directory

    This is useful for writing repository conversion tools, but should
    be used with care.

    Returns 0 on success.
    \"\"\"

    r1 = scmutil.revsingle(repo, rev1).node()
    r2 = scmutil.revsingle(repo, rev2, 'null').node()

    wlock = repo.wlock()
    try:
        repo.dirstate.setparents(r1, r2)
    finally:
        wlock.release()

@command('debugstate',
    [('', 'nodates', None, _('do not display the saved mtime')),
    ('', 'datesort', None, _('sort by saved mtime'))],
    _('[OPTION]...'))
def debugstate(ui, repo, nodates=None, datesort=None):
    \"\"\"show the contents of the current dirstate\"\"\"
    timestr = \"\"
    showdate = not nodates
    if datesort:
        keyfunc = lambda x: (x[1][3], x[0]) # sort by mtime, then by filename
    else:
        keyfunc = None # sort by filename
    for file_, ent in sorted(repo.dirstate._map.iteritems(), key=keyfunc):
        if showdate:
            if ent[3] == -1:
                # Pad or slice to locale representation
                locale_len = len(time.strftime(\"%Y-%m-%d %H:%M:%S \",
                                               time.localtime(0)))
                timestr = 'unset'
                timestr = (timestr[:locale_len] +
                           ' ' \* (locale_len - len(timestr)))
            else:
                timestr = time.strftime(\"%Y-%m-%d %H:%M:%S \",
                                        time.localtime(ent[3]))
        if ent[1] & 020000:
            mode = 'lnk'
        else:
            mode = '%3o' % (ent[1] & 0777)
        ui.write(\"%c %s %10d %s%s\\n\" % (ent[0], mode, ent[2], timestr, file_))
    for f in repo.dirstate.copies():
        ui.write(_(\"copy: %s -> %s\\n\") % (repo.dirstate.copied(f), f))

@command('debugsub',
    [('r', 'rev', '',
     _('revision to check'), _('REV'))],
    _('[-r REV] [REV]'))
def debugsub(ui, repo, rev=None):
    ctx = scmutil.revsingle(repo, rev, None)
    for k, v in sorted(ctx.substate.items()):
        ui.write('path %s\\n' % k)
        ui.write(' source %s\\n' % v[0])
        ui.write(' revision %s\\n' % v[1])

@command('debugwalk', walkopts, _('[OPTION]... [FILE]...'))
def debugwalk(ui, repo, \*pats, \*\*opts):
    \"\"\"show how files match on given patterns\"\"\"
    m = scmutil.match(repo[None], pats, opts)
    items = list(repo.walk(m))
    if not items:
        return
    fmt = 'f %%-%ds %%-%ds %%s' % (
        max([len(abs) for abs in items]),
        max([len(m.rel(abs)) for abs in items]))
    for abs in items:
        line = fmt % (abs, m.rel(abs), m.exact(abs) and 'exact' or '')
        ui.write(\"%s\\n\" % line.rstrip())

@command('debugwireargs',
    [('', 'three', '', 'three'),
    ('', 'four', '', 'four'),
    ('', 'five', '', 'five'),
    ] + remoteopts,
    _('REPO [OPTIONS]... [ONE [TWO]]'))
def debugwireargs(ui, repopath, \*vals, \*\*opts):
    repo = hg.peer(ui, opts, repopath)
    for opt in remoteopts:
        del opts[opt[1]]
    args = {}
    for k, v in opts.iteritems():
        if v:
            args[k] = v
    # run twice to check that we don't mess up the stream for the next command
    res1 = repo.debugwireargs(\*vals, \*\*args)
    res2 = repo.debugwireargs(\*vals, \*\*args)
    ui.write(\"%s\\n\" % res1)
    if res1 != res2:
        ui.warn(\"%s\\n\" % res2)

@command('^diff',
    [('r', 'rev', [], _('revision'), _('REV')),
    ('c', 'change', '', _('change made by revision'), _('REV'))
    ] + diffopts + diffopts2 + walkopts + subrepoopts,
    _('[OPTION]... ([-c REV] | [-r REV1 [-r REV2]]) [FILE]...'))
def diff(ui, repo, \*pats, \*\*opts):
    \"\"\"diff repository (or selected files)

    Show differences between revisions for the specified files.

    Differences between files are shown using the unified diff format.

    .. note::
       diff may generate unexpected results for merges, as it will
       default to comparing against the working directory's first
       parent changeset if no revisions are specified.

    When two revision arguments are given, then changes are shown
    between those revisions. If only one revision is specified then
    that revision is compared to the working directory, and, when no
    revisions are specified, the working directory files are compared
    to its parent.

    Alternatively you can specify -c/--change with a revision to see
    the changes in that changeset relative to its first parent.

    Without the -a/--text option, diff will avoid generating diffs of
    files it detects as binary. With -a, diff will generate a diff
    anyway, probably with undesirable results.

    Use the -g/--git option to generate diffs in the git extended diff
    format. For more information, read :hg:`help diffs`.

    Returns 0 on success.
    \"\"\"

    revs = opts.get('rev')
    change = opts.get('change')
    stat = opts.get('stat')
    reverse = opts.get('reverse')

    if revs and change:
        msg = _('cannot specify --rev and --change at the same time')
        raise util.Abort(msg)
    elif change:
        node2 = scmutil.revsingle(repo, change, None).node()
        node1 = repo[node2].p1().node()
    else:
        node1, node2 = scmutil.revpair(repo, revs)

    if reverse:
        node1, node2 = node2, node1

    diffopts = patch.diffopts(ui, opts)
    m = scmutil.match(repo[node2], pats, opts)
    cmdutil.diffordiffstat(ui, repo, diffopts, node1, node2, m, stat=stat,
                           listsubrepos=opts.get('subrepos'))

@command('^export',
    [('o', 'output', '',
     _('print output to file with formatted name'), _('FORMAT')),
    ('', 'switch-parent', None, _('diff against the second parent')),
    ('r', 'rev', [], _('revisions to export'), _('REV')),
    ] + diffopts,
    _('[OPTION]... [-o OUTFILESPEC] REV...'))
def export(ui, repo, \*changesets, \*\*opts):
    \"\"\"dump the header and diffs for one or more changesets

    Print the changeset header and diffs for one or more revisions.

    The information shown in the changeset header is: author, date,
    branch name (if non-default), changeset hash, parent(s) and commit
    comment.

    .. note::
       export may generate unexpected diff output for merge
       changesets, as it will compare the merge changeset against its
       first parent only.

    Output may be to a file, in which case the name of the file is
    given using a format string. The formatting rules are as follows:

    :``%%``: literal \"%\" character
    :``%H``: changeset hash (40 hexadecimal digits)
    :``%N``: number of patches being generated
    :``%R``: changeset revision number
    :``%b``: basename of the exporting repository
    :``%h``: short-form changeset hash (12 hexadecimal digits)
    :``%n``: zero-padded sequence number, starting at 1
    :``%r``: zero-padded changeset revision number

    Without the -a/--text option, export will avoid generating diffs
    of files it detects as binary. With -a, export will generate a
    diff anyway, probably with undesirable results.

    Use the -g/--git option to generate diffs in the git extended diff
    format. See :hg:`help diffs` for more information.

    With the --switch-parent option, the diff will be against the
    second parent. It can be useful to review a merge.

    Returns 0 on success.
    \"\"\"
    changesets += tuple(opts.get('rev', []))
    if not changesets:
        raise util.Abort(_(\"export requires at least one changeset\"))
    revs = scmutil.revrange(repo, changesets)
    if len(revs) > 1:
        ui.note(_('exporting patches:\\n'))
    else:
        ui.note(_('exporting patch:\\n'))
    cmdutil.export(repo, revs, template=opts.get('output'),
                 switch_parent=opts.get('switch_parent'),
                 opts=patch.diffopts(ui, opts))

@command('^forget', walkopts, _('[OPTION]... FILE...'))
def forget(ui, repo, \*pats, \*\*opts):
    \"\"\"forget the specified files on the next commit

    Mark the specified files so they will no longer be tracked
    after the next commit.

    This only removes files from the current branch, not from the
    entire project history, and it does not delete them from the
    working directory.

    To undo a forget before the next commit, see :hg:`add`.

    Returns 0 on success.
    \"\"\"

    if not pats:
        raise util.Abort(_('no files specified'))

    m = scmutil.match(repo[None], pats, opts)
    s = repo.status(match=m, clean=True)
    forget = sorted(s[0] + s[1] + s[3] + s[6])
    errs = 0

    for f in m.files():
        if f not in repo.dirstate and not os.path.isdir(m.rel(f)):
            if os.path.exists(m.rel(f)):
                ui.warn(_('not removing %s: file is already untracked\\n')
                        % m.rel(f))
            errs = 1

    for f in forget:
        if ui.verbose or not m.exact(f):
            ui.status(_('removing %s\\n') % m.rel(f))

    repo[None].forget(forget)
    return errs

@command('grep',
    [('0', 'print0', None, _('end fields with NUL')),
    ('', 'all', None, _('print all revisions that match')),
    ('a', 'text', None, _('treat all files as text')),
    ('f', 'follow', None,
     _('follow changeset history,'
       ' or file history across copies and renames')),
    ('i', 'ignore-case', None, _('ignore case when matching')),
    ('l', 'files-with-matches', None,
     _('print only filenames and revisions that match')),
    ('n', 'line-number', None, _('print matching line numbers')),
    ('r', 'rev', [],
     _('only search files changed within revision range'), _('REV')),
    ('u', 'user', None, _('list the author (long with -v)')),
    ('d', 'date', None, _('list the date (short with -q)')),
    ] + walkopts,
    _('[OPTION]... PATTERN [FILE]...'))
def grep(ui, repo, pattern, \*pats, \*\*opts):
    \"\"\"search for a pattern in specified files and revisions

    Search revisions of files for a regular expression.

    This command behaves differently than Unix grep. It only accepts
    Python/Perl regexps. It searches repository history, not the
    working directory. It always prints the revision number in which a
    match appears.

    By default, grep only prints output for the first revision of a
    file in which it finds a match. To get it to print every revision
    that contains a change in match status (\"-\" for a match that
    becomes a non-match, or \"+\" for a non-match that becomes a match),
    use the --all flag.

    Returns 0 if a match is found, 1 otherwise.
    \"\"\"
    reflags = 0
    if opts.get('ignore_case'):
        reflags |= re.I
    try:
        regexp = re.compile(pattern, reflags)
    except re.error, inst:
        ui.warn(_(\"grep: invalid match pattern: %s\\n\") % inst)
        return 1
    sep, eol = ':', '\\n'
    if opts.get('print0'):
        sep = eol = '\\0'

    getfile = util.lrucachefunc(repo.file)

    def matchlines(body):
        begin = 0
        linenum = 0
        while True:
            match = regexp.search(body, begin)
            if not match:
                break
            mstart, mend = match.span()
            linenum += body.count('\\n', begin, mstart) + 1
            lstart = body.rfind('\\n', begin, mstart) + 1 or begin
            begin = body.find('\\n', mend) + 1 or len(body)
            lend = begin - 1
            yield linenum, mstart - lstart, mend - lstart, body[lstart:lend]

    class linestate(object):
        def __init__(self, line, linenum, colstart, colend):
            self.line = line
            self.linenum = linenum
            self.colstart = colstart
            self.colend = colend

        def __hash__(self):
            return hash((self.linenum, self.line))

        def __eq__(self, other):
            return self.line == other.line

    matches = {}
    copies = {}
    def grepbody(fn, rev, body):
        matches[rev].setdefault(fn, [])
        m = matches[rev][fn]
        for lnum, cstart, cend, line in matchlines(body):
            s = linestate(line, lnum, cstart, cend)
            m.append(s)

    def difflinestates(a, b):
        sm = difflib.SequenceMatcher(None, a, b)
        for tag, alo, ahi, blo, bhi in sm.get_opcodes():
            if tag == 'insert':
                for i in xrange(blo, bhi):
                    yield ('+', b[i])
            elif tag == 'delete':
                for i in xrange(alo, ahi):
                    yield ('-', a[i])
            elif tag == 'replace':
                for i in xrange(alo, ahi):
                    yield ('-', a[i])
                for i in xrange(blo, bhi):
                    yield ('+', b[i])

    def display(fn, ctx, pstates, states):
        rev = ctx.rev()
        datefunc = ui.quiet and util.shortdate or util.datestr
        found = False
        filerevmatches = {}
        def binary():
            flog = getfile(fn)
            return util.binary(flog.read(ctx.filenode(fn)))

        if opts.get('all'):
            iter = difflinestates(pstates, states)
        else:
            iter = [('', l) for l in states]
        for change, l in iter:
            cols = [fn, str(rev)]
            before, match, after = None, None, None
            if opts.get('line_number'):
                cols.append(str(l.linenum))
            if opts.get('all'):
                cols.append(change)
            if opts.get('user'):
                cols.append(ui.shortuser(ctx.user()))
            if opts.get('date'):
                cols.append(datefunc(ctx.date()))
            if opts.get('files_with_matches'):
                c = (fn, rev)
                if c in filerevmatches:
                    continue
                filerevmatches[c] = 1
            else:
                before = l.line[:l.colstart]
                match = l.line[l.colstart:l.colend]
                after = l.line[l.colend:]
            ui.write(sep.join(cols))
            if before is not None:
                if not opts.get('text') and binary():
                    ui.write(sep + \" Binary file matches\")
                else:
                    ui.write(sep + before)
                    ui.write(match, label='grep.match')
                    ui.write(after)
            ui.write(eol)
            found = True
        return found

    skip = {}
    revfiles = {}
    matchfn = scmutil.match(repo[None], pats, opts)
    found = False
    follow = opts.get('follow')

    def prep(ctx, fns):
        rev = ctx.rev()
        pctx = ctx.p1()
        parent = pctx.rev()
        matches.setdefault(rev, {})
        matches.setdefault(parent, {})
        files = revfiles.setdefault(rev, [])
        for fn in fns:
            flog = getfile(fn)
            try:
                fnode = ctx.filenode(fn)
            except error.LookupError:
                continue

            copied = flog.renamed(fnode)
            copy = follow and copied and copied[0]
            if copy:
                copies.setdefault(rev, {})[fn] = copy
            if fn in skip:
                if copy:
                    skip[copy] = True
                continue
            files.append(fn)

            if fn not in matches[rev]:
                grepbody(fn, rev, flog.read(fnode))

            pfn = copy or fn
            if pfn not in matches[parent]:
                try:
                    fnode = pctx.filenode(pfn)
                    grepbody(pfn, parent, flog.read(fnode))
                except error.LookupError:
                    pass

    for ctx in cmdutil.walkchangerevs(repo, matchfn, opts, prep):
        rev = ctx.rev()
        parent = ctx.p1().rev()
        for fn in sorted(revfiles.get(rev, [])):
            states = matches[rev][fn]
            copy = copies.get(rev, {}).get(fn)
            if fn in skip:
                if copy:
                    skip[copy] = True
                continue
            pstates = matches.get(parent, {}).get(copy or fn, [])
            if pstates or states:
                r = display(fn, ctx, pstates, states)
                found = found or r
                if r and not opts.get('all'):
                    skip[fn] = True
                    if copy:
                        skip[copy] = True
        del matches[rev]
        del revfiles[rev]

    return not found
"))
  (when load-branch-function (funcall load-branch-function))
  (py-bug-tests-intern 'erste-tqs-syntax-base arg teststring)))

(defun erste-tqs-syntax-base ()
  (goto-char (point-min))
  (forward-line 664)
  (sit-for 0.1) 
  (let ((pps (syntax-ppss)))
    (message "#1 nth 3: %s" (nth 3 pps))
    (assert (eq t (nth 3 pps)) nil "erste-tqs-syntax-test #1 failed")
    (goto-char 25173)
     (sit-for 0.1) 
    (setq pps (syntax-ppss))
    (message "#2 nth 3: %s" (nth 3 pps))
    (assert (not (nth 3 pps)) nil "erste-tqs-syntax-test #2 failed")))

(provide 'python-mode-syntax-test)
;;; python-mode-test.el ends here
