How many times have you wanted to fire off a quick command, such as M-!, but
the directory you want to run the command in isn't the same as the directory
of the current buffer?  In those situations, you want a quick way to change
the default-directory *for only the next command*.  That is what Springboard
aims to solve.

Bind it to a convenient key, like `Control-.`, and after you press it you'll
see a handy Helm buffer showing the directories of all the files you've
recently visited, plus the permanent directory list from
`springboard-directories` -- a good place to list your active project
directories.

Type a few chars to narrow down to the directory of interest, then just type
your command, like `M-!`, `C-x C-f`, or whatever custom bindings you may have
to run PCVS, Magit, etc.  The moment you type your command, Springboard
disappears, and if your command needs minibuffer input, you'll now be in the
minibuffer for that new command.
