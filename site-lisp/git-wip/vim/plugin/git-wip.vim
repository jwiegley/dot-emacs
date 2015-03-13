" ---------------------------------------------------------------------------
" git wip stuff

if !exists('g:git_wip_verbose')
        let g:git_wip_verbose = 0
endif

function! GitWipSave()
        if expand("%") == ".git/COMMIT_EDITMSG"
            return
        endif
        let out = system('git rev-parse 2>&1')
        if v:shell_error
            return
        endif
        let dir = expand("%:p:h")
        let show_cdup = system('cd ' . dir . ' && git rev-parse --show-cdup 2>/dev/null')
        if v:shell_error
            " We're not editing a file anywhere near a .git repository, so abort
            return
        endif
        let show_cdup_len = len( show_cdup )
        if show_cdup_len == 0
            " We're editing a file in the .git directory
            " (.git/EDIT_COMMITMSG, .git/config, etc.), so abort
            return
        endif
        let file = expand("%:t")
        let out = system('cd ' . dir . ' && git wip save "WIP from vim (' . file . ')" --editor -- "' . file . '" 2>&1')
        let err = v:shell_error
        if err
                redraw
                echohl Error
                echo "git-wip: " . out
                echohl None
        elseif g:git_wip_verbose
                redraw
                echo "git-wip: " . out
        endif
endf

silent! !git wip -h >/dev/null 2>&1
if !v:shell_error
        augroup git-wip
                autocmd!
                autocmd BufWritePost * :call GitWipSave()
        augroup END
endif

