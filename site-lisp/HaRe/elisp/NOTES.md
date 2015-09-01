Interactive elisp shell

    M-x ielm

Break on unhandled error, put in .emacs

    (add-hook 'after-init-hook
          '(lambda () (setq debug-on-error t)))


If you get weird errors about changes in the number of arguments in a
function, delete the .elc files in this directory and compile again.
Also, do

    M-x unload-feature
    hare

Very useful resource: <http://www.emacswiki.org/emacs/ElispCookbook>

Menus: <http://ergoemacs.org/emacs/elisp_menu.html>
