# Do be do

This library lets Emacs talk to a page in a web browser. For now, it's
specifically aimed at telling the browser to update the stylesheet, in
a similar fashion to Firefox's latest Style Editor.

Video examples

* http://www.youtube.com/watch?v=JnImnaCkOMk

* http://chrisdone.com/bdo.ogv

# Usage

Add the library path (this is needed to be able to find bdo.js):

    (add-to-list 'load-path "/the/path/to/bdo")

Optional keybinding:

    (define-key css-mode-map (kbd "C-x C-s") 'css-refresh)
    (defun css-refresh ()
      "Refresh the current CSS file."
      (interactive)
      (when (buffer-modified-p)
        (save-buffer))
      (bdo-refresh))

To make Emacs start listening, run

    M-x bdo-listen

Then add the following in your web page:

    <script type="text/javascript" src="http://localhost:9090/bdo"></script>

You can use a browser userscript to make your browser insert that line on the
fly, on some webs. See contrib/bdo.user.js.

The script depdends on jQuery. If that's a problem, you can hack
around it and give me a patch.

(Or whichever port you configured bdo-port to, if you changed it.)

Load your web page, it will connect to Emacs. Emacs will say “New
client: http://your/address”, or if you refresh, it says “Client
re-connected: http://your/address”.

Go to your stylesheet file in Emacs which corresponds to one of the
.css files loaded with a `link` tag in your page. Run `M-x
bdo-refresh`.

* This will prompt for which client (browser page) you
  want to talk to, and then it will prompt which CSS file corresponds to
  this one.
* Then it will tell the browser to refresh that
  stylesheet. Running `M-x bdo-refresh` again will not prompt for these
  again.

If you change your mind, you can run `M-x bdo-set-client` or
`M-x bdo-set-link` to set the client or link element referred to.
