[![MELPA](http://melpa.org/packages/helm-firefox-badge.svg)](http://melpa.org/#/helm-firefox)
[![MELPA Stable](https://stable.melpa.org/packages/helm-firefox-badge.svg)](https://stable.melpa.org/#/helm-firefox)

<p>You can <a href="https://www.paypal.com/cgi-bin/webscr?cmd=_donations&amp;business=thierry.volpiatto@gmail.com&amp;lc=US&amp;currency_code=EUR&amp;bn=PP-DonationsBF:btn_donateCC_LG.gif:NonHosted"><img src="https://www.paypalobjects.com/en_US/i/btn/btn_donate_LG.gif" alt="Donate" title="" /></a> to help this project.</p>

# helm-firefox

Emacs helm interface for firefox bookmarks.

## Dependencies

You have first to install [helm](https://github.com/emacs-helm/helm) in order to make this working.
If you install from MELPA you don't have to care of this.

## Prerequisite

You will have to set firefox to import bookmarks in his html file bookmarks.html.
(only for firefox versions >=3)
To achieve that, open `about:config` in firefox url toolbar and go to this line:

    user_pref("browser.bookmarks.autoExportHTML", false);

Double click on this line to enable its value to `true`, you should have now:

    user_pref("browser.bookmarks.autoExportHTML", true);

NOTE: This is also working in the same way for mozilla aka seamonkey.

## Install

The easiest way is to install from MELPA.
Otherwise put this file in `load-path` compile it and add in your init file:

    (autoload 'helm-firefox-bookmarks "helm-firefox" nil t)
    
## Setup

On GNU Linux probably you can keep default setting, otherwise you may have to
setup `helm-firefox-default-directory` to some other value.

## Create a bookmarklet to jump to helm-firefox from firefox (facultative)

1) Create the bookmarklet in firefox:
   - Add a bookmark named `ffbookmarks` in your personal bar in firefox.
   - Right click on it and add `javascript:location.href='ffbookmarks://localhost'` as url.
   
2) Add the `ffbookmarks` script in a directory of your `PATH`.

3) Install [firefox-protocol](https://github.com/thierryvolpiatto/firefox-protocol)

   M-x `firefox-protocol-installer-install` RET `ffbookmarks` RET `/path/to/ffbookmarks`

Of course as the script use emacsclient you need an emacs session with a server running 
along with firefox to make this working.

Also to come back to firefox when you select a bookmark or abort with C-g this script is using
wmctrl program, so you should install it.
By default the script is assuming the firefox executable is "firefox", to modify this you can add
to your env vars in .profile or .bashrc:

    export FIREFOXEXE="name of your firefox executable"

