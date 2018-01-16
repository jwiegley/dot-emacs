// SAMPLE
this.i18n = {
    "settings": {
        "en": "Settings",
        "de": "Optionen"
    },
    "search": {
        "en": "Search",
        "de": "Suche"
    },
    "nothing-found": {
        "en": "No matches were found.",
        "de": "Keine Übereinstimmungen gefunden."
    },
    
    
    
    "information": {
        "en": "Information",
        "de": "Information"
    },
    "login": {
        "en": "Login",
        "de": "Anmeldung"
    },
    "username": {
        "en": "Username:",
        "de": "Benutzername:"
    },
    "password": {
        "en": "Password:",
        "de": "Passwort:"
    },
    "x-characters": {
        "en": "6 - 12 characters",
        "de": "6 - 12 Zeichen"
    },
    "x-characters-pw": {
        "en": "10 - 18 characters",
        "de": "10 - 18 Zeichen"
    },
    "description": {
        "en": "Edit with Emacs is an extension that allows you to edit textareas and other editable text elements\
        of a web-page with your favourite editor. For this to work you need to be running an \"edit server\"\
        on your local machine. This is because extensions in Chrome(ium) cannot directly start new programs. For Emacs users \
        it is recommended you use the use supplied native <a href=\"/servers/edit-server.el\">edit-server.el</a>.\
	Alternativley you can track the latest version through the <a href=\"http://melpa.milkbox.net/\">MELPA</a>\
	package archive.\
        </p>\
	<p>\
        Save the file to somewhere visible to your your Emacs <code>load-path</code> (~/.emacs.d is popular) and add the following\
        to your <code>.emacs</code>:\
        </p>\
	<pre>\
          (add-to-list 'load-path \"~/.emacs.d\")<br>\
          (require 'edit-server)<br>\
          (edit-server-start)\
	</pre>\
        For details about how to customise and control the behaviour of the edit server please see the\
        <a href=\"http://www.emacswiki.org/emacs/Edit_with_Emacs\">page on the Emacs Wiki</a>.\
	</p>\
	<p>\
	If for some reason you do not want to use Emacs there is a list of alternative servers\
	on the <a href=\"https://github.com/stsquad/emacs_chrome/wiki/edit-server\">project site</a>\
	</p>",
    },
    "focus": {
        "en": "A new feature of Edit with Emacs is the ability to bring up a new frame or focus an existing\
               Emacs session. This is triggered by a customisable keyboard shortcut\
               (see bottom of <a href=\"chrome://extensions/\"extensions\">extensions page</a>).\
               The action <em>Activate Emacs with contents of clipboard</em> will send\
               a <em>foreground</em> request to the edit server. I wrote this to support running Emacs on\
               my Chromebook. You will need to have started emacs in a <a href=\"https://github.com/dnschneid/crouton\">\
               Crouton</a> chroot using the <em>host-x11</em> script. For example:<br>\
               <pre>\
                 /usr/local/bin/host-x11 emacs --daemon\
               </pre>\
               You may need to experiment with frame configuration settings under ChromeOS as Aura is not a normal X11\
               window manager. Under non-ChromeOS set-ups it will behave just like an edit request although no buffer\
               is created for the new frame. However the contents of the clipboard (from the browser) will be copied into\
               the Emacs kill-ring."
    },
    "logout": {
        "en": "Logout",
        "de": "Abmeldung"
    },
    "enable": {
        "en": "Enable",
        "de": "Aktivieren"
    },
    "disconnect": {
        "en": "Disconnect:",
        "de": "Trennen:"
    },
    "enable_debug": {
        "en": "Enable debug (logs to the console)",
        "de": "Debug (Protokolle an die Konsole)"
    }
};
