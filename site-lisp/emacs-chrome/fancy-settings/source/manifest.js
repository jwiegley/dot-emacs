// Edit with Emacs options
this.manifest = {
    "name": "Edit with Emacs",
    "icon": "../../icons/emacs.png",
    "settings": [
        {
            "tab": i18n.get("information"),
            "group": i18n.get("Setup"),
            "name": "Description",
            "type": "description",
            "text": i18n.get("description")
        },
        {
            "tab": i18n.get("information"),
            "group": i18n.get("Focusing Emacs"),
            "name": "Description",
            "type": "description",
            "text": i18n.get("focus")
        },
        {
            "tab": "Configuration",
            "group": "Edit Server",
            "name": "edit_server_host",
            "type": "text",
            "label": "Edit Server Host:",
        },
        {
            "tab": "Configuration",
            "group": "Edit Server",
            "name": "edit_server_port",
            "type": "text",
            "label": "Edit Server Port:",
        },
	{
            "tab": "Configuration",
            "group": "Interface",
	    "name": "enable_button",
	    "type": "checkbox",
	    "label": "Show 'edit' button next to textarea"
	},
	{
            "tab": "Configuration",
            "group": "Interface",
	    "name": "enable_contextmenu",
	    "type": "checkbox",
	    "label": "Enable context menu item to invoke editor"
	},
	{
            "tab": "Configuration",
            "group": "Interface",
	    "name": "enable_dblclick",
	    "type": "checkbox",
	    "label": "Allow double click on textarea to invoke editor"
	},
	{
            "tab": "Configuration",
            "group": "Interface",
	    "name": "enable_keys",
	    "type": "checkbox",
	    "label": "Enable Alt-Enter Keyboard shortcut to invoke editor"
	},
        {
            "tab": "Test",
            "group": "Test",
	    "name": "TestButton",
            "type": "button",
            "label": i18n.get("Test Edit Server"),
	    "text": i18n.get("Test")
        },
        {
            "tab": "Test",
            "group": "Test",
            "name": "enable_debug",
            "type": "checkbox",
            "label": i18n.get("enable_debug")
        }
    ]
};
