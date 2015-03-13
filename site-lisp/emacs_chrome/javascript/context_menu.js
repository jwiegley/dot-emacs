// -*- tab-width:2; indent-tabs-mode:t -*- vim: set noet ts=2:
(function(){

	var edit_msg = {};

	function menuClicked(info, tab) {
		if (edit_msg) {
			var tab_port = chrome.tabs.connect(tab.id);
			tab_port.sender = { tab: tab };
			handleContentMessages(edit_msg, tab_port);
		}
	}


	var menu_enabled = false;

	function enableContextMenu() {
		if (!menu_enabled) {
			chrome.contextMenus.removeAll();
			chrome.contextMenus.create({
				title: "Edit with Emacs",
				contexts: ["editable"],
				onclick: function(info, tab) {
					menuClicked(info, tab);
				}
			});
			menu_enabled = true;
		}
	}

	function disableContextMenu() {
		chrome.contextMenus.removeAll();
		menu_enabled = false;
	}

	// Initialize the context menu based on stored options.
	// Also, default to enabled if the setting hasn't been saved before.
	if (localStorage.enable_contextmenu === "true" ||
			!localStorage.hasOwnProperty('enable_contextmenu')) {
		enableContextMenu();
	} else {
		disableContextMenu();
	}


	function processRequest(request, sender, sendResponse) {
		if (request.type === "menu_target") {
			edit_msg = request.edit_msg;
		} else if (request.type === "enable_contextmenu") {
			if (request.enabled) {
				enableContextMenu();
			} else {
				disableContextMenu();
			}
		}
		sendResponse({});
	}

	chrome.extension.onRequest.addListener(processRequest);

})();

