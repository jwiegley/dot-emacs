/* -*- tab-width: 4; indent-tabs-mode: nil; c-basic-offset: 4 -*-
 * xmlcomms.js
 *
 * This handles making XMLHttp calls to the "Edit Server"
 *
 * As no other parts of the extension can make xhr requests this
 * is essentially the gatekeeper to all contact with the Edit
 * Server.
 *
 * This file is part of emacs_chrome (http://github.com/stsquad/emacs_chrome)
 * and licensed under the GPLv3. See the COPYING file for details
 */

var settings = new Store("settings", {
    "edit_server_host": "127.0.0.1",
    "edit_server_port": 9292,
    "enable_button": true,
    "enable_dblclick": false,
    "enable_keys": false,
    "enable_debug": false
});

// Decorate console.log so that it only logs
// when the enable_debug setting is true
var orig_console_log = console.log;
console.log = function() {
    if (settings.get("enable_debug")) {
        orig_console_log.apply(console, Array.prototype.slice.call(arguments));
    }
};

// Get the base URL from which we make all requests to the server..
function getEditUrl()
{
    return "http://127.0.0.1:" + settings.get("edit_server_port") + "/";
}

/*
 * Give some feedback to the user via the icon/hover text.
 */
function updateUserFeedback(string, colour)
{
    console.log("updateUserFeedback: "+string);
    chrome.browserAction.setTitle({title:string});
    if (colour === null) {
        chrome.browserAction.setIcon({path:"../icons/emacs23-16x16.png"});
    } else if (colour == "green") {
        chrome.browserAction.setIcon({path:"../icons/emacs23-16x16-green.png"});
    } else if (colour == "red") {
        chrome.browserAction.setIcon({path:"../icons/emacs23-16x16-red.png"});
    } else if (colour == "darkblue") {
        chrome.browserAction.setIcon({path:"../icons/emacs23-16x16-darker.png"});
    } else {
        chrome.browserAction.setIcon({path:"../icons/emacs23-16x16.png"});
    }
}

// Initial message
updateUserFeedback("Awaiting edit request", "blue");

// Called when the user clicks on the browser action
// (or the activate extension key-stroke)
//
// When clicked we send a message to the current active tab's
// content script. If it fails we will never see an answer.
chrome.browserAction.onClicked.addListener(function(tab) {
    var find_msg = {
        msg: "find_edit"
    };
    var tab_port = chrome.tabs.connect(tab.id);
 
    tab_port.postMessage(find_msg);
    updateUserFeedback("sent request to content script", "green");
});

// Called when the browser passes another configured command action
// as defined in manifest.json (or configured in exttensions tab)
chrome.commands.onCommand.addListener(function(command) {
    console.log('onCommand listener:', command);
    if (command == "activate-emacs") {
        handleForegroundMessage();
    }
});

// Handle and edit request coming from the content page script
//
// Package up the text to be edited and send it to the edit server
function handleContentMessages(msg, tab_port)
{
    console.log("handleContentMessages called:"+JSON.stringify(msg));
    var cmd = msg.msg;
    var id = msg.id;
    var text = msg.text;
    var file = msg.file;

    var page_url = tab_port.sender.tab.url;
    var page_port = tab_port.portId_;
    console.log(" from page:"+page_url+" and tab port:"+page_port);

    var xhr = new XMLHttpRequest();
    var url = getEditUrl() + cmd;

    xhr.open("POST", url, true);

    xhr.onreadystatechange = function() {
        console.log("State change:"+ xhr.readyState + " status:"+xhr.status);
        // readyState 4=HTTP response complete
        if(xhr.readyState == 4) {
            if (xhr.status == 200) {
                xfile = xhr.getResponseHeader("x-file");
                xopen = xhr.getResponseHeader("x-open");
                console.log("x-file: "+xfile+" x-open: "+xopen);

                var update_msg = {
                    msg: "update",
                    text: xhr.responseText,
                    id: id
                };

                updateUserFeedback("Successful edit of "+msg.title);
                tab_port.postMessage(update_msg);

                msg.text = xhr.responseText;
                msg.file = xfile;
                if(xopen == "true") {
                    handleContentMessages(msg, tab_port);
                }
            } else if (xhr.status === 0) {
                // Is the edit server actually running?
                updateUserFeedback("Error: is edit server running?", "red");

                // Also do a notification to draw attention to the failure
                var notification = webkitNotifications.createNotification(
                    'icons/emacs23-16x16-red.png',
                    'Edit Server Error',
                    "Unable to contact an edit server, is it running?"+
                        " I'll take you to the options page when you close this"
                );
                notification.onclose = function() {
                    var fs_url =
                        chrome.extension.getURL('fancy-settings/source/index.html');
                    chrome.tabs.create(
                        {
                            'url': fs_url
                        }
                    );
                };
                notification.show();
            } else {
                updateUserFeedback("Un-handled response: "+xhr.status, "red");
            }
        }
    };

    // reset the display before sending request..
    updateUserFeedback("Edit request sent for "+msg.title, "green");

    xhr.setRequestHeader("Content-type", "text/plain");
    xhr.setRequestHeader("x-url", page_url);
    xhr.setRequestHeader("x-id", id);
    xhr.setRequestHeader("x-file", file);
    xhr.send(text);
}

/*
 * Handle and edit request coming from the content page script
 *
 * Package up the text to be edited and send it to the edit server
 */
function handleTestMessages(msg, tab_port)
{
    var url = getEditUrl() + "status";
    var xhr = new XMLHttpRequest();
    xhr.open("GET", url, true);
    xhr.onreadystatechange = function() {
        console.log("State change:"+ xhr.readyState + " status:"+xhr.status);
        // readyState 4=HTTP response complete
        if(xhr.readyState == 4) {
            if (xhr.status == 200) {
                tab_port.postMessage({msg: "test_result", text: xhr.responseText});
            } else if (xhr.status === 0) {
                tab_port.postMessage({msg: "test_result", text: "Edit Server Test failed: is it running?"});
            } else {
                tab_port.postMessage({msg: "test_result", text: "Un-handled response: "+xhr.status}); 
            }
        }
    };
    xhr.send();
}

/*
 * Handle foreground focus message
 *
 * This isn't really an edit request but will allow the edit-server running in emacs
 * to respond. My main use case for this is quickly spinning up a window on my Chromebook
 * because I can't focus emacs directly due to the rather minimal WM
 */
function handleForegroundMessage()
{
    var url = getEditUrl() + "foreground";
    var xhr = new XMLHttpRequest();
    xhr.open("POST", url, true);
    xhr.onreadystatechange = function() {
        console.log("handleForegroundMessage state change:"+ xhr.readyState + " status:"+xhr.status);
        // readyState 4=HTTP response complete
        if(xhr.readyState == 4) {
            if (xhr.status == 200) {
                updateUserFeedback(xhr.responseText);
            }
        }
    };
    xhr.setRequestHeader("Content-type", "text/plain");
    // get the contents of the clipboard
    var clipboard = document.getElementById("clipboardholder");
    clipboard.value = "";
    clipboard.select();
    document.execCommand("Paste");
    xhr.send(clipboard.value);
 }


// Handle config request messages, the textarea.js content script being in it's own
// isolated sandbox has to be fed all this via the IPC mechanisms

function handleConfigMessages(msg, tab_port)
{
    var config_msg = {
        msg: "config",
        enable_button: settings.get("enable_button"),
        enable_dblclick: settings.get("enable_dblclick"),
        enable_keys: settings.get("enable_keys"),
        enable_debug: settings.get("enable_debug")
    };
    tab_port.postMessage(config_msg);
}


/*
  Handle all in-coming messages to the extension.

  As other parts of the extension cannot trigger XHR requests they all
  send message to the main part of the extension to service these requests.
*/

function localMessageHandler(port)
{
    port.onMessage.addListener(function(msg, port) {
        if (msg.msg == "config") {
            handleConfigMessages(msg, port);
        } else if (msg.msg == "edit") {
            handleContentMessages(msg, port);
        } else if (msg.msg == "test") {
            handleTestMessages(msg, port);
        } else if (msg.msg == "error") {
            updateUserFeedback(msg.text, "red");
        } else if (msg.msg == "focus") {
            if (msg.id === null) {
                updateUserFeedback("Awaiting edit request: no focus", "darkblue");
            } else {
                updateUserFeedback("Awaiting edit request: in focus");
            }
        }
    });
}

// Hook up whenever someone connects to the extension comms port
chrome.extension.onConnect.addListener(localMessageHandler);
