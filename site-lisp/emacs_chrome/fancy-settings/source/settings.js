/* Message handling multiplexer */
function localMessageHandler(msg, port) {
	// What was the bidding?
	var cmd = msg.msg;
	if (cmd == "test_result") {
	    alert(msg.text);
	} else {
	    console.log("localMessageHandler: un-handled message:"+cmd);
	}
}

// Test for the presence of an Edit Server
function test_server() {
	var port = chrome.extension.connect();
	port.onMessage.addListener(localMessageHandler);
	port.postMessage({msg: "test"});
}

window.addEvent("domready", function () {
    new FancySettings.initWithManifest(function (settings) {
        settings.manifest.TestButton.addEvent("action", test_server);
    });
});
