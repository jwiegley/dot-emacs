var ws;

function write(data){
  var before = document.getElementById("buffer").innerHTML;
  document.getElementById("buffer").innerHTML = before + data;
  window.scrollTo(0,document.body.scrollHeight); }

function read(){
  var tmp = document.getElementById("mini-buffer").value;
  document.getElementById("mini-buffer").value = "";
  write(tmp + "\n");
  return tmp; }

function connect(){
  ws = new WebSocket("ws://localhost:%d/");
  ws.onopen    = function()    { write("<p><i>connected</i></p>"); };
  ws.onmessage = function(msg) { write(msg.data); };
  ws.onclose   = function()    { write("<p><i>closed</i></p>"); }; }

window.onload = function(){
  document.getElementById("mini-buffer").addEventListener(
    "keyup", function(e){ if(e.keyCode == 13){ ws.send(read()); } }); }
