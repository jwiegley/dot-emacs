;;; elnode-bm.el -- bookmarking helpers with elnode   -*- lexical-binding: t -*-

(require 'elnode)
(require 's)

(defgroup elnode-bookmark nil
  "The Elnode bookmarker application."
  :group 'elnode)

(defcustom elnode-bookmark-file-name "~/bookmarks.org"
  "The filename used to log bookmarks.

This file is expanded to find the file that bookmarks will be
stored in."
  :group 'elnode-bookmark
  :type 'filename)

(defun elnode-stud (port forward-port pem-file)
  "Start stud on PORT, sending to FORWARD-PORT with PEM-FILE."
  (start-process
   "elnode-stud" "elnode-stud"
   "stud" "-ssl" "-b" "127.0.0.1,8004" "-f" "*,8443" (expand-file-name pem-file))
  (switch-to-buffer "elnode-stud"))

(defun elnode-bm-time->org (time)
  "Format the specified time in org-mode format."
  (format-time-string "[%Y-%m-%d %a %H:%M]" time))

(defun elnode-bm-save (httpcon)
  "Take a bookmarklet and save it."
  (let* ((method (elnode-http-method httpcon))
         (page (decode-coding-string
                (elnode-http-param httpcon "u")
                'utf-8))
         (title (or
                 (decode-coding-string
                  (elnode-http-param httpcon "i")
                  'utf-8)
                 page))
         (time (seconds-to-time
                (/ (string-to-int
                    (elnode-http-param httpcon "t"))
                   1000))))
    (with-current-buffer
        (find-file-noselect
         (expand-file-name elnode-bookmark-file-name))
      (case major-mode
        ('org-mode
         (save-excursion
           (goto-char (point-min))
           (let ((org-time-str
                  (elnode-bm-time->org time)))
             (insert
              (s-lex-format
               "* [[${page}][${title}]] ${org-time-str}\n")))))))
    (elnode-send-json httpcon (list :ok))))

(defun elnode-bm-chrome-ext (httpcon)
  "Send the chrome extension."
  (elnode-send-file
   httpcon
   (concat 
    (file-name-directory
     (or (buffer-file-name)
         load-file-name
         default-directory))
    "bookmark4chrome.crx")
   :mime-types
   '(("application/x-chrome-extension" . "crx"))))

(defun elnode-bm-index (httpcon)
  (elnode-send-html httpcon "<html>
<style>
body { font-family: sans-serif;}
</style>
<body>
<h1>Elnode Bookmarking IT</h1>
chrome extension: <a href=\"/elnode-bookmarks.crx\">elnode</a><br></br>
bookmarklet: <a href=\"javascript:function elnodebm001(){
var d=document,
i=''+d.title,
z=d.createElement('scr'+'ipt'),
b=d.body,
l=d.location;
try{
if(!b)throw(0);
z.setAttribute('src','http://localhost:8004/bm/save?u='
+encodeURIComponent(l.href)
+'&t='+(new Date().getTime())
+'&i='+encodeURIComponent(i));
b.appendChild(z);
}catch(e){
alert('Please wait until the page has loaded.');
}
}
elnodebm001();void(0)\">elnode</a>
</body></html>"))

;;;###autoload
(defun elnode-bm-handler (httpcon)
  (elnode-hostpath-dispatcher
   httpcon
   '(("^[^/]+//$" . elnode-bm-index)
     ("^[^/]+//elnode-bookmarks.crx" . elnode-bm-chrome-ext)
     ("^[^/]+//bm/save" . elnode-bm-save)
     ("^[^/]+//bm/report" . elnode-bm-report))))

(provide 'elnode-bm)

;;; elnode-bm.el ends here
