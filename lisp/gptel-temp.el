(defun my-current-temperature (place)
  (interactive "sLocation: ")
  (with-current-buffer
      (url-retrieve-synchronously
       (url-encode-url
        (format
         "http://api.weatherapi.com/v1/current.json?key=%s&q=%s&aqi=yes"
         (lookup-password "api.weatherapi.com" "jwiegley@gmail.com" 80)
         place)))
    (goto-char (point-min))
    (goto-char url-http-end-of-headers)
    (let ((json (json-parse-buffer :object-type 'alist)))
      (kill-buffer (current-buffer))
      (alist-get 'temp_f (alist-get 'current json)))))

(defun my-gptel-rag-with-current-temperature (messages)
  (let ((last-user (gptel-rag-last-user-message messages)))
    (when (string-match "temperature in \\(.+?\\)\\?" last-user)
      (gptel-rag-add-system-message
       messages
       (let ((place (match-string 1 last-user)))
         (format "The current temperature in %s is %s"
                 place (my-current-temperature place)))))))

(provide 'gptel-temp)
