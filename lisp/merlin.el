(defun merlin-record-times ()
  (interactive)
  (require 'rx)
  (let* ((text (buffer-substring-no-properties (line-beginning-position)
                                               (line-end-position)))
         (regex
          (rx (and string-start (0+ space)
                   (group (and (= 2 num) ?/ (= 2 num) ?/ (= 2 num)
                               space (= 2 num) ?: (= 2 num) space
                               (in "AP") ?M)) (1+ space)
                   (group (and (= 2 num) ?/ (= 2 num) ?/ (= 2 num)
                               space (= 2 num) ?: (= 2 num) space
                               (in "AP") ?M)) (1+ space)
                   (? (and (group ?*) (1+ space)))
                   (group (1+ (or digit (in ".hms"))))
                   (1+ space) (group (1+ nonl)) string-end))))
    (if (string-match regex text)
        (let ((start (match-string 1 text))
              (end (match-string 2 text))
              (cleared (match-string 3 text))
              (duration (match-string 4 text)) commodity
              (account (match-string 5 text)))
          (when (string-match "\\([0-9.]+\\)\\([mhs]\\)" duration)
            (setq commodity (match-string 2 duration)
                  duration (match-string 1 duration))
            (cond ((string= commodity "h")
                   (setq commodity "hours"))
                  ((string= commodity "m")
                   (setq commodity "minutes"))
                  ((string= commodity "s")
                   (setq commodity "seconds"))))
          (if (string-match "\\([0-9.][0-9.a-z]+\\)" account)
              (setq account (match-string 1 account)))
          (do-applescript
           (format "
  tell application \"Merlin\"
  activate

  set act to 0

  set listActivity to every activity of first document
  repeat with oneActivity in listActivity
  if subtitle of oneActivity is \"%s\" then
  set act to oneActivity
  exit repeat
  end if
  end repeat

  if act is 0 then
  set myselection to selected object of main window of first document as list

  if (count of myselection) is 0 then
  display dialog \"Please select activity to set time for\" buttons {\"OK\"}
  else
  set act to beginning of myselection
  end if
  end if

  if act is 0 or (class of act is project) or (is milestone of act is true) then
  display dialog \"Cannot locate activity for %s\" buttons {\"OK\"}
  else
  tell act
  if ((class is not project) and (is milestone is not true)) then
  set actual start date to (date \"%s\")
  if %s then
  set actual end date to (date \"%s\")
  delete last actuals reporting date

  set given remaining work to {amount:0, unit:hours, floating:false, ¬
  relative error:0}
  else
  delete actual end date
  set last actuals reporting date to (date \"%s\")
  end if
  set given actual work to {amount:%s, unit:%s, floating:false, ¬
  relative error:0}
  end if
  end tell
  end if
  end tell" account account start (if cleared "true" "false")
            end end  duration commodity))))))
