;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defadvice ido-visit-buffer (before switch-to-buffers-workgroup
                                    (buffer method &optional record)
                                    activate)
  "If a workgroup is showing BUFFER, switch to it first"
  (wg-aif (wg-find-buffer (if (bufferp buffer)
                              (buffer-name buffer)
                            buffer))
      (ignore-errors
        (wg-switch-to-workgroup it))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
