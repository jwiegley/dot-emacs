; To use holes-mode, require this file in your .emacs and add path to
; holes.el in the load-path of emacs

(autoload 'holes-mode "holes"
  "Minor mode for using \"holes\" in your buffers." t)
(autoload 'holes-set-make-active-hole "holes"
  "Makes a new hole and make it active." t)
(autoload 'holes-abbrev-complete "holes"
  "Completes an abbreviation, and replace #s ans @{}s by holes.")
(autoload 'holes-insert-and-expand "holes"
  "insert and expand an abbreviation, and replace #s ans @{}s by holes.")

(provide 'holes-load)

