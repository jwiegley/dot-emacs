;; pg-metadata.el   Persistant storage of metadata for proof scripts
;;
;; Copyright (C) 2001-2 LFCS Edinburgh. 
;; Author:      David Aspinall
;; Maintainer:  Proof General maintainer <proofgen@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; Status: incomplete; experimental
;;
;; TODO: 
;;  - add file dependency information to proof scripts individually
;;    (can approximate from the transitive closure that is included files list)
;;

(require 'pg-xml)

;; Variables

(defcustom pg-metadata-default-directory "~/.proofgeneral/"
  "*Directory for storing metadata information about proof scripts."
  :type 'file
  :group 'proof-user-options)

(defface proof-preparsed-span 
  (proof-face-specs
   (:background "lightgoldenrodyellow")
   (:background "darkgoldenrod")
   (:underline t))
  "*Face for pre-parsed regions of proof script (unprocessed commands)."
  :group 'proof-faces)


;; Utility functions

(defun pg-metadata-filename-for (filename)
  "Compute a revised FILENAME for storing corresponding metadata."
  ;; We replace directory separators with double underscores.
  ;; Clashes are possible, hopefully unlikely.
  (concat
   (file-name-as-directory pg-metadata-default-directory)
   (replace-in-string 
    (file-name-sans-extension filename)
    (regexp-quote (char-to-string directory-sep-char))
    "__")
   ".pgm"))


;; Main code

(defun pg-write-metadata-file (buffer)
  "Write meta data for a script buffer BUFFER."
  ;; FIXME: should check buffer has been saved
  (if (buffer-file-name buffer)
      (let* ((scriptfile    (buffer-file-name buffer))
	     (modtime	    (nth 5 (file-attributes scriptfile)))
	     (metadatafile  (pg-metadata-filename-for scriptfile))
	     (metadatabuf   (find-file-noselect metadatafile 'nowarn))
	     (span	   (span-at (point-min) 'type)))
	     type)
	(pg-xml-begin-write)
	(pg-xml-openelt 'script-file 
			(list (list 'filename scriptfile)
			      (list 'filedate modtime)))
	(pg-xml-closeelt)
	(while span
	  (let ((type  (span-property span 'type))
		(name  (span-property span 'name))
		(start (span-start span))
		(end   (span-end span)))
	  (pg-xml-openelt 
	   'span
	   (list (list 'type type)
		 (list 'name name)
		 (list 'start start)
		 (list 'end end)))
	  ;; Include the span contents: can recover script file
	  ;; from this.  (Could even display script using special
	  ;; display functions?)
	  (pg-xml-writetext (buffer-substring start end buffer))
	  (pg-xml-closeelt))
	  (setq span (next-span 'type)))
	(with-current-buffer metadatabuf
	  (delete-region (point-min) (point-max))
	  (insert (pg-xml-doc))
	  (write-file metadatafile))))


;(defun pg-read-metadata-file (buffer)
;  "Read meta data for a script file BUFFER, and reconstitute spans.
;Spans are only reconstituted for positions after (proof-unprocessed-begin),
;and providing that the meta-data file is older than the script file."
;  (if (buffer-file-name buffer)
;      (let* ((scriptfile    (buffer-file-name buffer))
;	     (modtime	    (nth 5 (file-attributes scriptfile)))
;	     (metadatafile  (pg-metadata-filename-for scriptfile))
;	     (metadatabuf   (find-file-noselect metadatafile 'nowarn))
;	     (metadata      (pg-xml-parse-buffer metadatabuf)))
	
;	     (span	   (span-at (point-min) 'type)))
;	     type)


(provide 'pg-metadata)
;; pg-metadata.el ends here.
  
	
	  

	  
		     
  