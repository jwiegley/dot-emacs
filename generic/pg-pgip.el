;; pg-pgip.el	 Functions for processing PGIP for Proof General
;;
;; Copyright (C) 2000 LFCS Edinburgh. 
;;
;; Author: David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;
;; Proof General Kit uses PGIP, an XML-message protocol
;; for interactive proof.  This file contains functions 
;; to process PGIP commands.
;;

(defun pg-pgip-process-cmd (pgip) 
  "Process the command in PGIP, which should be parsed XML according to pg-xml-parse-*."
  ;; blah blah
  )

(defpacustom goals-limit  10
  "Setting for maximum number of goals printed in Isabelle."
  :type 'integer
  :setting "<pgip><setpref name=\"goals_limit\">%i</setpref></pgip>")


;; End of `pg-pgip.el'


