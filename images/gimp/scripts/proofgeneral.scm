;;
;; Gimp script fu to make buttons from a source .xcf file.
;;
;; David Aspinall <da@dcs.ed.ac.uk>
;;
;; $Id$
;;


;; TODO: make greyed out, pressed, unpressed versions.
;; e.g. : Add bevel for "up" position:
;; (script-fu-add-bevel 0 image
;;     (car (gimp-image-active-drawable image)) "10" 0 0)

(define (script-fu-proofgeneral-make-button buttonname)
  (let* ((filename (string-append buttonname ".xcf"))
	 (image    (car (gimp-file-load 1 filename filename)))
	 (xpmname  (string-append buttonname ".xpm"))
	 (poor-xpm (string-append buttonname ".8bit.xpm")))
    (gimp-image-flatten image)
    ;; Full xpm
    (gimp-file-save 1 image (car (gimp-image-active-drawable image))
		    xpmname xpmname)
    ;; Impoverised xpm
    (gimp-convert-indexed image 1 0 8 1 1 "blah")
    (gimp-file-save 1 image (car (gimp-image-active-drawable image))
		    poor-xpm poor-xpm)
    ;; Finish
    (gimp-image-delete image)
    ))

(script-fu-register "script-fu-proofgeneral-make-button" 
		    "<Toolbox>/Xtns/Script-Fu/Proof General/Make Button"
		    "Save buttons in various formats"
		    "da@dcs.ed.ac.uk" "da@dcs.ed.ac.uk"
		    "1998/10/04"
		    ""
		    SF-VALUE "Button/file name" "\"goal\"")

(define (script-fu-proofgeneral-make-all-buttons)
  (mapcar script-fu-proofgeneral-make-button
	  '("goal" "next" "qed" "restart" "retract" "undo" "use" "state" "context" "info" "command" "find" "help" "interrupt" "goto" "abort")))

(script-fu-register "script-fu-proofgeneral-make-all-buttons" 
		    "<Toolbox>/Xtns/Script-Fu/Proof General/Make All Buttons"
		    "Save Proof General buttons in the various formats"
		    "da@dcs.ed.ac.uk" "da@dcs.ed.ac.uk"
		    "1998/10/04"
		    "")

(define (script-fu-proofgeneral-save-pic imgname)
  (let* ((filename (string-append imgname ".xcf"))
	 (image    (car (gimp-file-load 1 filename filename)))
	 (jpgname  (string-append imgname ".jpg"))
	 (gifname  (string-append imgname ".gif"))
	 (poorgifname  (string-append imgname ".8bit.gif")))
    ;; Flatten and save as jpg
    ;;(gimp-image-flatten image)
    ;; Flattening forces a white background.  Let's use merge.
    (if (> (car (gimp-image-get-layers image)) 1)
	(gimp-image-merge-visible-layers image 0))
    (file-jpeg-save 1 image (car (gimp-image-active-drawable image))
		    jpgname jpgname
		    0.75 0 1)
    ;; gif with full palette
    (gimp-convert-indexed image TRUE 255)
    (file-gif-save 1 image (car (gimp-image-active-drawable image))
		    gifname gifname
		    FALSE FALSE 0 0)
    ;; gif with impoverished palette for display in XEmacs
    (gimp-convert-rgb image)
    (gimp-convert-indexed image 1 15)
    (file-gif-save 1 image (car (gimp-image-active-drawable image))
		    poorgifname poorgifname
		    FALSE FALSE 0 0)
    ;; Finish
    (gimp-image-delete image)
    ))

(script-fu-register "script-fu-proofgeneral-save-jpg" 
		    "<Toolbox>/Xtns/Script-Fu/Proof General/Save Jpeg"
		    "Save image as jpeg"
		    "da@dcs.ed.ac.uk" "da@dcs.ed.ac.uk"
		    "1998/10/04"
		    ""
		    SF-VALUE "Basename" "\"test\"")


(define (script-fu-proofgeneral-save-all-pix)
  (mapcar script-fu-proofgeneral-save-pic
	  '("ProofGeneral" "pg-text")))

(script-fu-register "script-fu-proofgeneral-save-all-jpegs" 
		    "<Toolbox>/Xtns/Script-Fu/Proof General/Save all Jpegs"
		    "Save Proof General images as jpegs"
		    "da@dcs.ed.ac.uk" "da@dcs.ed.ac.uk"
		    "1998/10/04"
		    "")