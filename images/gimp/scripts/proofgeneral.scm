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
	 (poor-xpm (string-append buttonname ".8bit.xpm"))
	 (xbmname  (string-append buttonname ".xbm")))
    (gimp-image-flatten image)
    ;; Full xpm
    (gimp-file-save 1 image (car (gimp-image-active-drawable image))
		    xpmname xpmname)
    ;; Impoverised xpm
    (gimp-convert-indexed image 1 8)
    (gimp-file-save 1 image (car (gimp-image-active-drawable image))
		    poor-xpm poor-xpm)
    ;; Mono image
    (gimp-convert-rgb image)
    (gimp-image-flatten image)
    (gimp-convert-indexed-palette image 1 3 0 "")
    (file-xbm-save 1 image (car (gimp-image-active-drawable image))
		    xbmname xbmname
		    "Proof General button"
		    FALSE 0 0 "")
    ;; Finish
    (gimp-image-delete image)
    ))

(script-fu-register "script-fu-proofgeneral-make-button" 
		    "<Toolbox>/Xtns/Script-Fu/Proof General/Make Button"
		    "Save buttons in various formats"
		    "da@dcs.ed.ac.uk" "da@dcs.ed.ac.uk"
		    "1998/10/04"
		    ""
		    SF-VALUE "Button/file name" "\"test\"")

(define (script-fu-proofgeneral-make-all-buttons)
  (mapcar script-fu-proofgeneral-make-button
	  '("goal" "next" "qed" "restart" "retract" "undo" "use")))

(script-fu-register "script-fu-proofgeneral-make-all-buttons" 
		    "<Toolbox>/Xtns/Script-Fu/Proof General/Make All Buttons"
		    "Save Proof General buttons in the various formats"
		    "da@dcs.ed.ac.uk" "da@dcs.ed.ac.uk"
		    "1998/10/04"
		    "")

(define (script-fu-proofgeneral-save-jpg imgname)
  (let* ((filename (string-append imgname ".xcf"))
	 (image    (car (gimp-file-load 1 filename filename)))
	 (jpgname  (string-append imgname ".jpg"))
	 (gifname  (string-append imgname ".gif")))
    ;; Flatten and save as jpg
    (gimp-image-flatten image)
    (file-jpeg-save 1 image (car (gimp-image-active-drawable image))
		    jpgname jpgname
		    0.75 0 1)
    ;; Poor jpegs for display in XEmacs, limit to 10 colours.
    (gimp-convert-indexed image 1 10)
    (file-gif-save 1 image (car (gimp-image-active-drawable image))
		    gifname gifname
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


(define (script-fu-proofgeneral-save-all-jpegs)
  (mapcar script-fu-proofgeneral-save-jpg
	  '("ProofGeneral" "text_proof" "text_general")))

(script-fu-register "script-fu-proofgeneral-save-all-jpegs" 
		    "<Toolbox>/Xtns/Script-Fu/Proof General/Save all Jpegs"
		    "Save Proof General images as jpegs"
		    "da@dcs.ed.ac.uk" "da@dcs.ed.ac.uk"
		    "1998/10/04"
		    "")