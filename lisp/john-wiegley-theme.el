(deftheme john-wiegley
  "Dark theme used by John Wiegley.")

;; Luminosity 50
(defconst palette-red               "#FF0000")
(defconst palette-orange            "#FF8000")
(defconst palette-yellow            "#FFFF00")
(defconst palette-yellow-green      "#80FF00")
(defconst palette-green             "#00FF00")
(defconst palette-teal              "#00FF80")
(defconst palette-cyan              "#00FFFF")
(defconst palette-slate-blue        "#007FFF")
(defconst palette-blue              "#0000FF")
(defconst palette-indigo            "#7F00FF")
(defconst palette-purple            "#FF00FF")
(defconst palette-fuschia           "#FF0080")

;; Luminosity 20
(defconst palette-red-dark          "#660000")
(defconst palette-orange-dark       "#663300")
(defconst palette-yellow-dark       "#666600")
(defconst palette-yellow-green-dark "#336600")
(defconst palette-green-dark        "#006600")
(defconst palette-teal-dark         "#006633")
(defconst palette-cyan-dark         "#006666")
(defconst palette-slate-blue-dark   "#003366")
(defconst palette-blue-dark         "#000066")
(defconst palette-indigo-dark       "#330066")
(defconst palette-purple-dark       "#660066")
(defconst palette-fuschia-dark      "#660033")

;; Luminosity 15
(defconst palette-red-darker          "#4D0000")
(defconst palette-orange-darker       "#4D2600")
(defconst palette-yellow-darker       "#4D4D00")
(defconst palette-yellow-green-darker "#264D00")
(defconst palette-green-darker        "#004D00")
(defconst palette-teal-darker         "#004D26")
(defconst palette-cyan-darker         "#004D4D")
(defconst palette-slate-blue-darker   "#00264D")
(defconst palette-blue-darker         "#00004D")
(defconst palette-indigo-darker       "#26004D")
(defconst palette-purple-darker       "#4D004D")
(defconst palette-fuschia-darker      "#4D0026")

;; Luminosity 10
(defconst palette-red-darkest          "#330000")
(defconst palette-orange-darkest       "#331A00")
(defconst palette-yellow-darkest       "#333300")
(defconst palette-yellow-green-darkest "#1A3300")
(defconst palette-green-darkest        "#003300")
(defconst palette-teal-darkest         "#00331A")
(defconst palette-cyan-darkest         "#003333")
(defconst palette-slate-blue-darkest   "#001A33")
(defconst palette-blue-darkest         "#000033")
(defconst palette-indigo-darkest       "#1A0033")
(defconst palette-purple-darkest       "#330033")
(defconst palette-fuschia-darkest      "#33001A")

;; (custom-theme-set-faces
;;  'john-wiegley
;;  `(default ((,class :background ,main-bg :foreground ,main-fg)))
;;  `(cursor ((,class :background ,red)))
;;  `(font-lock-builtin-face ((,class :foreground ,blue)))
;;  `(font-lock-string-face ((,class :foreground ,green))))

(provide-theme 'john-wiegley)

(provide 'john-wiegley-theme)
