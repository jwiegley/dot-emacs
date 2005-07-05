;; $State$ $Date$ $Revision$ 
;;--------------------------------------------------------------------------;;
;;--------------------------------------------------------------------------;;
;; messages in various languages

(provide 'phox-lang)

(defvar phox-lang
  (let* ((s1 (getenv "LANG")) (s2 (getenv "LC_LANG")) (s (if s1 s1 s2)))
    (message s)
    (cond
      ((or (string= s "en") (string= s "us")) 'en)
      ((string= s "fr") 'fr)
      (t 'en))))

 
(defun phox-lang-absurd ()
  (case phox-lang 
    (en "By absurd")
    (fr "Par l'absurde")))

(defun phox-lang-suppress (s)
  (case phox-lang
    (en (concat "Remove hypothesis " s " (if it became useless)."))
    (fr (concat  "Supprimer l'hypothèse " s " (si elle est devenue inutile)."))))

(defun phox-lang-opendef ()
  (case phox-lang 
    (en "Expand the definition: ")
    (fr "Ouvre la définition : ")))

(defun phox-lang-instance (s)
  (case phox-lang
    (en (concat "Choose " s " = "))
    (fr (concat  "Choisissons " s " = "))))

(defun phox-lang-prove ()
  (case phox-lang 
    (en "Let us prove \\[ \\].")
    (fr "Prouvons \\[ \\].")))

(defun phox-lang-let ()
  (case phox-lang 
    (en "Let \\[ \\] = \\[ \\].")
    (fr "Définissons \\[ \\] = \\[ \\].")))
