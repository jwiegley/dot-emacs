theory TextProps imports Main begin

(* Note: nesting regions shows up possible text property 
   merging problem inside Emacs/font-lock

   \<^bbold>Bold and \<^bitalic>italic\<^eitalic>\<^ebold>

   ;; good, desirable property value for 'face 
   (append '(:slant italic) '(:weight bold font-lock-string-face))
   (:slant italic :weight bold font-lock-string-face)

   ;; bad, value obtained with font-lock-{append/prepend}-property:
   (append '(:slant italic) '((:weight bold font-lock-string-face)))
   (:slant italic (:weight bold font-lock-string-face))

   For now we work around this in unicode-tokens 
   (see unicode-tokens-prepend-text-properties)
*)

term "\<^bbold>Bold and \<^bitalic>italic\<^eitalic>\<^ebold>"

end
