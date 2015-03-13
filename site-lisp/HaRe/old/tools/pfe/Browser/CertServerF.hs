module CertServerF(certServerF,backspace) where
import Fudgets
--import AllFudgets(expandTabs)
import Char(isDigit)
import FudExtras(longTextChoicePopupF)

certServerF =
   loopThroughRightF (absF certServerSP)
	             (delayF shF>+<longTextChoicePopupF)

shF = --teeF show "shF" >==<
      (inputLinesSP -+- inputLinesSP) >^^=< subProcessF "sh" >=^< (++"\n")

certServerSP = loop
  where
    loop = get $ either ignore fromInput

    ignore _ = loop -- ignore output from shell while waiting for a cmd

    fromInput cmd =
      putSh ("LANG=C "++cmd ++ " ; echo +-+ $?") $
      getResult $ \ res ->
      output res $
      loop

getResult cont = loop []
  where
    loop acc = dispatch fromShell fromPopup ignore
      where
        ignore _ = loop acc -- ignore new cmds while a cmd is in progress

        fromShell l =
	  case l of
	    Left ('+':'-':'+':' ':s) | all isDigit s ->
	      cont (s=="0",reverse acc)
	    Right "+-+ Yes No" -> popup (msgTxt acc,("Yes","No")) (loop [])
	    --Right ('+':'-':'+':' ':s) -> cont (s=="0",reverse acc)
	    _ -> loop (mapEither backspace backspace l:acc)

        fromPopup msg = putSh msg (loop acc)

        msgTxt = map stripEither . reverse

output = put . Right
putSh = put . Left . Left
popup = put . Left . Right

dispatch fromShell fromPopup fromInput =
    get $ either (either fromShell fromPopup) fromInput

--confirmString Confirm = "Yes"
--confirmString Cancel = "No"


-- Interpret the backspace control character:
backspace = bs []
  where
    bs ls ('\b':rs) = bs (drop 1 ls) rs
    bs ls (r:rs) = bs (r:ls) rs
    bs ls [] = reverse ls
