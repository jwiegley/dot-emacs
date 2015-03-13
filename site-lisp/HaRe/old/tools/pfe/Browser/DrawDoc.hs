module DrawDoc(drawDoc,toDrawing) where
import FudDraw
import PrettyDoc
import PrettyEnv
import MUtils
import PfeBrowserColors

drawDoc = toDrawing . runEnv defaultMode

toDrawing = conv . trim
  where
    conv d =
      case d of
	Empty -> blankD 0
	Char c -> g c
	Text s -> g s
	Attr t d -> fgD (defaultColor t) (conv d) -- a quick hack
	Nest n d -> indentD (n,conv d) -- hmm
	Group l ds -> group l (map conv' ds)
	  where
	    group l ds =
	      case l of
		Horiz Cat -> hboxcaD' 0 (map snd ds)
		Horiz Sep -> hboxcaD' sep (map snd ds)
		Vert -> vboxlD' 0 (map indentD ds)
		HorizOrVert Cat -> catD ds
		HorizOrVert Sep -> sepD ds
		Fill Cat -> fcatD ds
		Fill Sep -> fsepD ds

    conv' = apSnd conv . splitNest

    noNest = snd . splitNest

    splitNest = splitNest' 0
    splitNest' n (Nest n' d) = splitNest' (n+n') d
    splitNest' n d = (n,d)

    trim d =
      case d of
	Nest n d -> case trim d of
		      Empty -> Empty
		      d -> Nest n d
	Group l ds -> case [ d | d<-map trim ds,nonEmpty d] of
		        [] -> Empty
			[d] -> d
			ds -> Group l ds
	Attr a d -> Attr a (trim d)
        _ -> d

catD = wideOrTallD 0
sepD = wideOrTallD sep

fcatD = paraD 0
fsepD = paraD sep

--paraD = hboxcaD'
--paraD = wideOrTallD
paraD sep = placedD (paragraphP' (Point sep 0)) . boxD . map snd

--rframeD = frameD "red"
--bframeD = frameD "blue"
--frameD c d = stackD [fgD c (g frame),padD 2 d]
