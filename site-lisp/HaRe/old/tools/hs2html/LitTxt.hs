module LitTxt (toHTML,toHTMLblock) where

import MyDoc
import ParseMyDoc
import MyDoc2HTML
import Text.PrettyPrint(render)
import EnvM (withEnv)


toHTML = render . withEnv html . ppMyDoc . parse
toHTMLblock = render . withEnv htmlblock . ppMyDoc . parse
