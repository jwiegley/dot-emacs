module PfeHtmlCmds where
import Prelude hiding (putStr,putStrLn,writeFile)

import HsName(ModuleName(..))
import PFE_HTML
import PfeParse(moduleArgs,just)

import AbstractIO
import PrettyPrint(pp)
--import CmdLineParser

pfeHtmlCmds =
     [--("html"     , moduleArgs showHtml),
      ("htmlfiles", (moduleArgs htmlfiles,"generate HTML files for modules")),
      ("webpages",  (moduleArgs webpages, "generate web pages for modules"))]

--showHtml = toHtml pfeURL (const putStrLn) . Just

htmlfiles ms = toHtmlFiles htmlDir pfeURL (const id) (just ms)
webpages ms = toHtmlFiles wwwDir wwwURL addHead (just ms)
  where
    addHead m body = unlines head++body
       where
         head = [doctype,"<html><head>", title (pp m),style,
	        "<body>",h1 (pp m)]


wwwURL m = htmlFile m
pfeURL m = "pfe.cgi?"++simpModuleName m

simpModuleName (PlainModule m) = m
simpModuleName (MainModule path) = path

--- Some HTML combinators that belong somewhere else...
title=wrap "title"
h1=wrap "h1"
style=
 "<link rel=stylesheet type=\"text/css\" href=\"haskell.css\" title=Haskell>"
doctype = "<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.01 Transitional//EN\" \"http://www.w3.org/TR/html4/loose.dtd\">"

wrap tag html = start tag++html++end tag
start tag = "<"++tag++">"
end tag = start ('/':tag)
