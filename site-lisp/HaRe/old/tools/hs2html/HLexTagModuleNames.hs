{-+
This module exports the lexer postprocessor #convModulesNames#,
which changes the tags of module names and special identifers in imports.
(They are just tagged as #Conid# and #Varid# by the lexer.)

Real module names are retagged as #ModuleName#, while module aliases in
export lists, and after the #as# keyword, are retagged as #ModuleAlias#.

The special identifiers #qualified#, #as# and #hiding# are retagged as
 #Specialid#.

This is a simple hack that assumes that the input is syntactically correct.
-}
module HLexTagModuleNames(convModuleNames) where
import HsTokens

convModuleNames = convh

-- At the beginning of a module
convh = skipspace convh'
convh' (t@(Reservedid,(_,"module")):ts) = t:convm ts 
convh' ts = conv ts -- no module header

-- When "module" has been seen at the beginning of a module:
convm = skipspace convm'
convm' ((Qconid,ps):ts) = (ModuleName,ps):conv ts
convm' ((Conid,ps):ts) = (ModuleName,ps):conv ts
convm' ts = conv ts -- syntactically incorrect module header?!

-- At various positions
conv = skipspace conv'
conv' [] = []
conv' (t@(Reservedid,(_,"import")):ts) = t:convi ts
conv' (t@(Reservedid,(_,"module")):ts) = t:conve ts 
conv' (t:ts) = t:conv ts -- a "normal" token, output unchanged

-- When "module" has been seen in an export list:
conve = skipspace conve'
conve' ((Qconid,ps):ts) = (ModuleAlias,ps):conv ts
conve' ((Conid,ps):ts) = (ModuleAlias,ps):conv ts
conve' ts = conv ts  -- syntactically incorrect module export?!

-- When "import" has been seen:
convi = skipspace convi'
convi' ((Varid,ps@(_,"qualified")):ts) = (Specialid,ps):convi ts
convi' ((Qconid,ps):ts) = (ModuleName,ps):conva ts
convi' ((Conid,ps):ts) = (ModuleName,ps):conva ts
convi' ts = conv ts -- syntactically incorrect import declaration?!

-- When the module name after "import" has been seen:
conva = skipspace conva'
conva' (t2@(Varid,ps@(_,"as")):ts) = (Specialid,ps):conva ts
conva' (t2@(Varid,ps@(_,"hiding")):ts) = (Specialid,ps):conv ts
conva' ((Qconid,ps):ts) = (ModuleAlias,ps):conva ts
conva' ((Conid,ps):ts) = (ModuleAlias,ps):conva ts
conva' ts = conv ts


skipspace f (t@(Whitespace,_):ts) = t:skipspace f ts
skipspace f (t@(NestedComment,_):ts) = t:skipspace f ts
skipspace f (t1@(Commentstart,_):t2@(Comment,_):ts) = t1:t2:skipspace f ts
skipspace f ts = f ts
