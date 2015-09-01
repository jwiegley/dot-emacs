" Vim/GVim interface to Haskell refactorer
" (generated automatically - manual edits may be lost)

" use :source <file> to load this into vim/gvim


let g:haskell_refac_version = "HaRe 0.6.0.1"

if !exists("g:haskell_refac_refactorer")
	let g:haskell_refac_refactorer = "hare"
endif

if !exists("g:haskell_refac_refactorer_client")
	let g:haskell_refac_refactorer_client = "hare-client"
endif

if !exists("g:haskell_refac_chasePaths")
	let g:haskell_refac_chasePaths = getcwd() . " HaskellLibraries"
endif

if !exists("g:haskell_refac_showWindow")
	let g:haskell_refac_showWindow = 1
endif

function! Myinput(p)
     if version >=602
        call inputsave()
     endif
        let x=input(a:p)
     if version >=602
        call inputrestore()
     endif
        return x
endfunction


function! Haskell_refac_new()
	let fileName0 = expand("%:p")

call Haskell_refac_client_cmd(" new"." ".fileName0)
endfunction


function! Haskell_refac_add()
	let fileName0 = expand("%:p")

call Haskell_refac_client_cmd(" add"." ".fileName0)
endfunction


function! Haskell_refac_chase()

call Haskell_refac_client_cmd(" chase"." ". g:haskell_refac_chasePaths)
endfunction


function! Haskell_refac_files()

call Haskell_refac_client_cmd(" files")
endfunction



function! Haskell_refac_rename()
	let fileName0 = expand("%:p")
	let name1 = Myinput("New name? ")
	let line2 = line(".")
	let column2 = col(".")

call Haskell_refac_client_cmd(" rename"." ".fileName0." ".name1." ".line2." ".column2)
endfunction


function! Haskell_refac_liftToTopLevel()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" liftToTopLevel"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_liftOneLevel()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" liftOneLevel"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_demote()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" demote"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_refacTypeSig()
	let fileName0 = expand("%:p")

call Haskell_refac_client_cmd(" refacTypeSig"." ".fileName0)
endfunction


function! Haskell_refac_parseAnswers()
	let fileName0 = expand("%:p")

call Haskell_refac_client_cmd(" parseAnswers"." ".fileName0)
endfunction


function! Haskell_refac_letToWhere()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" letToWhere"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_whereToLet()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" whereToLet"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_introPattern()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" introPattern"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_introCase()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" introCase"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_foldPattern()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Name of pattern variable: ")
	let start2 = line("'<")." ".col("'<")
	let end2 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" foldPattern"." ".fileName0." ".name1." ".start2." ".end2)
endfunction



function! Haskell_refac_refacRedunDec()
	let fileName0 = expand("%:p")
	let start1 = line("'<")." ".col("'<")
	let end1 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" refacRedunDec"." ".fileName0." ".start1." ".end1)
endfunction


function! Haskell_refac_refacSlicing()
	let fileName0 = expand("%:p")
	let start1 = line("'<")." ".col("'<")
	let end1 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" refacSlicing"." ".fileName0." ".start1." ".end1)
endfunction


function! Haskell_refac_refacSlicTuple()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")
	let name2 = Myinput("Elements to slice: (A for all; (x,_x,_) for some): ")

call Haskell_refac_client_cmd(" refacSlicTuple"." ".fileName0." ".line1." ".column1." ".name2)
endfunction


function! Haskell_refac_refacMerge()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Name for new definition: ")

call Haskell_refac_client_cmd(" refacMerge"." ".fileName0." ".name1)
endfunction


function! Haskell_refac_refacCacheMerge()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" refacCacheMerge"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_refacInstantiate()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")
	let name2 = Myinput("patterns: ")

call Haskell_refac_client_cmd(" refacInstantiate"." ".fileName0." ".line1." ".column1." ".name2)
endfunction



function! Haskell_refac_unfoldDef()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" unfoldDef"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_subFunctionDef()
	let fileName0 = expand("%:p")
	let start1 = line("'<")." ".col("'<")
	let end1 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" subFunctionDef"." ".fileName0." ".start1." ".end1)
endfunction


function! Haskell_refac_genFold()
	let fileName0 = expand("%:p")
	let start1 = line("'<")." ".col("'<")
	let end1 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" genFold"." ".fileName0." ".start1." ".end1)
endfunction


function! Haskell_refac_genFoldCache()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" genFoldCache"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_refacAsPatterns()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Name for Pattern: ")
	let start2 = line("'<")." ".col("'<")
	let end2 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" refacAsPatterns"." ".fileName0." ".name1." ".start2." ".end2)
endfunction


function! Haskell_refac_refacUnfoldAsPatterns()
	let fileName0 = expand("%:p")
	let start1 = line("'<")." ".col("'<")
	let end1 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" refacUnfoldAsPatterns"." ".fileName0." ".start1." ".end1)
endfunction


function! Haskell_refac_simplifyExpr()
	let fileName0 = expand("%:p")
	let start1 = line("'<")." ".col("'<")
	let end1 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" simplifyExpr"." ".fileName0." ".start1." ".end1)
endfunction



function! Haskell_refac_introNewDef()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Name for new definition? ")
	let start2 = line("'<")." ".col("'<")
	let end2 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" introNewDef"." ".fileName0." ".name1." ".start2." ".end2)
endfunction


function! Haskell_refac_generaliseDef()
	let fileName0 = expand("%:p")
	let name1 = Myinput("name of new parameter? ")
	let start2 = line("'<")." ".col("'<")
	let end2 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" generaliseDef"." ".fileName0." ".name1." ".start2." ".end2)
endfunction


function! Haskell_refac_removeDef()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" removeDef"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_duplicateDef()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Name for duplicate? ")
	let line2 = line(".")
	let column2 = col(".")

call Haskell_refac_client_cmd(" duplicateDef"." ".fileName0." ".name1." ".line2." ".column2)
endfunction


function! Haskell_refac_addOneParameter()
	let fileName0 = expand("%:p")
	let name1 = Myinput("name of new parameter? ")
	let line2 = line(".")
	let column2 = col(".")

call Haskell_refac_client_cmd(" addOneParameter"." ".fileName0." ".name1." ".line2." ".column2)
endfunction


function! Haskell_refac_rmOneParameter()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" rmOneParameter"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_moveDefBtwMod()
	let fileName0 = expand("%:p")
	let name1 = Myinput("name of the destination module? ")
	let line2 = line(".")
	let column2 = col(".")

call Haskell_refac_client_cmd(" moveDefBtwMod"." ".fileName0." ".name1." ".line2." ".column2)
endfunction


function! Haskell_refac_guardToIte()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" guardToIte"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_deforest()
	let fileName0 = expand("%:p")

call Haskell_refac_client_cmd(" deforest"." ".fileName0)
endfunction



function! Haskell_refac_cleanImports()
	let fileName0 = expand("%:p")

call Haskell_refac_client_cmd(" cleanImports"." ".fileName0)
endfunction


function! Haskell_refac_mkImpExplicit()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" mkImpExplicit"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_addToExport()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" addToExport"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_rmFromExport()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" rmFromExport"." ".fileName0." ".line1." ".column1)
endfunction



function! Haskell_refac_addFieldLabels()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" addFieldLabels"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_addDiscriminators()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" addDiscriminators"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_addConstructors()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" addConstructors"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_elimNestedPatterns()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" elimNestedPatterns"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_elimPatterns()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" elimPatterns"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_createADTMod()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" createADTMod"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_fromAlgebraicToADT()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" fromAlgebraicToADT"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_refacAddCon()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Enter text for constructor and parameters: ")
	let line2 = line(".")
	let column2 = col(".")

call Haskell_refac_client_cmd(" refacAddCon"." ".fileName0." ".name1." ".line2." ".column2)
endfunction


function! Haskell_refac_refacRmCon()
	let fileName0 = expand("%:p")
	let line1 = line(".")
	let column1 = col(".")

call Haskell_refac_client_cmd(" refacRmCon"." ".fileName0." ".line1." ".column1)
endfunction


function! Haskell_refac_refacRemoveField()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Enter position of field to be removed: ")
	let line2 = line(".")
	let column2 = col(".")

call Haskell_refac_client_cmd(" refacRemoveField"." ".fileName0." ".name1." ".line2." ".column2)
endfunction


function! Haskell_refac_refacAddField()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Type of Field : ")
	let line2 = line(".")
	let column2 = col(".")

call Haskell_refac_client_cmd(" refacAddField"." ".fileName0." ".name1." ".line2." ".column2)
endfunction



function! Haskell_refac_duplicateCode()
	let fileName0 = expand("%:p")
	let name1 = Myinput("Clone Token Size: ")

call Haskell_refac_client_cmd(" duplicateCode"." ".fileName0." ".name1)
endfunction


function! Haskell_refac_refacDupTrans()
	let fileName0 = expand("%:p")
	let start1 = line("'<")." ".col("'<")
	let end1 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" refacDupTrans"." ".fileName0." ".start1." ".end1)
endfunction


function! Haskell_refac_refacIdentify()
	let fileName0 = expand("%:p")
	let start1 = line("'<")." ".col("'<")
	let end1 = line("'>")." ".col("'>")
call Haskell_refac_client_cmd(" refacIdentify"." ".fileName0." ".start1." ".end1)
endfunction



function! Haskell_refac_undo()

call Haskell_refac_client_cmd(" undo")
endfunction


command! New :echo Haskell_refac_new()
command! Add :echo Haskell_refac_add()
command! Chase :echo Haskell_refac_chase()
command! Files :echo Haskell_refac_files()

command! Rename :echo Haskell_refac_rename()
command! LiftToTopLevel :echo Haskell_refac_liftToTopLevel()
command! LiftOneLevel :echo Haskell_refac_liftOneLevel()
command! Demote :echo Haskell_refac_demote()
command! RefacTypeSig :echo Haskell_refac_refacTypeSig()
command! ParseAnswers :echo Haskell_refac_parseAnswers()
command! LetToWhere :echo Haskell_refac_letToWhere()
command! WhereToLet :echo Haskell_refac_whereToLet()
command! IntroPattern :echo Haskell_refac_introPattern()
command! IntroCase :echo Haskell_refac_introCase()
command! FoldPattern :echo Haskell_refac_foldPattern()

command! RefacRedunDec :echo Haskell_refac_refacRedunDec()
command! RefacSlicing :echo Haskell_refac_refacSlicing()
command! RefacSlicTuple :echo Haskell_refac_refacSlicTuple()
command! RefacMerge :echo Haskell_refac_refacMerge()
command! RefacCacheMerge :echo Haskell_refac_refacCacheMerge()
command! RefacInstantiate :echo Haskell_refac_refacInstantiate()

command! UnfoldDef :echo Haskell_refac_unfoldDef()
command! SubFunctionDef :echo Haskell_refac_subFunctionDef()
command! GenFold :echo Haskell_refac_genFold()
command! GenFoldCache :echo Haskell_refac_genFoldCache()
command! RefacAsPatterns :echo Haskell_refac_refacAsPatterns()
command! RefacUnfoldAsPatterns :echo Haskell_refac_refacUnfoldAsPatterns()
command! SimplifyExpr :echo Haskell_refac_simplifyExpr()

command! IntroNewDef :echo Haskell_refac_introNewDef()
command! GeneraliseDef :echo Haskell_refac_generaliseDef()
command! RemoveDef :echo Haskell_refac_removeDef()
command! DuplicateDef :echo Haskell_refac_duplicateDef()
command! AddOneParameter :echo Haskell_refac_addOneParameter()
command! RmOneParameter :echo Haskell_refac_rmOneParameter()
command! MoveDefBtwMod :echo Haskell_refac_moveDefBtwMod()
command! GuardToIte :echo Haskell_refac_guardToIte()
command! Deforest :echo Haskell_refac_deforest()

command! CleanImports :echo Haskell_refac_cleanImports()
command! MkImpExplicit :echo Haskell_refac_mkImpExplicit()
command! AddToExport :echo Haskell_refac_addToExport()
command! RmFromExport :echo Haskell_refac_rmFromExport()

command! AddFieldLabels :echo Haskell_refac_addFieldLabels()
command! AddDiscriminators :echo Haskell_refac_addDiscriminators()
command! AddConstructors :echo Haskell_refac_addConstructors()
command! ElimNestedPatterns :echo Haskell_refac_elimNestedPatterns()
command! ElimPatterns :echo Haskell_refac_elimPatterns()
command! CreateADTMod :echo Haskell_refac_createADTMod()
command! FromAlgebraicToADT :echo Haskell_refac_fromAlgebraicToADT()
command! RefacAddCon :echo Haskell_refac_refacAddCon()
command! RefacRmCon :echo Haskell_refac_refacRmCon()
command! RefacRemoveField :echo Haskell_refac_refacRemoveField()
command! RefacAddField :echo Haskell_refac_refacAddField()

command! DuplicateCode :echo Haskell_refac_duplicateCode()
command! RefacDupTrans :echo Haskell_refac_refacDupTrans()
command! RefacIdentify :echo Haskell_refac_refacIdentify()

command! Undo :echo Haskell_refac_undo()

" --------------------------------------------------- menu
if has("menu")
	if exists("b:haskell_refac_menu")
		aunmenu Haskell(Refac)
	endif

	200amenu Haskell(Refac).-Change-      :

	amenu Haskell(Refac).Projects.New\ project :New<cr>
	tmenu Haskell(Refac).Projects.New\ project <fileName> Start new project with current file
	amenu Haskell(Refac).Projects.Add\ file :Add<cr>
	tmenu Haskell(Refac).Projects.Add\ file <fileName> Add current file to project
	amenu Haskell(Refac).Projects.Chase\ imports :Chase<cr>
	tmenu Haskell(Refac).Projects.Chase\ imports <option (chasePaths)> Chase to add missing files to project
	amenu Haskell(Refac).Projects.List\ files :Files<cr>
	tmenu Haskell(Refac).Projects.List\ files List files in project

	amenu Haskell(Refac).Names/Scopes.Rename :Rename<cr>
	tmenu Haskell(Refac).Names/Scopes.Rename <fileName> <name (New name? )> <line> <column> Rename a variable name
	amenu Haskell(Refac).Names/Scopes.Lift\ def\ to\ top\ level :LiftToTopLevel<cr>
	tmenu Haskell(Refac).Names/Scopes.Lift\ def\ to\ top\ level <fileName> <line> <column> Lift a local declaration to top level
	amenu Haskell(Refac).Names/Scopes.Lift\ def\ one\ level :LiftOneLevel<cr>
	tmenu Haskell(Refac).Names/Scopes.Lift\ def\ one\ level <fileName> <line> <column> Lift a local declaration one level up
	amenu Haskell(Refac).Names/Scopes.Demote\ def :Demote<cr>
	tmenu Haskell(Refac).Names/Scopes.Demote\ def <fileName> <line> <column> Demote a declaration to where it is used
	amenu Haskell(Refac).Names/Scopes.Create\ Type\ Signatures :RefacTypeSig<cr>
	tmenu Haskell(Refac).Names/Scopes.Create\ Type\ Signatures <fileName> Generates type signatures for top-level definitions using GHC.
	amenu Haskell(Refac).Names/Scopes.ReadFile :ParseAnswers<cr>
	tmenu Haskell(Refac).Names/Scopes.ReadFile <fileName> Read in an answer
	amenu Haskell(Refac).Names/Scopes.Convert\ Let\ to\ Where :LetToWhere<cr>
	tmenu Haskell(Refac).Names/Scopes.Convert\ Let\ to\ Where <fileName> <line> <column> Converts a let expression into a where equation.
	amenu Haskell(Refac).Names/Scopes.Convert\ Where\ to\ Let :WhereToLet<cr>
	tmenu Haskell(Refac).Names/Scopes.Convert\ Where\ to\ Let <fileName> <line> <column> Converts a where equation into a let expression
	amenu Haskell(Refac).Names/Scopes.Introduce\ patterns\ over\ an\ argument\ position :IntroPattern<cr>
	tmenu Haskell(Refac).Names/Scopes.Introduce\ patterns\ over\ an\ argument\ position <fileName> <line> <column> Replace variable with exhaustive set of patterns
	amenu Haskell(Refac).Names/Scopes.Introduce\ case\ analysis :IntroCase<cr>
	tmenu Haskell(Refac).Names/Scopes.Introduce\ case\ analysis <fileName> <line> <column> Introduction of cases analysis via a pattern variable
	amenu Haskell(Refac).Names/Scopes.Fold\ term\ against\ pattern\ variable :FoldPattern<cr>
	tmenu Haskell(Refac).Names/Scopes.Fold\ term\ against\ pattern\ variable <fileName> <name (Name of pattern variable: )> <line> <column> <line> <column> Folds a sub-expression against a pattern variable

	amenu Haskell(Refac).Slicing.Remove\ redundant\ declarations :RefacRedunDec<cr>
	tmenu Haskell(Refac).Slicing.Remove\ redundant\ declarations <fileName> <line> <column> <line> <column> Removes redundant declarations in a where clause or expression
	amenu Haskell(Refac).Slicing.Slicing\ based\ on\ a\ subexpression :RefacSlicing<cr>
	tmenu Haskell(Refac).Slicing.Slicing\ based\ on\ a\ subexpression <fileName> <line> <column> <line> <column> Slices a subexpression
	amenu Haskell(Refac).Slicing.Slicing\ a\ tuple :RefacSlicTuple<cr>
	tmenu Haskell(Refac).Slicing.Slicing\ a\ tuple <fileName> <line> <column> <name (Elements to slice: (A for all; (x,_x,_) for some): )> slices a definition which returns a tuple
	amenu Haskell(Refac).Slicing.Merge\ definitions :RefacMerge<cr>
	tmenu Haskell(Refac).Slicing.Merge\ definitions <fileName> <name (Name for new definition: )> Merges multiple definitions to form one single definition.
	amenu Haskell(Refac).Slicing.Add\ definition\ for\ merge :RefacCacheMerge<cr>
	tmenu Haskell(Refac).Slicing.Add\ definition\ for\ merge <fileName> <line> <column> Adds a definition to the cache for merging.
	amenu Haskell(Refac).Slicing.Instantiate\ a\ general\ pattern :RefacInstantiate<cr>
	tmenu Haskell(Refac).Slicing.Instantiate\ a\ general\ pattern <fileName> <line> <column> <name (patterns: )> Instantiates patterns in a generalised function clause

	amenu Haskell(Refac).Fold/Unfold.Unfold\ def :UnfoldDef<cr>
	tmenu Haskell(Refac).Fold/Unfold.Unfold\ def <fileName> <line> <column> Unfold a definition
	amenu Haskell(Refac).Fold/Unfold.Fold\ Definition :SubFunctionDef<cr>
	tmenu Haskell(Refac).Fold/Unfold.Fold\ Definition <fileName> <line> <column> <line> <column> Folds against a definition
	amenu Haskell(Refac).Fold/Unfold.Generative\ Fold\ of\ Definition :GenFold<cr>
	tmenu Haskell(Refac).Fold/Unfold.Generative\ Fold\ of\ Definition <fileName> <line> <column> <line> <column> Replace an instance of the right hand side of a definition by the corresponding left hand side, creating a new recursive definition.
	amenu Haskell(Refac).Fold/Unfold.Select\ an\ equation\ for\ generative\ fold :GenFoldCache<cr>
	tmenu Haskell(Refac).Fold/Unfold.Select\ an\ equation\ for\ generative\ fold <fileName> <line> <column> Places an selcted equation into a cache for use by generative fold.
	amenu Haskell(Refac).Fold/Unfold.Convert\ pattern\ to\ use\ an\ as\ pattern :RefacAsPatterns<cr>
	tmenu Haskell(Refac).Fold/Unfold.Convert\ pattern\ to\ use\ an\ as\ pattern <fileName> <name (Name for Pattern: )> <line> <column> <line> <column> Converts all appropriate patterns to use an as binding.
	amenu Haskell(Refac).Fold/Unfold.Unfold\ references\ to\ AS\ patterns :RefacUnfoldAsPatterns<cr>
	tmenu Haskell(Refac).Fold/Unfold.Unfold\ references\ to\ AS\ patterns <fileName> <line> <column> <line> <column> Converts all references to an as pattern to the actuall pattern.
	amenu Haskell(Refac).Fold/Unfold.Simplify\ Expression\ via\ Symbolic\ Evalutaion :SimplifyExpr<cr>
	tmenu Haskell(Refac).Fold/Unfold.Simplify\ Expression\ via\ Symbolic\ Evalutaion <fileName> <line> <column> <line> <column> Attempts to simplify a case expression.

	amenu Haskell(Refac).Definitions.Introduce\ new\ def :IntroNewDef<cr>
	tmenu Haskell(Refac).Definitions.Introduce\ new\ def <fileName> <name (Name for new definition? )> <line> <column> <line> <column> Introduce a new definition
	amenu Haskell(Refac).Definitions.Generalise\ def :GeneraliseDef<cr>
	tmenu Haskell(Refac).Definitions.Generalise\ def <fileName> <name (name of new parameter? )> <line> <column> <line> <column> Generalise a definition
	amenu Haskell(Refac).Definitions.Remove\ def :RemoveDef<cr>
	tmenu Haskell(Refac).Definitions.Remove\ def <fileName> <line> <column> Remove a definition if it is no used
	amenu Haskell(Refac).Definitions.Duplicate\ def :DuplicateDef<cr>
	tmenu Haskell(Refac).Definitions.Duplicate\ def <fileName> <name (Name for duplicate? )> <line> <column> Duplicate a definition at the same level
	amenu Haskell(Refac).Definitions.Add\ one\ parameter :AddOneParameter<cr>
	tmenu Haskell(Refac).Definitions.Add\ one\ parameter <fileName> <name (name of new parameter? )> <line> <column> Add parameter (default undefined)
	amenu Haskell(Refac).Definitions.Rm\ one\ parameter :RmOneParameter<cr>
	tmenu Haskell(Refac).Definitions.Rm\ one\ parameter <fileName> <line> <column> Remove unused parameter
	amenu Haskell(Refac).Definitions.Move\ def\ to\ another\ module :MoveDefBtwMod<cr>
	tmenu Haskell(Refac).Definitions.Move\ def\ to\ another\ module <fileName> <name (name of the destination module? )> <line> <column> Move a definition from one module to another module
	amenu Haskell(Refac).Definitions.Converts\ guards\ to\ an\ if\ then\ else :GuardToIte<cr>
	tmenu Haskell(Refac).Definitions.Converts\ guards\ to\ an\ if\ then\ else <fileName> <line> <column> Converts guards to an if then else
	amenu Haskell(Refac).Definitions.Shortcut\ Deforestration :Deforest<cr>
	tmenu Haskell(Refac).Definitions.Shortcut\ Deforestration <fileName> A (partial) implementation of the warm fusion algorithm

	amenu Haskell(Refac).Import/Export.Clean\ imports :CleanImports<cr>
	tmenu Haskell(Refac).Import/Export.Clean\ imports <fileName> Tidy up the import list of the current module
	amenu Haskell(Refac).Import/Export.Make\ import\ explicit :MkImpExplicit<cr>
	tmenu Haskell(Refac).Import/Export.Make\ import\ explicit <fileName> <line> <column> Make the used entities explicit
	amenu Haskell(Refac).Import/Export.Add\ to\ export :AddToExport<cr>
	tmenu Haskell(Refac).Import/Export.Add\ to\ export <fileName> <line> <column> Add an identifier to the export list
	amenu Haskell(Refac).Import/Export.Remove\ from\ export :RmFromExport<cr>
	tmenu Haskell(Refac).Import/Export.Remove\ from\ export <fileName> <line> <column> Remove an identifier from the export list

	amenu Haskell(Refac).Data\ types.Add\ field\ labels :AddFieldLabels<cr>
	tmenu Haskell(Refac).Data\ types.Add\ field\ labels <fileName> <line> <column> Add field labels to a data type declaration
	amenu Haskell(Refac).Data\ types.Add\ discriminators :AddDiscriminators<cr>
	tmenu Haskell(Refac).Data\ types.Add\ discriminators <fileName> <line> <column> Add discriminator functions to a data type declaration
	amenu Haskell(Refac).Data\ types.Add\ constructors :AddConstructors<cr>
	tmenu Haskell(Refac).Data\ types.Add\ constructors <fileName> <line> <column> Add constructor functions to a data type declaration
	amenu Haskell(Refac).Data\ types.Eliminate\ nested\ patterns :ElimNestedPatterns<cr>
	tmenu Haskell(Refac).Data\ types.Eliminate\ nested\ patterns <fileName> <line> <column> Eliminate nested pattern matchings
	amenu Haskell(Refac).Data\ types.Eliminate\ patterns :ElimPatterns<cr>
	tmenu Haskell(Refac).Data\ types.Eliminate\ patterns <fileName> <line> <column> Eliminate pattern matchings
	amenu Haskell(Refac).Data\ types.Create\ an\ ADT\ module :CreateADTMod<cr>
	tmenu Haskell(Refac).Data\ types.Create\ an\ ADT\ module <fileName> <line> <column> Create an new ADT module
	amenu Haskell(Refac).Data\ types.From\ concrete\ to\ abstract\ data\ type :FromAlgebraicToADT<cr>
	tmenu Haskell(Refac).Data\ types.From\ concrete\ to\ abstract\ data\ type <fileName> <line> <column> Transforms an algebraic data type to an ADT
	amenu Haskell(Refac).Data\ types.Add\ a\ new\ constructor\ to\ a\ data\ type :RefacAddCon<cr>
	tmenu Haskell(Refac).Data\ types.Add\ a\ new\ constructor\ to\ a\ data\ type <fileName> <name (Enter text for constructor and parameters: )> <line> <column> Adds a new constructor to a data type
	amenu Haskell(Refac).Data\ types.Remove\ a\ constructor\ from\ a\ data\ type :RefacRmCon<cr>
	tmenu Haskell(Refac).Data\ types.Remove\ a\ constructor\ from\ a\ data\ type <fileName> <line> <column> Removes constructor from a data type
	amenu Haskell(Refac).Data\ types.Remove\ a\ field\ from\ a\ data\ type :RefacRemoveField<cr>
	tmenu Haskell(Refac).Data\ types.Remove\ a\ field\ from\ a\ data\ type <fileName> <name (Enter position of field to be removed: )> <line> <column> Removes a field from a data type
	amenu Haskell(Refac).Data\ types.Add\ a\ field\ to\ a\ data\ type :RefacAddField<cr>
	tmenu Haskell(Refac).Data\ types.Add\ a\ field\ to\ a\ data\ type <fileName> <name (Type of Field : )> <line> <column> Adds a field to a data type

	amenu Haskell(Refac).Duplicate\ Code.Duplicate\ Code\ Analysis :DuplicateCode<cr>
	tmenu Haskell(Refac).Duplicate\ Code.Duplicate\ Code\ Analysis <fileName> <name (Clone Token Size: )> Analysis a project for code duplication.
	amenu Haskell(Refac).Duplicate\ Code.Transform\ Duplicate\ Code :RefacDupTrans<cr>
	tmenu Haskell(Refac).Duplicate\ Code.Transform\ Duplicate\ Code <fileName> <line> <column> <line> <column> Transforms duplicate code
	amenu Haskell(Refac).Duplicate\ Code.Identify\ Class :RefacIdentify<cr>
	tmenu Haskell(Refac).Duplicate\ Code.Identify\ Class <fileName> <line> <column> <line> <column> identifies a clone class

	amenu Haskell(Refac).Undo :Undo<cr>
	tmenu Haskell(Refac).Undo One step back in refactorer history

	amenu Haskell(Refac).-Custom- :
	amenu Haskell(Refac).version :echo g:haskell_refac_version<cr>
	amenu Haskell(Refac).customize :call Customize()<cr>
	tmenu Haskell(Refac).customize customize paths and options
	amenu Haskell(Refac).start :RefacStart<cr>
	tmenu Haskell(Refac).start start refactorer
	amenu Haskell(Refac).stop :RefacStop<cr>
	tmenu Haskell(Refac).stop stop refactorer

	amenu disable Haskell(Refac).*
	amenu enable Haskell(Refac).version
	amenu enable Haskell(Refac).customize
	amenu enable Haskell(Refac).start


	let b:haskell_refac_menu = "yes"
endif

function! Customize()
  let current=bufname("%")
  if bufexists("customize")
      set switchbuf+=useopen
      sbuf ^customize$
    else
      new customize
  endif
  set buftype=nofile
  set bufhidden=delete
  set noswapfile
  execute "%d"
  set tw=0
  map <buffer> _ok :exe getline(3)<cr>:exe getline(4)<cr>:exe getline(5)<cr>:q<cr>
  call append(0,"let g:haskell_refac_showWindow=".g:haskell_refac_showWindow)
  call append(0,"let g:haskell_refac_chasePaths='".g:haskell_refac_chasePaths."'")
  call append(0,"let g:haskell_refac_refactorer='".g:haskell_refac_refactorer."'")
  call append(0,"\" (you might want to add these lines to your vimrc)")
  call append(0,"\" To customize, edit values, then type \"_ok\"")
endfunction

if has("win32")
  function! Haskell_refac_start()
    let @r=''
    redir @r
    silent execute ":!start /min ".g:haskell_refac_refactorer." vim ".escape($VIMRUNTIME,' ')."\\".v:progname." ".v:servername
    au VimLeave * call Haskell_refac_client_cmd('stop')
    redir END
    call Haskell_refac_msg(0,@r)
  
    amenu enable Haskell(Refac).*
    amenu disable Haskell(Refac).start
    amenu disable Haskell(Refac).customize
  endfunction

  function! Haskell_refac_client_cmd(cmd)
    let @r=''
    redir @r
    "to rescue users of behave mswin
    normal gV
    silent execute ":!start /min ".g:haskell_refac_refactorer_client." ".a:cmd
    redir END
    call Haskell_refac_msg(0,@r)
  endfunction
else
  if executable(v:progname)
    function! Haskell_refac_start()
      let @r=''
      redir @r
      silent execute ":!".g:haskell_refac_refactorer." vim ".v:progname." ".v:servername." >log.txt 2>&1 &"
      au VimLeave * call Haskell_refac_client_cmd('stop')
      redir END
      call Haskell_refac_msg(0,@r)
    
      amenu enable Haskell(Refac).*
      amenu disable Haskell(Refac).start
      amenu disable Haskell(Refac).customize
    endfunction

    function! Haskell_refac_client_cmd(cmd)
      let @r=''
      redir @r
      silent execute ":!".g:haskell_refac_refactorer_client." ".a:cmd
      redir END
      call Haskell_refac_msg(0,@r)
    endfunction
  else
  echoerr "cannot find path to executable"
  endif
endif

function! Haskell_refac_stop()
  call Haskell_refac_client_cmd('stop')

  amenu disable Haskell(Refac).*
  amenu enable Haskell(Refac).start
  amenu enable Haskell(Refac).version
  amenu enable Haskell(Refac).customize
endfunction

command! RefacStart :call Haskell_refac_start()
command! RefacStop :call Haskell_refac_stop()

function! Haskell_refac_modified(f)
    set switchbuf+=useopen
    if bufexists(a:f)
      execute ":sbuf ".a:f
      edit
    else
      call Haskell_refac_msg(1,"modified file: ".a:f."  (not currently opened)")
    endif
endfunction

function! Haskell_refac_msg(dialog,msg)
  let visible = bufwinnr('^refac$')
  if bufexists('^refac$')
    set switchbuf+=useopen
    sbuf ^refac$
    call append(line('$'),a:msg)
    if visible==-1 
      hide 
    else 
      sbuf % 
    endif
  else
    hide new refac
    set bufhidden=hide
    set buftype=nofile
    set noswapfile
    call append(line('$'),a:msg)
    hide
  endif
 if a:dialog
   call confirm(a:msg)
 endif
endfunction

"--------------------- HaRe selection

function! Hare_withSelection(existsCmd,emptyCmd)
  let visible = bufwinnr('^hare-selection$')
  if bufexists('hare-selection')
    set switchbuf+=useopen
    sbuf ^hare-selection$

    exe a:existsCmd

    if visible==-1 
      hide 
    else 
      sbuf % 
    endif
  else

    exe a:emptyCmd
    
  endif
endfunction

function! Hare_createSelection(entry)
  hide new hare-selection
  set bufhidden=hide
  set buftype=nofile
  set noswapfile
  map <buffer> <cr> :call Hare_sel_goto(0) <cr>
  call setline(1,a:entry)
  hide
endfunction

function! Hare_sel_clear()
  call Hare_withSelection(":bunload! hare-selection",":call confirm('empty selection')")
endfunction

function! Hare_sel_add_aux(entry)
  if nextnonblank(1)
    call append(line('$'),a:entry)
  else
    call setline(1,a:entry)
  endif
endfunction

function! Hare_sel_add()
  let l=line(".")
  let c=col(".")
  let entry="\"" . bufname("") . "\" " . l . " " . c . " : " . getline(l)
  let entry='"'.escape(entry,'"').'"'
  call Hare_withSelection(":call Hare_sel_add_aux(".entry.")",":call Hare_createSelection(".entry.")")
endfunction

function! Hare_sel_delete()
  let l=line(".")
  let c=col(".")
  let prefix="\"" . bufname("") . "\" " . l . " " . c . " : "
  call Hare_withSelection(":g/^".prefix."/d",":call confirm('empty selection')")
endfunction

function! Hare_sel_display()
  if bufexists('hare-selection')
    set switchbuf+=useopen
    sbuf ^hare-selection$
    normal J
    resize 5
  else
    call confirm('empty selection')
  endif
endfunction

function! Hare_sel_goto(motion)
  let visible = bufwinnr('^hare-selection$')
  if bufexists('hare-selection')
    set switchbuf+=useopen
    sbuf ^hare-selection$
    call cursor(line(".")+a:motion,0)
    let l=getline(".")
    let buffer=matchstr(l,"\"[^\"]*\" ")
    let buffer=strpart(buffer,1,strlen(buffer)-3)
    let i=matchend(l,"\"[^\"]*\" ")
    let l=strpart(l,i)
    let lnr=matchstr(l,"[0-9][0-9]*")
    let j=stridx(l," ")
    let cnr=matchstr(l,"[0-9][0-9]*",j)
    if visible==-1 
      hide 
    else 
      sbuf % 
    endif
    "call confirm(buffer ." ".lnr." ".cnr)
    exe ":sbuf " . buffer
    call cursor(lnr,cnr)
  else
    call confirm('empty selection')
  endif
endfunction

amenu Haskell(Refac).Selection.Clear\ selection :call Hare_sel_clear()<cr>
tmenu Haskell(Refac).Selection.Clear\ selection clear selection
amenu Haskell(Refac).Selection.Add\ to\ selection :call Hare_sel_add()<cr>
tmenu Haskell(Refac).Selection.Add\ to\ selection add current position to selection
amenu Haskell(Refac).Selection.Delete\ from\ selection :call Hare_sel_delete()<cr>
tmenu Haskell(Refac).Selection.Delete\ from\ selection delete current position from selection
amenu Haskell(Refac).Selection.Show\ selection :call Hare_sel_display()<cr>
tmenu Haskell(Refac).Selection.Show\ selection show selection
amenu Haskell(Refac).Selection.Visit\ next\ entry :call Hare_sel_goto(1)<cr>
tmenu Haskell(Refac).Selection.Visit\ next\ entry visit next entry
amenu Haskell(Refac).Selection.Visit\ current\ entry :call Hare_sel_goto(0)<cr>
tmenu Haskell(Refac).Selection.Visit\ current\ entry visit current entry
amenu Haskell(Refac).Selection.Visit\ previous\ entry :call Hare_sel_goto(-1)<cr>
tmenu Haskell(Refac).Selection.Visit\ previous\ entry visit previous entry


