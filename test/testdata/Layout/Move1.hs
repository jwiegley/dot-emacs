module Layout.Move1 where

data Located a = L Int a
type Name = String
hsBinds = undefined
divideDecls = undefined
definingDeclsNames = undefined
nub = undefined
definedPNs = undefined
logm = undefined
showGhc = undefined
pnsNeedRenaming = undefined

-- liftToTopLevel' :: ModuleName -- -> (ParseResult,[PosToken]) -> FilePath
--                 -> Located Name
--                 -> RefactGhc [a]
liftToTopLevel' :: Int -> Located Name -> IO [a]
liftToTopLevel' modName pn@(L _ n) = do
  liftToMod
  return []
    where
          {-step1: divide the module's top level declaration list into three parts:
            'parent' is the top level declaration containing the lifted declaration,
            'before' and `after` are those declarations before and after 'parent'.
            step2: get the declarations to be lifted from parent, bind it to liftedDecls 
            step3: remove the lifted declarations from parent and extra arguments may be introduce.
            step4. test whether there are any names need to be renamed.
          -}
       liftToMod :: IO ()
       liftToMod = do
                      -- renamed <- getRefactRenamed
                      let renamed = undefined
                      let declsr = hsBinds renamed
                      let (before,parent,after) = divideDecls declsr pn
                      -- error ("liftToMod:(before,parent,after)=" ++ (showGhc (before,parent,after))) -- ++AZ++
                      {- ++AZ++ : hsBinds does not return class or instance definitions
                      when (isClassDecl $ ghead "liftToMod" parent)
                            $ error "Sorry, the refactorer cannot lift a definition from a class declaration!"
                      when (isInstDecl $ ghead "liftToMod" parent)
                            $ error "Sorry, the refactorer cannot lift a definition from an instance declaration!"
                      -}
                      let liftedDecls = definingDeclsNames [n] parent True True
                          declaredPns = nub $ concatMap definedPNs liftedDecls

                      -- TODO: what about declarations between this
                      -- one and the top level that are used in this one?

                      logm $ "liftToMod:(liftedDecls,declaredPns)=" ++ (showGhc (liftedDecls,declaredPns))
                      -- original : pns<-pnsNeedRenaming inscps mod parent liftedDecls declaredPns
                      -- pns <- pnsNeedRenaming renamed parent liftedDecls declaredPns
                      return ()
