module OldBaseSyntax where
import BaseSyntax

-- For backwards compatibility -------------------------------------------------

type E = EI HsName
type HsField e = HsFieldI HsName e

mapE :: (e1 -> e2) ->
        (p1 -> p2) ->
        (d1 -> d2) ->
        (t1 -> t2) ->
        (c1 -> c2) ->
        EI i e1 p1 d1 t1 c1 ->
        EI i e2 p2 d2 t2 c2
mapE = mapEI id 

seqE :: (Monad m,Functor m) =>
        E (m e) (m p) (m ds) (m t) (m c) ->
        m (E e p ds t c)
seqE = seqEI . mapEI return id id id id id


accE :: (e -> b -> b) ->
        (p -> b -> b) ->
        (d -> b -> b) ->
        (t -> b -> b) ->
        (c -> b -> b) ->
        EI i e p d t c ->
        b ->
        b
accE = accEI (const id)
    
type P p = PI HsName p

mapP :: (p1 -> p2) ->
        PI i p1 ->
        PI i p2
mapP = mapPI id

seqP :: (Monad m,Functor m) => PI i (m p) -> m (PI i p)
seqP = seqPI . mapPI return id

type D = DI HsName
type HsMatch = HsMatchI HsName
type HsConDecl = HsConDeclI HsName

mapD :: (e1 -> e2) ->           -- expression recursion function
        (p1 -> p2) ->           -- pattern recursion function
        (d1 -> d2) ->           -- declaration recursion function
        (t1 -> t2) ->           -- type recursion function
        (c1 -> c2) ->           -- context recursion function
        (tp1 -> tp2) ->         -- type pattern recursion function
        DI i e1 p1 d1 t1 c1 tp1 -> -- old declaration structure
        DI i e2 p2 d2 t2 c2 tp2    -- new declaration structure
mapD = mapDI id

type T t = TI HsName t

type HsIdent = HsIdentI HsName
type HsModule = HsModuleI HsName
type HsExportSpec = HsExportSpecI HsName
type HsImportDecl = HsImportDeclI HsName
type HsImportSpec =  HsImportSpecI HsName
