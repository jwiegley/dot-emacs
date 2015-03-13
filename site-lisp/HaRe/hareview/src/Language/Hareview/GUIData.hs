{-# LANGUAGE ExistentialQuantification #-}
{- contains the GUI data types
 -
 -}
module Language.Hareview.GUIData where

import Data.Tree (Tree(..))
import Data.IORef

-- gtksourceview
import Graphics.UI.Gtk hiding (Language,get)
import Graphics.UI.Gtk.SourceView (SourceBuffer) 

import Language.Hareview.Language (Language)

type AstAction a = IORef AstState -> IO a

-- |union of intern program state and gui
data AstState = AstState
  { state :: State -- ^ intern program state
  , gui :: GUI -- ^ gtk data types
  , options :: Options -- ^ global program options
  }

-- |data type for global options
data Options = Options
  { font :: String -- ^ font name of textbuffer
  , fsize :: Int -- ^ font size of textbuffer
  }

-- |data type for the intern program state
data State =  forall a .  State
  { cFile :: (String,String) -- ^ current file
  , textchanged :: (Bool,Bool) -- ^ true if file changed
  , cursor :: (CursorP,CursorP) -- ^ last active cursor position
  , languages :: [Language] -- ^ known languages
  , config :: Configuration -- ^ current configuration
  , configFile :: FilePath -- ^ path of current configuraton file 
  }

-- |main gui data type, contains gtk components
data GUI = GUI
  { window :: Window -- ^ main window
  , tv :: (TreeView,TreeView) -- ^ treeview
  , sb :: (SourceBuffer,SourceBuffer) -- ^ sourceview
  , tvConf :: TextView -- ^ text view showing the config file
  , dlgAbout :: AboutDialog -- ^ about dialog
  }

data CursorP = CursorP 
  { cursorLine :: Int
  , cursorRow  :: Int
  }

-- |indicator data type for both areas
data Area = L -- ^ left area 
          | R -- ^ right area

-- |a configuration contains of relatons between nodes
data Configuration = Configuration
  { relations :: [Relation]
  }

-- |data type to specify binary relations between nodes
data Relation = Relation 
  { e1 :: Elem -- ^ first relation element
  , e2 :: Elem -- ^ second relation element
  }

-- |an element of the relation
data Elem = Elem
  { path :: [Direction]   -- ^ path in ast to a node 
  , filepath :: FilePath  -- ^ file containing the ast
  } 

-- |data type to specify paths in trees, a path has the type 
-- > [Direction]
data Direction 
  = D -- ^ go down one level to the leftmost child
  | Ri -- ^ stay at the same level and go to the right

-- * parser of data type configuration

readConfig :: String -> Configuration
readConfig = Configuration . map readRelation . lines

readRelation :: String -> Relation
readRelation s = 
  let e1 = takeWhile (/=' ') s in
  let e2 = drop (1+length e1) s in
  Relation (readElem e1) (readElem e2)

readElem :: String -> Elem
readElem s = 
  let (p,fp) = span (/='@') s in
  Elem (map readDirection p) (tail fp)
  
readDirection :: Char -> Direction
readDirection 'r' = Ri
readDirection 'd' = D
readDirection _ = error "direction r or d expected"  


-- * getter functions

getConfigFile :: IORef AstState -> IO FilePath
getConfigFile = fmap (configFile . state) . readIORef

getTvConf :: IORef AstState -> IO TextView
getTvConf = fmap (tvConf . gui) . readIORef 

getSourceBuffer :: Area -> IORef AstState -> IO SourceBuffer
getSourceBuffer a r = do
  let sel = case a of 
              L -> fst
              R -> snd
  fmap (sel . sb . gui) $ readIORef r

getTreeViews :: IORef AstState -> IO [TreeView]
getTreeViews r = do
  t1 <- fmap (fst . tv . gui) $ readIORef r
  t2 <- fmap (snd . tv . gui) $ readIORef r
  return [t1,t2] 

getTreeView :: Area -> IORef AstState -> IO TreeView
getTreeView L = fmap (fst . tv . gui) . readIORef 
getTreeView R = fmap (snd . tv . gui) . readIORef 

getSourceBuffers :: IORef AstState -> IO [SourceBuffer]
getSourceBuffers r = do
  s1 <- fmap (fst . sb . gui) $ readIORef r
  s2 <- fmap (snd . sb . gui) $ readIORef r
  return [s1,s2] 

getAstState :: IORef AstState -> IO AstState
getAstState = readIORef

-- |returns gui data type
getGui :: IORef AstState -> IO GUI
getGui = fmap gui . readIORef 

getState :: IORef AstState -> IO State 
getState = fmap state . readIORef 

getLangs :: IORef AstState -> IO [Language]
getLangs = fmap (languages . state) . readIORef

getChanged :: Area -> IORef AstState -> IO Bool
getChanged L = fmap (fst . textchanged . state) . readIORef
getChanged R = fmap (snd . textchanged . state) . readIORef

getCursor :: Area -> IORef AstState -> IO CursorP
getCursor L = fmap (fst . cursor . state) . readIORef
getCursor R = fmap (snd . cursor . state) . readIORef

getFile :: Area -> IORef AstState -> IO String
getFile L = fmap (fst . cFile . state) . readIORef
getFile R = fmap (snd . cFile . state) . readIORef

getWindow = fmap (window . gui) . readIORef

-- * setter functions

setCursor :: Area -> CursorP -> IORef AstState -> IO ()
setCursor a cp r = modifyIORef r (f a) where
  f :: Area -> AstState -> AstState
  f L s@(AstState (State f c (_,cR) ls co cf) _ _) = 
    s { state = State f c (cp,cR) ls co cf}
  f R s@(AstState (State f c (cL,_) ls co cf) _ _) = 
    s { state = State f c (cL,cp) ls co cf}

setcFile :: Area -> FilePath -> IORef AstState -> IO ()
setcFile a file r = modifyIORef r (f a) where
  f :: Area -> AstState -> AstState
  f L s@(AstState (State (_,cR) cp c ls co cf) _ _) = 
    s { state = State (file,cR) cp c ls co cf}
  f R s@(AstState (State (cL,_) cp c ls co cf) _ _) = 
    s { state = State (cL,file) cp c ls co cf}

setChanged :: Area -> Bool -> IORef AstState -> IO ()
setChanged a b r = modifyIORef r (f a) where
  f :: Area -> AstState -> AstState
  f L s@(AstState (State f (_,c) cp ls co cf) _ _) = 
    s { state = State f (b,c) cp ls co cf}
  f R s@(AstState (State f (c,_) cp ls co cf) _ _) = 
    s { state = State f (c,b) cp ls co cf}


setConfiguration :: Configuration -> IORef AstState -> IO ()
setConfiguration c r = modifyIORef r f where
  f :: AstState -> AstState
  f s@(AstState (State f cc cp ls _ cf) _ _) = 
    s { state = State f cc cp ls c cf}

setConfigFile :: FilePath -> IORef AstState -> IO ()
setConfigFile fp r = modifyIORef r f where
  f :: AstState -> AstState
  f s@(AstState (State f cc cp ls c _) _ _) = 
    s { state = State f cc cp ls c fp}

-- * misc transformations

addRelation :: Relation -> IORef AstState -> IO ()
addRelation r ref = modifyIORef ref f where
  f :: AstState -> AstState
  f s@(AstState (State f cc cp ls (Configuration rs) fp) _ _) = 
    s { state = State f cc cp ls (Configuration $ rs++[r]) fp}

-- instances

instance Show Relation where
  show (Relation e1 e2) = show e1 ++" "++ show e2

instance Show Elem where
  show (Elem p file) = show p ++ "@" ++ file 

instance Show Direction where
  show D  = "d"
  show Ri = "r"
  
