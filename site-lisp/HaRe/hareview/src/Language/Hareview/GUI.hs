{- contains the main GUI functions
 -
 -}
module Language.Hareview.GUI where

-- guiactions
import Language.Hareview.GUIData
import Language.Hareview.GUIActions 

-- base
import Control.Monad.Trans (liftIO)
import Data.IORef
-- filepath
import System.FilePath ((</>))

-- gtk
import Graphics.UI.Gtk hiding (Language) 
import Graphics.UI.Gtk.Gdk.EventM

-- glib
import System.Glib.Signals (ConnectId)

-- glade
import Graphics.UI.Gtk.Glade     

-- gtksourceview
import Graphics.UI.Gtk.SourceView

-- astview-utils
import Language.Hareview.Language

-- generated on-the-fly by cabal
import Paths_hareview (getDataFileName) 

-- | initiates aststate
buildAststate :: Options -> [Language] -> IO (IORef AstState)
buildAststate opt langs = do
  -- GTK init
  initGUI 

  -- load GladeXML
  Just xml <- xmlNew =<< getDataFileName ("data" </> "astview.glade")
  -- Just xml <- xmlNew =<< getDataFileName ("data" </> "hareview.glade")
 
  -- get or create widgets
  window   <- xmlGetWidget xml castToWindow "mainWindow"
  treeviewL <- xmlGetWidget xml castToTreeView "treeviewLeft"
  treeviewR <- xmlGetWidget xml castToTreeView "treeviewRight"

  tbL <- buildSourceView opt 
    =<< xmlGetWidget xml castToScrolledWindow "swSourceLeft" 

  tbR <- buildSourceView opt 
    =<< xmlGetWidget xml castToScrolledWindow "swSourceRight" 

  tvConfig <- xmlGetWidget xml castToTextView "tvConfig"

  dlgAbout <-xmlGetWidget xml castToAboutDialog "dlgAbout"

  -- build compound datatype
  let gui = GUI window 
                (treeviewL,treeviewR) 
                (tbL,tbR) 
                tvConfig 
                dlgAbout 
      state = State 
        { cFile = (unsavedDoc,unsavedDoc)
        , textchanged = (False,False)
        , cursor = (CursorP 0 0,CursorP 0 0)
        , languages = langs
        , config = Configuration [] 
        , configFile = unsavedDoc
        }

  r <- newIORef $ AstState state gui opt
   
  hooks r

  -- get all menuitems from xml and register guiactions to them
  mapM_ (registerMenuAction xml r) menuActions
  
  return r

-- -------------------------------------------------------------------
-- ** some helper functions
-- -------------------------------------------------------------------

-- |builds combobox label for a language
buildLabel :: Language -> String
buildLabel l = 
  name l
  ++ " ["
  ++ concatMap (" "++) (exts l)
  ++ "]"

-- | setup the GtkSourceView and add it to the ScrollPane. return the 
-- underlying textbuffer
buildSourceView :: Options -> ScrolledWindow -> IO SourceBuffer
buildSourceView opt sw = do
  sourceBuffer <- sourceBufferNew Nothing
  sourceBufferSetHighlightSyntax sourceBuffer True
  sourceView <- sourceViewNewWithBuffer sourceBuffer
  sourceViewSetShowLineNumbers sourceView True
  sourceViewSetHighlightCurrentLine sourceView True
  srcfont <- fontDescriptionFromString $ 
    font opt ++" "++show (fsize opt)
  widgetModifyFont sourceView (Just srcfont)
  containerAdd sw sourceView
  return sourceBuffer

-- | registers one GUIAction with a MenuItem
registerMenuAction 
  :: GladeXML -> IORef AstState 
  -> (String,AstAction ()) -> IO (ConnectId MenuItem)
registerMenuAction xml ref (gtkId,action) = do
  item <- xmlGetWidget xml castToMenuItem gtkId
  onActivateLeaf item $ action ref

-- | adds actions to some widgets
hooks :: AstAction (ConnectId Window)
hooks ref = do
  gui <- getGui ref
  -- textbuffer
  onBufferChanged (fst $ sb gui) $ do 
    actionBufferChanged L ref
    cp <- getCursorPosition L ref
    setCursor L cp ref
  onBufferChanged (snd $ sb gui) $ do
    actionBufferChanged R ref  
    cp <- getCursorPosition R ref
    setCursor R cp ref

  -- ctrl+p to reparse
  window gui `on` keyPressEvent $ tryEvent $ do
    [Control] <- eventModifier
    "p" <- eventKeyName
    liftIO $ actionReparseAll ref 

  dlgAbout gui `onResponse` (const $ widgetHide $ dlgAbout gui)
        
  window gui `on` deleteEvent $ tryEvent $ liftIO $ actionQuit ref
  
  -- window    
  onDestroy (window gui) mainQuit
