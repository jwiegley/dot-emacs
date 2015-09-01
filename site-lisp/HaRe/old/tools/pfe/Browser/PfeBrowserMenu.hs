module PfeBrowserMenu where
import ContribFudgets
import Fudgets

-- If Haskell only had first class constructors...
#define CON(c) (Transl (c) (\x->case x of c y->Just y;_->Nothing))

data MenuCmd w
  = File FileCmd
  | View ViewCmd
  | Windows (WindowCmd w)
  | Cert CertCmd
  deriving (Eq)

data FileCmd
  = ReloadModule
  | EditModule
  | Quit
  deriving (Eq)

view0 = Hyper
data ViewCmd
  = Hyper
  | Typed
  deriving (Eq)

data WindowCmd w = WindowCmd w Bool deriving (Eq)

data CertCmd
  = NewCert
  | NewAll String
  | TodoCert
  | RevalidateAllQuick
  | ValidateAll
  deriving (Eq)

pfeMenuBarF certtypes =
   spacer1F (noStretchS False True `compS` leftS) (menuBarF menuBar)
  where
    menuBar =
      [item fileMenu  "File",
       item viewMenu  "View",
       item windowsMenu "Windows",
       item certMenu "Cert"]

    fileMenu =
      menu CON(File)
      [cmdItem ReloadModule     "Reload Module" `key` "r",
       cmdItem EditModule       "Edit Module"   `key` "e",
       cmdItem Quit		"Quit"		`key` "q"]

    viewMenu = menu idT [radioGroupItem CON(View) views view0 "Module View"]
      where
	views =
	  [--cmdItem Plain "Plain Source Text",
	   item Hyper "Highlighted & Hyperlinked" `key` "h",
	   item Typed "Type info" `key` "t"]
        idT = Transl id Just -- why not this?

    windowsMenu =
	menu CON(Windows)
	[toggleItem (wcon w) False (show w)|w<-[minBound..maxBound]]
      where
	wcon w = Transl (WindowCmd w) (inv w)
	inv w (WindowCmd w' b) = if w'==w then Just b else Nothing

    certMenu =
      menu CON(Cert)
      [cmdItem NewCert "Add one new Certificate..." `key` "n",
       subMenuItem CON(NewAll) newAllMenu "Add certificates to all assertions",
       cmdItem TodoCert "ToDo" `key` "d",
       cmdItem RevalidateAllQuick "Quick Revalidate All" `key` "v",
       cmdItem ValidateAll "Validate All"]

    newAllMenu = map strCmdItem certtypes

    strCmdItem s = cmdItem s s
