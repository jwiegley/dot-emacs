EDITOR_FILES=Vim/refactor.vim Emacs/haskell-refac.el 

all: GenEditorInterfaces ${EDITOR_FILES}

clean:
	rm -f LocalSettings.hi
	rm -f LocalSettings.hs
	rm -f LocalSettings.o
	rm -f Main.hi
	rm -f GenEditorInterfaces
	rm -f GenEditorInterfaces.exe
	rm -f GenEditorInterfaces.o
	rm -f GenEditorInterfaces.hi
	rm -f GenEditorInterfacesAux.o
	rm -f GenEditorInterfacesAux.hi
	rm -f Vim/refactor.vim
	rm -f Vim/EditorFunctions.hi
	rm -f Vim/EditorFunctions.o
	rm -f Emacs/haskell-refac.el
	rm -f Emacs/EditorFunctions.hi
	rm -f Emacs/EditorFunctions.o

LocalSettings.hs:
	./localpaths "${HARE_VERSION}"

GenEditorInterfaces: GenEditorInterfaces.hs LocalSettings.hs
	ghc --make -fglasgow-exts GenEditorInterfaces -o GenEditorInterfaces

Vim/refactor.vim: GenEditorInterfaces
	cd Vim; ../GenEditorInterfaces vim

Emacs/haskell-refac.el: GenEditorInterfaces
	cd Emacs; ../GenEditorInterfaces emacs ; ./Duplicate.sh


