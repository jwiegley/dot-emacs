all: monitor.info monitor.texi

EMACSBIN="emacs"
RAW_DOCS=monitor.org

org-convert=@$(EMACSBIN) -batch -Q -L .. monitor.org --eval "(progn (ignore-errors (org-texinfo-convert-region-to-texinfo)) (org-texinfo-export-to-$(1)))"

monitor.texi : $(RAW_DOCS)
	$(call org-convert,texinfo)

monitor.info : $(RAW_DOCS)
	$(call org-convert,info)
