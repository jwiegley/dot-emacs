README.md: make-readme-markdown.el diffview.el
	emacs --script $< < diffview.el >$@

ifeq ($(LOCAL),1)
make-readme-markdown.el:
	cp -v ../make-readme-markdown/make-readme-markdown.el .
else
make-readme-markdown.el:
	wget -q -O $@ https://raw.github.com/mgalgs/make-readme-markdown/master/make-readme-markdown.el
endif

.INTERMEDIATE: make-readme-markdown.el
.PHONY: README.md
