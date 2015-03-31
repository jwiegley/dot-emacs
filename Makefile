all:
	notangle -Rzencoding-trie.el zencoding-trie.nw > zencoding-trie.el

docs:
	noweave -latex zencoding-trie.nw > zencoding-trie.latex
	pdflatex zencoding-trie.latex