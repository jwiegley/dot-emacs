all: test

test: ecukes

ecukes:
	cask exec ecukes features

.PHONY: ecukes test all
