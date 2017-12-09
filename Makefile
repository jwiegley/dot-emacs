VERSION = 0.5
CONTENT_DIR = emacs-cl-$(VERSION)
CONTENT_TAR = $(CONTENT_DIR).tar

package: $(CONTENT_TAR)

$(CONTENT_TAR): $(CONTENT_DIR)
	tar cf $@ $<

$(CONTENT_DIR): emacs-cl-pkg.el Makefile
	rm -rf $(CONTENT_DIR)
	mkdir $(CONTENT_DIR)
	sed "s/VERSION/$(VERSION)/" < $< > $(CONTENT_DIR)/$<
	cp README $(CONTENT_DIR)
	cp COPYING $(CONTENT_DIR)
	cp src/* $(CONTENT_DIR)

clean:
	$(MAKE) -C src clean
	rm -rf $(CONTENT_DIR) $(CONTENT_TAR)
