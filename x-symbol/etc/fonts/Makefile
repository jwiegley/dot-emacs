### Makefile --- create fonts for package x-symbol

## Author: Christoph Wedler <wedler@users.sourceforge.net>
## Version: 4.5
## Keywords: fonts, WYSIWYG, LaTeX, HTML, wp, math
## X-URL: http://x-symbol.sourceforge.net/

# This file is not part of XEmacs.

# This software is free software; you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the
# Free Software Foundation; either version 2, or (at your option) any
# later version.

# This software is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
# for more details.

# You should have received a copy of the GNU General Public License
# along with This software; see the file COPYING.  If not, write to
# the Free Software Foundation, Inc., 59 Temple Place - Suite 330,
# Boston, MA 02111-1307, USA.

# latin-2: ftp://ftp.vslib.cz/pub/unix/X11/fonts/iso8859-2/ (1998)
# latin-3: XEMACS/aux/fonts/ (1998), changed
# latin-5: ETL (1998)
# latin-9: http://linux.ee/~ville/vh-fonts/vh-fonts-0.99.2.tar.gz (2002)
#          http://www.inp.nsk.su/~bolkhov/files/fonts/cyr-rfx/srctgz/
#          cyr-rfx-iso8859-15-1.0.bdfs.tgz: didn't succeed to download

PERL = perl
BDFTOPCF = bdftopcf

FONTS = ../fonts
GENFONTS = ../genfonts
ORIGFONTS = ../origfonts
PCFDIR = ../pcf

ORIGBDFS = helvR12.bdf helvR14.bdf
BDFS = 2helvR12.bdf 3helvR12.bdf 5etl14.bdf heriR12.bdf \
	xsymb0_12.bdf xsymb1_12.bdf \
	2helvR14.bdf 3helvR14.bdf 5etl16.bdf heriR14.bdf \
	xsymb0_14.bdf xsymb1_14.bdf
EXTRABDFS = nilxs.bdf

.SUFFIXES:
.SUFFIXES: .pcf .bdf

vpath %.bdf $(FONTS):$(ORIGFONTS):$(GENFONTS)

GENS = $(patsubst %.bdf,$(GENFONTS)/%sub.bdf,$(ORIGBDFS)) \
	$(patsubst %.bdf,$(GENFONTS)/%sub.bdf,$(BDFS)) \
	$(patsubst %.bdf,$(GENFONTS)/%sup.bdf,$(ORIGBDFS)) \
	$(patsubst %.bdf,$(GENFONTS)/%sup.bdf,$(BDFS))
PCFS = $(patsubst %.bdf,$(PCFDIR)/%.pcf,$(BDFS)) \
	$(patsubst %.bdf,$(PCFDIR)/%.pcf,$(EXTRABDFS)) \
	$(patsubst %.bdf,$(PCFDIR)/%sub.pcf,$(ORIGBDFS)) \
	$(patsubst %.bdf,$(PCFDIR)/%sub.pcf,$(BDFS)) \
	$(patsubst %.bdf,$(PCFDIR)/%sup.pcf,$(ORIGBDFS)) \
	$(patsubst %.bdf,$(PCFDIR)/%sup.pcf,$(BDFS))

$(PCFDIR)/%.pcf: %.bdf
	$(BDFTOPCF) -o $@ $<

$(GENFONTS)/%sub.bdf: %.bdf
	$(PERL) ./makesub $< $@
$(GENFONTS)/%sup.bdf: %.bdf
	$(PERL) ./makesub $< $@

## vpath and VPATH don't accept a dir which doesn't exists yet...
all:
	$(MAKE) mkdirs
	$(MAKE) pcfs

echo:
	echo $(BDFS)
	echo $(GENS)

mkdirs:
	-if [ ! -d $(GENFONTS) ]; then mkdir $(GENFONTS); fi
	-if [ ! -d $(PCFDIR) ]; then mkdir $(PCFDIR); fi

gens: $(GENS)

pcfs: gens $(PCFS)
	cd $(PCFDIR) ; mkfontdir
	-xset fp rehash

clean:
	-if [ -d $(GENFONTS) ]; then rm -f $(GENFONTS)/*.bdf ; fi
	-if [ -d $(PCFDIR) ]; then \
		rm -f $(PCFDIR)/*.pcf $(PCFDIR)/fonts.dir ; fi
