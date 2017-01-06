IDLC=/usr/lib/xulrunner-1.9/xpidl
INC=/usr/share/idl/xulrunner-1.9/stable/
XPTS=MozRepl.xpt

all: $(XPTS)

%.xpt: %.idl
	$(IDLC) -m typelib -w -v -I $(INC) -e $(@) $(<)

.PHONY: all