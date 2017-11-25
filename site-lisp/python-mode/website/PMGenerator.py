"""Standard Generator with slight tweaks."""

from StandardGenerator import StandardGenerator

try:
    import rst_html
except ImportError:
    print 'Unable to import rst_html/docutils'
    print 'Get and install the docutils from docutils.sf.net'
    rst_html = None

class PMGenerator(StandardGenerator):
    def __init__(self, file, rootdir, relthis):
        StandardGenerator.__init__(self, file, rootdir, relthis)
        self.rootdir = rootdir
        self.filename = file
        self.__body = None
        self.__cont = None

    def get_corner(self):
        return ('''<center><a href="%(rootdir)s/">No Logo!</a></center>''' %
                self.__dict__)

    def get_banner(self):
        return '''\
<table width="100%%">
<tr>
<td><a href="%(rootdir)s/docs/">Python-Mode Documentation</a></td>
<td><a href="http://www.python.org/">Python</a></td>
</tr>
<tr>
<td><a href="http://www.gnu.org/software/emacs/">GNU Emacs</a></td>
<td><a href="http://www.xemacs.org/">XEmacs</a></td>
</tr>
</table>
        ''' % self.__dict__

    def _grokbody(self):
        if self.__body is None:
            data = self._parser.fp.read()
            # convert to Unicode:
            text = data.decode(self.get_encoding())
            if self.get_content_type() == 'text/x-rst':
                if rst_html is None:
                    print 'ReST-to-HTML conversion not available'
                else:
                    text = rst_html.process_rst(self.filename, text)
            # convert Unicode back to 8-bit string:
            text = text.encode(self.get_charset(), 'xmlcharrefreplace')
            i = text.find('<!--table-stop-->')
            if i >= 0:
                self.__body = text[:i]
                self.__cont = text[i+17:]
            else:
                # there is no wide body
                self.__body = text

    def get_body(self):
        self._grokbody()
        return self.__body

    def get_cont(self):
        self._grokbody()
        return self.__cont

    def get_encoding(self):
        return self._parser.get('encoding', 'utf-8')

    def get_content_type(self):
        return self._parser.get('content-type', use_defaults=False)


