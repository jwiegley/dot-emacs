#!/usr/bin/env python3

from bs4 import BeautifulSoup
from glob import glob
from os import mkdir
from os.path import join, split
import errno
import re
import sys

def deduplicate(seq, key):
    seen = set()
    deduped = []
    for elem in seq:
        k = key(elem)
        if k not in seen:
            deduped.append(elem)
            seen.add(k)
        else:
            print("Duplicate: {}".format(elem))
    return deduped

class TextPattern:
    ID_PAT = r'@{([^{}]+)}'
    REPLACEMENTS = [(re.compile(x), y) for (x, y) in
                    [(r'[\r\n  ]+', ' '),
                     (r'([\(\{\[]) +', r'\1'),
                     (r' +([\)\}\]])', r'\1'),
                     (r'\.\.\.', '…'),
                     (ID_PAT + "′", r"@{\1'}"),
                     ("‘‘", '"'), ("’’", '"')]]

    ALT_RE    = re.compile(r'\[\?([^\[\]]+)\?\]')
    OPTION_RE = re.compile(r'^Set ')
    ARGCHOICE_RE = re.compile("[a-zA-Z]+(,[a-zA-Z]+)+")
    DOTS_RE = re.compile(r"([^ ].+[^ ]) *((.*[^ ])?) *… *\2 *\1")
    ID_RE = re.compile(ID_PAT)

    def __init__(self, source, ind, typ, *variants):
        self.source = source
        self.ind = ind
        self.typ = typ
        self.variants = [self.preprocess_one(variant) for variant in variants]

    def preprocess_one(self, variant):
        variant = TextPattern.cleanup_single(variant, self.typ)
        variant = TextPattern.replace_dots_re(variant)
        if self.typ == "error":
            variant = variant.replace("…", "@{hole}")
        return variant

    @staticmethod
    def replace_dots_re(variant):
        while TextPattern.DOTS_RE.search(variant):
            variant = TextPattern.DOTS_RE.sub(TextPattern.pluralize_re, variant)
        return variant

    @staticmethod
    def pluralize_re(match):
        repeated, sep = match.group(1), match.group(2)

        repeated = TextPattern.replace_dots_re(repeated)
        sep = sep.replace(' ', '')

        nb_ids = len(TextPattern.ID_RE.findall(repeated))

        if nb_ids == 0:
            return None
        elif nb_ids == 1:
            indicator = '+'
        else:
            indicator = '&'

        return TextPattern.ID_RE.sub(r'@{\1' + sep + indicator + '}', repeated)

    @staticmethod
    def with_option_variants(variants, already_known):
        for variant in variants:
            yield variant
            if TextPattern.OPTION_RE.match(variant):
                for repl in ("Unset ", "Test "):
                    new_variant = TextPattern.OPTION_RE.sub(repl, variant)
                    if new_variant not in already_known:
                        yield new_variant

    @staticmethod
    def with_alternatives(variants, already_known, typ, may_discard = False):
        for variant in variants:
            if TextPattern.ALT_RE.search(variant):
                yield from TextPattern.with_alternatives((TextPattern.ALT_RE.sub('',    variant, 1),
                                                          TextPattern.ALT_RE.sub(r'\1', variant, 1),),
                                                         already_known, typ, True)
            else:
                variant = TextPattern.cleanup_single(variant, typ)
                if not (may_discard and (variant in already_known)):
                    yield variant

    def add_variants(self, already_known):
        with_opt = TextPattern.with_option_variants(self.variants, already_known)
        with_alt = TextPattern.with_alternatives(with_opt, already_known, self.typ)
        self.variants = list(with_alt)
        already_known.update(self.variants)

    @staticmethod
    def cleanup_single(variant, typ):
        for reg, sub in TextPattern.REPLACEMENTS:
            variant = reg.sub(sub, variant)
        variant = variant.strip()
        if typ == "vernac":
            variant = re.sub(r'[ \.]*$', '.', variant)
        return variant

    def cleanup(self, known):
        self.variants = [TextPattern.cleanup_single(variant, self.typ)
                         for variant in self.variants]
        self.variants = [variant for variant in self.variants
                         if variant not in known]
        known.update(self.variants)

    @staticmethod
    def choicify(match):
        return "@{" + "|".join(match.group(0).split(",")) + "}"

    @staticmethod
    def replace_argchoice(variant):
        return TextPattern.ARGCHOICE_RE.sub(TextPattern.choicify, variant)

    def finalize(self):
        if any(variant == "" or "…" in variant or "..." in variant for variant in self.variants):
            print(self.variants)
            print(self.typ)
            raise Exception

        self.variants = [TextPattern.replace_argchoice(variant) for variant in self.variants]

    @staticmethod
    def patterns_to_strings(patterns, with_info = False):
        for pattern in patterns:
            for variant in pattern.variants:
                if with_info:
                    yield variant, pattern.source, pattern.ind
                else:
                    yield variant

    @staticmethod
    def expand_patterns(patterns):
        known = set(TextPattern.patterns_to_strings(patterns))
        for pattern in patterns:
            pattern.add_variants(known)

        known = set()
        for pattern in patterns:
            pattern.cleanup(known)

        return patterns

    @staticmethod
    def format_defconst_body(strings):
        return "\n    ".join('\'("{}" . ("{}" . {}))'.format(*string)
                             for string in strings)

    @staticmethod
    def make_defconst(patterns, name):
        DEFCONST = '(defconst {}\n  (list\n    {}))'

        for pattern in patterns:
            pattern.finalize()

        strings = TextPattern.patterns_to_strings(patterns, with_info=True)
        strings = deduplicate(strings, key=lambda x: x[0].replace(" ", "").lower().rstrip('.'))
        strings = [(string.replace('"', r'\"'), source, index) for
                   (string, source, index) in strings]

        lisp = TextPattern.format_defconst_body(strings)
        return strings, DEFCONST.format(name, lisp)

    def __repr__(self):
        return repr((self.source, self.ind, self.variants))

class XMLPattern:
    def __init__(self, soup, source, ind):
        self.source = source
        self.soup = BeautifulSoup(str(soup)).body.contents[0]
        self.typ = soup["type"]
        self.ind = ind

    def cleanup(self):
        for span in self.soup.find_all("span"):
            style = span['style']
            span.attrs = {}

            if style == "font-style:italic":
                span.name = 'i'
            elif style == "font-style:oblique":
                span.name = 'o'
            elif style in ("font-family:monospace", "font-variant:small-caps"):
                span.unwrap()
            else:
                print(style)
                print(span)
                raise Exception

        for alias in ("em", "i"):
            for tag in self.soup.find_all(alias):
                tag.name = "o"

        for rotten in ("a", "sub", "sup"):
            for tag in self.soup.find_all(rotten):
                tag.decompose()

        for useless in ("code",):
            for tag in self.soup.find_all(useless):
                tag.unwrap()

        for o in self.soup.find_all("o"):
            if o.string == '[':
                o.string = '[?'
                o.unwrap()
            elif o.string == ']':
                o.string = '?]'
                o.unwrap()

        for tag in self.soup.find_all():
            if tag.name != "o":
                print(self)
                raise Exception

    def make_pattern(self):
        for o in self.soup.find_all("o"):
            o.insert_before("@{")
            o.insert_after("}")
            o.unwrap()

        return TextPattern(self.source, self.ind, self.typ, "".join(map(str, self.soup.children)).strip())

    def __repr__(self):
        return repr(self.soup)

class HtmlDocument:
    B36 = '0123456789abcdefghijklmnopqrstuvwxyz'
    RENAME_RE = re.compile(r'Reference-Manual([0-9]+)\.html')

    def __init__(self, fpath):
        _, self.fname = split(fpath)
        self.code = HtmlDocument.b36_from_match(HtmlDocument.RENAME_RE.match(self.fname))
        self.shortname = HtmlDocument.RENAME_RE.sub(HtmlDocument.rename_sub, self.fname)
        self.soup = BeautifulSoup(open(fpath, mode='rb'))

    @staticmethod
    def b36(num):
        s = []
        while num > 0:
            num, d = divmod(num, len(HtmlDocument.B36))
            s.append(HtmlDocument.B36[d])
        return "".join(reversed(s)) or HtmlDocument.B36[0]

    @staticmethod
    def b36_from_match(match):
        num = int(match.groups(1)[0])
        return HtmlDocument.b36(num)

    @staticmethod
    def rename_sub(match):
        return HtmlDocument.b36_from_match(match) + '.html'

    def cleanup(self):
        for span in self.soup.find_all('span'):
            style = span['style']
            if style == "font-style:italic" or style == "font-style:oblique":
                span.name = 'i'
            elif style == "font-family:monospace":
                span.name = 'tt'
            elif style == 'font-weight:bold':
                span.name = 'b'
            elif style == 'font-size:small':
                span.name = 'small'
            # elif style == 'font-family:sans-serif':
                # span.name = 'u'
            else:
                # print(style) font-family:sans-serif
                continue
            span.attrs = {}

        for i in self.soup.find_all('i'):
            right = i.next_sibling
            if right and right.name == 'sub':
                for child in right.children:
                    if child.name != 'i':
                        child.wrap(self.soup.new_tag('i'))

        for code in self.soup.find_all('code'):
            code.name = "tt"

        for nuke in ("table", "hr"):
            for tag in self.soup.find_all(nuke):
                tag.decompose()

        for a in self.soup.find_all('a'):
            if "href" in a.attrs:
                a["href"] = HtmlDocument.RENAME_RE.sub(HtmlDocument.rename_sub, a["href"])

    @staticmethod
    def is_toc_link(node):
        if node.name == "a" and "href" in node.attrs:
            return True or re.match(r"^[  ]*[0-9\.]+[  ]*", node.string)
        return False

    def read_patterns(self, ind):
        for ind, elem in enumerate(self.soup.find_all("definition"), ind):
            if HtmlDocument.is_toc_link(elem.parent):
                print("Discarding", elem.parent.get_text())
                continue

            xml = XMLPattern(elem, self.code, ind)

            elem.name = "a"
            elem.attrs = {"id": "qh" + str(ind)}

            xml.cleanup()
            yield xml.make_pattern()

    def writeout(self, outdir):
        outpath = join(outdir, self.shortname)

        with open(outpath, mode='w') as html_output:
            html_output.write(str(self.soup))

def process_files(outdir, paths):
    try:
        mkdir(outdir)
    except OSError as exception:
        if exception.errno != errno.EEXIST:
            raise

    patterns = []

    for fpath in sorted(paths):
        if fpath.endswith(".min.html"):
            return

        document = HtmlDocument(fpath)
        print(document.shortname, document.fname)

        doc_patterns = document.read_patterns(len(patterns))
        patterns.extend(doc_patterns)

        if outdir:
            document.cleanup()
            document.writeout(outdir)

    patterns = TextPattern.expand_patterns(patterns)
    return patterns

def write_patterns(template_path, patterns):
    errors = [p for p in patterns if p.typ == "error"]
    abbrevs = [p for p in patterns if p.typ != "error"]

    errors,  e_defconst = TextPattern.make_defconst(errors, "company-coq-errors")
    abbrevs, a_defconst = TextPattern.make_defconst(abbrevs, "company-coq-abbrevs")

    with open(template_path) as template_f:
        template = template_f.read()

    with open(template_path.replace(".template", ""), mode='w') as output:
        output.write(template.replace('$ABBREVS$', a_defconst + "\n\n" + e_defconst))

    with open("tactics", mode = "w") as output:
        for string, _, _ in abbrevs:
            output.write(string)
            output.write("\n")

pats = process_files(sys.argv[1], sys.argv[3:])
write_patterns(sys.argv[2], pats)
