#!/usr/bin/env python3

from bs4 import BeautifulSoup
from os import mkdir
from os.path import join, split
from collections import defaultdict, OrderedDict
import errno
import re
import sys
import itertools
import os

def deduplicate(seq, key):
    seen = set()
    deduped = []
    for elem in seq:
        k = key(elem)
        if k not in seen:
            deduped.append(elem)
            seen.add(k)
        else:
            print("Duplicate: {} (with key {})".format(elem, k))
    return deduped

class Abbrev:
    "A single variant, extracted from a pattern."

    PRIORITIES = ("ltac", "tactic", "vernac", "scope", "error")
    ARGCHOICE_TRANSLATED_RE = re.compile(r"@{[^{}]+ | [^{}]+}")

    def __init__(self, variant, pattern):
        self.abbrev = variant
        self.pattern = pattern

    @staticmethod
    def count_holes(pattern):
        return len(TextPattern.ID_RE.findall(pattern))

    @staticmethod
    def key(abbrev):
        abbr, pat = abbrev.abbrev, abbrev.pattern
        priority = Abbrev.PRIORITIES.index(pat.typ)
        has_choices = Abbrev.ARGCHOICE_TRANSLATED_RE.search(abbr) is not None
        if pat.typ == "tactic":
            # Roughly preserve original order of tactics, moving argumentless
            # ones at the beginning of each section and choice ones at the bottom.
            return (priority, pat.source, has_choices, Abbrev.count_holes(abbr) > 0, pat.ind)
        elif pat.typ in ("vernac", "ltac"):
            # Sort vernacs alphabetically by stripped abbrev (no holes nor
            # punctuation), then by chapter; inside a single chapter, for
            # vernacs that strip to the same string, sort by increasing number
            # of holes (putting the ones with choices at the bottom; finally,
            # disambiguate by order in the refman. By doing the sorting on
            # individual abbrevs, we ensure that abbrevs that have choices do
            # not penalize their variants.
            # Note that we use abbr to generate the key; using pat.variants[0]
            # would group variants their original entry.
            key = re.sub("[^A-Z]", "", re.sub(TextPattern.ID_RE, "", abbr).upper())
            return (priority, has_choices, key, pat.source, Abbrev.count_holes(abbr), pat.ind)
        else:
            return (priority, abbr.upper(), pat.ind)

    @staticmethod
    def abbrevs_to_strings(abbrevs, with_info=False):
        for abbrev in abbrevs:
            if with_info:
                yield abbrev.abbrev, abbrev.pattern.source, abbrev.pattern.ind
            else:
                yield abbrev.abbrev

    @staticmethod
    def collect_sorted_strings(patterns):
        abbrevs = sorted(TextPattern.patterns_to_abbrevs(patterns), key=Abbrev.key)
        strings = Abbrev.abbrevs_to_strings(abbrevs, with_info=True)
        strings = deduplicate(strings, key=lambda x: re.sub("[+&]}", "+}", re.sub(" ", "", x[0].lower().rstrip('.'))))
        strings = [(string.replace('"', r'\"'), source, index) for
                   (string, source, index) in strings]
        return strings

class TextPattern:
    ID_PAT = r'@{([^{}]+)}'
    REPLACEMENTS = [(re.compile(x), y) for (x, y) in
                    [(r'[\r\n  ]+', ' '),
                     (r'([\(\{\[]) +', r'\1'),      # Spurious spaces after opening brackets
                     (r' +([\)\}\]])', r'\1'),      # Spurious spaces before closing brackets
                     (r'\.\.\.', '…'),              # Ellipses
                     ("‘‘", '"'), ("’’", '"'),      # `` and '' in texttt
                     (ID_PAT + "[′’]", r"@{\1'}")]] # Primes in identifiers (two types!)

    ALT_RE    = re.compile(r'\[\?\<\<([^\[\]]+)\>\>\?\]')
    OPTION_RE = re.compile(r'^(Set|Unset|Test) ')
    ARGCHOICE_RE = re.compile(r"[a-zA-Z]+(,[a-zA-Z]+)+")
    # The char_before group avoids pathologic cases like "In environmen(t ... t)he term"
    DOTS_RE = re.compile(r"(?P<char_before>[^a-z])(?P<repeated_element>[^ ](?:.*[^ ])?) *(?P<separator>(.*[^ ])?) *… *(?P=separator) *(?P=repeated_element)")
    ID_RE = re.compile(ID_PAT)

    def __init__(self, source, ind, typ, pattern):
        self.source = source
        self.ind = ind
        self.typ = typ
        self.variants = [self.preprocess_one(pattern)]
        self.unique_variants = None # Populated upon cleanup

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
        char_before, repeated, sep = match.group("char_before"), match.group("repeated_element"), match.group("separator")

        repeated = TextPattern.replace_dots_re(repeated)
        sep = sep.replace(' ', '')

        nb_ids = len(TextPattern.ID_RE.findall(repeated))

        if nb_ids == 0:
            print("Repeated pattern {} in {} does not contain identifiers".format(repeated, match.group(0)))
            raise Exception
        elif nb_ids == 1:
            indicator = '+'
        else:
            indicator = '&'

        return char_before + TextPattern.ID_RE.sub(r'@{\1' + sep + indicator + '}', repeated)

    @staticmethod
    def strip_pattern(pattern):
        """Remove identifiers, non-ascii characters, and extrac spaces from COMMAND.
        These replacements are useful for comparing options.  For example, we
        don't want to guess [Set Default Timeout] from [Unset Default Timeout],
        given that we already have [Set Default Timeout @{n}].  Same for [Set
        Default Goal Selector] from [Unset Default Goal Selector] (we already
        have [Set Default Goal Selector "@{selector}"])"""
        for regexp in (TextPattern.ID_RE, re.compile(r"[^a-zA-Z]"), re.compile(r" *$")):
            pattern = regexp.sub("", pattern)
        return pattern

    @staticmethod
    def with_option_variants(variants, stripped_already_known):
        for variant in variants:
            # NOTES:
            # * We don't generate variants for commands with holes
            # * '"' is a special case for [Set Loose Hint Behaviour "Lax"]
            if (TextPattern.OPTION_RE.match(variant) and not TextPattern.ID_RE.search(variant)) and not '"' in variant:
                # We always return the original variant
                yield variant
                # Plus option variants, if not mentionned elsewhere in the manual
                for repl in ("Set ", "Unset ", "Test "):
                    new_variant = TextPattern.OPTION_RE.sub(repl, variant)
                    if (new_variant != variant and TextPattern.strip_pattern(new_variant) not in stripped_already_known):
                        yield new_variant
            else:
                yield variant

    @staticmethod
    def with_alternatives(variants, already_known, typ, may_discard = False):
        for variant in variants:
            if TextPattern.ALT_RE.search(variant):
                yield from TextPattern.with_alternatives(
                    (TextPattern.ALT_RE.sub('',    variant, 1),
                     TextPattern.ALT_RE.sub(r'\1', variant, 1)),
                    already_known, typ, True)
            else:
                variant = TextPattern.cleanup_single(variant, typ)
                if not (may_discard and (variant in already_known)):
                    yield variant

    def add_variants(self, already_known, stripped_already_known):
        with_opt = TextPattern.with_option_variants(self.variants, stripped_already_known)
        with_alt = TextPattern.with_alternatives(with_opt, already_known, self.typ)
        self.variants = [TextPattern.replace_argchoice(variant) for variant in with_alt]
        already_known.update(self.variants)
        stripped_already_known.update(map(TextPattern.strip_pattern, self.variants))

    @staticmethod
    def cleanup_single(variant, typ):
        for reg, sub in TextPattern.REPLACEMENTS:
            variant = reg.sub(sub, variant)
        variant = variant.strip()
        if typ == "vernac": # Add final dot
            variant = re.sub(r'[ \.]*$', '.', variant)
        return variant

    def cleanup(self, known):
        self.variants = [TextPattern.cleanup_single(variant, self.typ) for variant in self.variants]
        self.unique_variants = [variant for variant in self.variants if variant not in known]
        known.update(self.unique_variants)
        if any(variant == "" or "…" in variant or "..." in variant for variant in self.unique_variants):
            print(self)
            raise Exception

    @staticmethod
    def choicify(match):
        return "@{" + " | ".join(match.group(0).split(",")) + "}"

    @staticmethod
    def replace_argchoice(variant):
        return TextPattern.ARGCHOICE_RE.sub(TextPattern.choicify, variant)

    @staticmethod
    def patterns_to_abbrevs(patterns):
        for pattern in patterns:
            for variant in pattern.unique_variants:
                yield Abbrev(variant, pattern)

    @staticmethod
    def expand_patterns(patterns):
        known = set()
        stripped_known = set()
        for pattern in patterns:
            pattern.add_variants(known, stripped_known)

        known = set()
        for pattern in patterns:
            pattern.cleanup(known)

        return patterns

    @staticmethod
    def format_defconst_body(strings):
        return "\n    ".join('\'("{}" . ("{}" . {}))'.format(*string)
                             for string in strings)

    @staticmethod
    def format_defconst(strings, name):
        DEFCONST = '(defconst company-coq--refman-{}-abbrevs\n  (list\n    {}))'
        lisp = TextPattern.format_defconst_body(strings)
        return DEFCONST.format(name, lisp)

    def __repr__(self):
        return repr((self.source, self.ind, self.typ, self.variants, self.unique_variants))

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
                print("Unexpected style {} on span {} of {}".format(style, span, self.soup))
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
            # '[?<<' and '>>?]' are matched by ALT_RE.  The <o>s are added by
            # the \zeroorone macro
            if o.string == '[':
                o.string = '[?<<'
                o.unwrap()
            elif o.string == ']':
                o.string = '>>?]'
                o.unwrap()

        if any(self.soup.find_all("br")):
            print("Splitting {} at first <br/> tag".format(self))
            self.soup.contents = list(itertools.takewhile(lambda tag: tag.name != "br", self.soup.contents))

        for tag in self.soup.find_all():
            if tag.name != "o":
                print("{} contains unexpected tag {}".format(self.soup.contents, tag))
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

        # Unneeded thanks to custom rendering
        # for nuke in ("table", "hr"):
        #     for tag in self.soup.find_all(nuke):
        #         tag.decompose()

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
                print("Discarding TOC link '{}'".format(elem.parent.get_text().strip()))
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

        # Reset times, since they are recorded in gzip archive
        jan01_2015 = 1420070400
        os.utime(outpath, (jan01_2015, jan01_2015))

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
    patterns_by_typ = defaultdict(list)
    for p in patterns:
        patterns_by_typ[p.typ].append(p)

    strings_by_typ = OrderedDict()
    for typ in Abbrev.PRIORITIES:
        strings_by_typ[typ] = Abbrev.collect_sorted_strings(patterns_by_typ[typ])

    with open(template_path) as template_f:
        template = template_f.read()

    with open(template_path.replace(".template", ""), mode='w') as output:
        abbrevs = "\n\n".join(TextPattern.format_defconst(strings, typ)
                              for (typ, strings) in strings_by_typ.items())
        output.write(template.replace('$ABBREVS$', abbrevs))

    with open("etc/tactics", mode = "w") as output:
        for strings in strings_by_typ.values():
            for string, _, _ in strings:
                output.write(string)
                output.write("\n")

def main():
    pats = process_files(sys.argv[1], sys.argv[3:])
    write_patterns(sys.argv[2], pats)

if __name__ == '__main__':
    main()
