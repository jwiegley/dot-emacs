#!/usr/bin/env python2.7

"""
opml2org.py -- convert OPML to Org mode
"""

import sys
import xml.etree.ElementTree as ET

class opmlDataObject:

    def __init__(self):
        self.hasHeadlineAttributes = False
        self.headlineDepth = 1
        self.listDepth = 0

def process_body(element, data=False):
    if not data:
        data = opmlDataObject()
    for outline in element:
        attrib = outline.attrib.copy()
        assert 'text' in attrib, 'missing text attribute'
        text = attrib.pop('text')
        if 'structure' in attrib:
            structure = attrib.pop('structure')
        else:
            if attrib or (not data.hasHeadlineAttributes and not data.listDepth):
                if attrib:
                    data.hasHeadlineAttributes = True
                structure = 'headline'
            elif len(outline):
                structure = 'list'
            else:
                structure = 'paragraph'

        if structure == 'headline':
            yield '%s %s' % ('*' * data.headlineDepth, text)
            if attrib:
                yield ':PROPERTIES:'
                for k, v in attrib.iteritems():
                    yield ':%s: %s' % (k, v)
                yield ':END:\n'
            if len(outline):
                data.headlineDepth += 1
                for child in process_body(outline, data):
                    yield child
                data.headlineDepth += -1
        elif structure == 'list':
            yield '%s- %s' % (' ' * data.listDepth, text)
            if len(outline):
                data.listDepth += 2
                for child in process_body(outline, data):
                    yield child
                data.listDepth += -2
        elif structure == 'paragraph':
            yield '%s\n' % text

def extract_header(head, tag, export_tag=None):
    if head.find(tag) is not None and head.find(tag).text:
        return '#+%s: %s' % (export_tag or tag.upper(), head.find(tag).text)

if __name__ == '__main__':
    head, body = ET.fromstring(sys.stdin.read())
    org_head = [
        extract_header(head, 'title'),
        extract_header(head, 'description'),
    ]
    org_body = process_body(body)

    sys.stdout.write((
        '\n'.join(filter(bool, org_head)) +
        '\n\n' +
        '\n'.join(org_body) +
        '\n'
    ).encode('utf-8', 'replace'))
