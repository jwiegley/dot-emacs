#!/usr/bin/env python

import os, sys
import linecache
import tempfile
from pycomplete import *

def test_signature():
    assert pysignature('') == ''
    assert pysignature('os.path.join') == 'join: (a, *p)'
    assert pysignature('json.dump').startswith(
        'dump: (obj, fp, skipkeys=False, ensure_ascii=True, ')
    assert pysignature('json.JSONEncoder.encode') == 'encode: (self, o)'
    assert pysignature('json.JSONEncoder').startswith(
        '__init__: (self, skipkeys=False, ensure_ascii=True, ')
    assert pysignature('xml.dom.minidom.parse') == \
           'parse: (file, parser=None, bufsize=None)'
    assert pysignature('csv.reader') == \
           'csv_reader = reader(iterable [, dialect=\'excel\']'
    assert pysignature('super') in (
        'super(type) -> unbound super object',
        'super() -> same as super(__class__, <first argument>)',
        'super(type, obj) -> bound super object; requires isinstance(obj, type)')

def test_help():
    assert pyhelp('os.path.join').startswith('Help on function join')
    assert pyhelp('logging', imports=('import logging',)).startswith(
        'Help on package logging:\n\nNAME\n    logging\n')
    assert pyhelp('csv', imports=('import csv',)).startswith(
        'Help on module csv:\n\nNAME\n    csv - CSV parsing and writing.\n')
    assert pyhelp('import').startswith(
        ('The ``import`` statement\n************************\n',
         'The "import" statement\n**********************\n'))
    assert pyhelp('pydoc.help').startswith(
        'Help on class Helper in module pydoc')
    assert pyhelp('') == ''

def test_complete():
    assert pycomplete('') == ''
    assert pycomplete('sys.getd') == ['getdefaultencoding', 'getdlopenflags']
    assert pycomplete('set') == ['set', 'setattr']
    assert pycomplete('settr') is None
    assert pycomplete('settr', imports=['from sys import settrace']) == [
        'ace']
    # Test with cached imports
    assert pycomplete('settr') == ['ace']
    # Not cached for other files
    fpath = os.path.abspath(__file__)
    assert pycomplete('settr', fname=fpath) is None
    assert pycomplete('settr', fname=fpath,
                      imports=['from sys import settrace']) == ['ace']
    assert pycomplete('foo.') is None
    assert pycomplete('JSONEnc') is None
    assert pycomplete('JSONEnc', imports=['from json import *']) == ['oder']
    assert pycomplete('A') == [
        'ArithmeticError', 'AssertionError', 'AttributeError']

def test_completions():
    all_completions = pycompletions('')
    assert all_completions[0] == 'ArithmeticError'
    assert all_completions[-1] == 'zip'
    assert pycompletions('os.path.jo') == ['join']
    assert pycompletions('settr', imports=['']) == []
    assert pycompletions('settr',
                imports=['from sys import settrace']) == ['settrace']
    # Check if imports are still cached.
    assert pycompletions('settr', imports=None) == ['settrace']
    # Change list of imports, so that cache is invalidated.
    assert pycompletions('settr', imports=['']) == []

def test_location():
    fn, line = pylocation('os.path.join')
    assert os.path.exists(fn)
    assert linecache.getline(fn, line).startswith('def join')
    assert pylocation('io.StringIO') is None
    fn, line = pylocation('json')
    assert os.path.exists(fn)
    assert pylocation('for') is None

def test_docstring():
    assert pydocstring('os.path.abspath') == 'Return an absolute path.'
    assert pydocstring('os.path').startswith(
        'Common operations on Posix pathnames.\n')
    assert pydocstring('json.JSONEncoder.encode').startswith(
        'Return a JSON string representation of a Python data structure.\n')
    assert pydocstring('yield') == ''
    assert pydocstring('numbers.Real.real') == \
      'Real numbers are their real component.'
    assert pydocstring('notexisting') == ''
    assert pydocstring('re.IGNORECASE') == ''

def test_parse_source():
    tmp_file = tempfile.NamedTemporaryFile(suffix='.py', mode='w')
    name = tmp_file.name
    with tmp_file.file as fh:
        assert pyparse('not_existing', only_reload=True) == None
        assert pyparse('not_existing') == \
           "[Errno 2] No such file or directory: 'not_existing'"
        assert pyparse(name) is None
        # Nothing imported so far
        assert pycompletions('dat' , name) == []
        src = """
"Doc for module."
from __future__ import print_function
import sys, os, io, re
from datetime import date, \
time
import argparse
if os.getenv('LC'):
    import linecache

modvar = 1
mod_re = re.compile(r'^test')

def testfunc():
    "Doc for testfunc."
    import urllib

def emptyfunc():
    "Function with only docstring."

class TestClass(date):
    "Doc for TestClass."
    CONST1 = 7
    CONST2 = 'abc'
    CONST3 = ['a', ]

    def __init__(self):
        self._member1 = 'string member'
        self._member2 = None
        self.__member3 = [ None, open('not_existing') ]
        self.member4 = argparse.ArgumentParser()
        self.member4 = None
        self.member5 = open('not_existing')
        self.member6 = self.member7 = { 'multiple': 'targets' }
        self.member8, self.member9 = 'tuple', 'assignment'
        self.member10 = [ n for n in range(3) ]
        self.member11 = SyntaxError()
        self.member12 = testfunc()
    def testmeth(self, arg1=modvar):
        "Doc for testmeth."
        sys.stdout.write('From testmeth %d' % arg1)
        if arg1 == 2:
            self._member1 = None
    @staticmethod
    def teststaticmeth(arg1=2):
        "Doc for teststaticmeth."
        sys.stdout.write('From teststaticmeth %d' % arg1)
    @classmethod
    def testclassmeth(cls, arg1=3):
        "Doc for testclassmeth."
        open('not_existing')
    @property
    def testprop(self):
        "Doc for testprop."
        return 4 * 8

if __name__ == '__main__':
    testfunc()
"""
        num_src_lines = len(src.splitlines())
        fh.write(src)
        fh.flush()
        assert pyparse(name) == None
        # Check if only global imports are visible
        assert pycompletions('dat' , name) == ['date']
        assert pycompletions('tim' , name) == ['time']
        assert pycompletions('url' , name) == []
        assert pycompletions('line' , name) == ['linecache']
        assert pycompletions('os' , name) == ['os']
        # Check for definitions in local file
        assert pycompletions('test' , name) == ['testfunc']
        assert pycompletions('TestClass.CO' , name) == \
          ['CONST1', 'CONST2', 'CONST3']
        assert pycompletions('TestClass.test' , name) == \
          ['testclassmeth', 'testmeth', 'testprop', 'teststaticmeth']
        # Check for instance members
        assert pycompletions('TestClass._mem', name) == \
          ['_member1', '_member2']
        assert pycompletions('TestClass.__mem', name) == ['__member3']
        assert pycompletions('TestClass._member1.start', name) == \
          ['startswith']
        assert pycompletions('TestClass._member2.', name) == []
        assert pycompletions('TestClass.__member3.ext', name) == \
          ['extend']
        if sys.version_info[0] < 3:
            assert pycompletions('TestClass.member4.prin', name) == \
              ['print_help', 'print_usage', 'print_version']
        assert pycompletions('TestClass.member5.writel', name) == \
          ['writelines']
        assert pycompletions('TestClass.member6.from', name) == \
          ['fromkeys']
        assert pycompletions('TestClass.member7.from', name) == \
          ['fromkeys']
        assert pycompletions('TestClass.member10.ext', name) == \
          ['extend']
        assert pycompletions('TestClass.member11.ar', name) == \
          ['args']
        assert pycompletions('modvar.num', name) == ['numerator']
        assert pycompletions('mod_re.ma', name) == ['match']
        assert pydocstring('TestClass._member1', name) == ''
        assert pydocstring('TestClass._member2', name) == ''
        assert pydocstring('TestClass.__member3', name) == ''
        # Check for super class
        assert pycompletions('TestClass.week' , name) == ['weekday']
        assert pycompletions('TestClass.utc' , name) == []
        # Check signature, documentation and location
        assert pysignature('TestClass.testmeth', name) == \
          'testmeth: (self, arg1=1)'
        assert pydocstring('testfunc', name) == \
          'Doc for testfunc.'
        assert pylocation('TestClass.testclassmeth', name) == \
          (name, num_src_lines - 10)
        # Verify that loaded symbols are not affected by transient
        # syntax error
        fh.write('while')
        fh.flush()
        assert pyparse(name) == \
          'invalid syntax (%s, line %d)' % (os.path.basename(name),
                                            num_src_lines + 1)
        assert pycompletions('dat' , name) == ['date']
        # Replace file contents and check new imports
        fh.seek(0)
        fh.truncate(0)
        fh.write('import urllib\n')
        fh.flush()
        assert pyparse(name) == None
        assert pycompletions('dat' , name) == []
        assert pycompletions('url' , name) == ['urllib']

def run_tests():
    test_complete()
    test_completions()
    test_help()
    test_signature()
    test_location()
    test_docstring()
    test_parse_source()

if __name__ == "__main__":
    run_tests()
