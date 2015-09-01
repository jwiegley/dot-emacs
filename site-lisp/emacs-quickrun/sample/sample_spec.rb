# -*- coding: utf-8 -*-
require 'rspec'

def add(a, b)
  a + b
end

def sub(a, b)
  a * b
end

describe "Test func" do
  it "one plus one" do
    (add(1,1)==2).should be_true
  end
  it "one minus one" do
    (sub(1,1)==0).should be_true
  end
end

#
#  Local Variables:
#  quickrun-option-cmd-alist: ((:command . "rspec")
#                              (:exec    . "%c -c %s"))
#  End:
#
