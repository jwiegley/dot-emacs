import sublime_plugin
from subprocess import Popen, PIPE, STDOUT
from os import path
import sublime
import copy

class GitWipAutoCommand(sublime_plugin.EventListener):
  """docstring for GitWipPlugin"""

  def __init__(self):
    super(GitWipAutoCommand, self).__init__()
    self.p = None
    self.dirdata = None

  def on_post_save_async(self, view):
    #(dirname, fname) = path.split(view.file_name())
    self.dirdata = path.split(view.file_name())

    if self.p is None:      
      self.apply_git()
    else:
      print("git command is still running")      
      

  def finish_callback(self):    
    p = self.p
    if p is None:
      return

    if p.poll() is None: #not terminated yet
      sublime.set_timeout_async(lambda: self.finish_callback(), 20)
    else:

      rcode = p.returncode
      
      if rcode != 0:
        print ("git command error -> return code: %d" % rcode)
        for line in p.stdout:
          print(line)

      if self.dirdata is not None:
        apply_git(self)
      else:
        self.p = None
    
    

  def apply_git(self):
    (dirname, fname) = self.dirdata
    self.dirdata = None
    myenv = copy.copy(os.environ)
    myenv["PATH"] = "/usr/local/bin:" + myenv["PATH"]
    self.p = Popen(["git", "wip", "save", "WIP from ST3: saving %s" % fname, "--editor", "--", fname], 
      cwd=dirname, bufsize=8096, stdout=PIPE, stderr=STDOUT, env=myenv)
    sublime.set_timeout_async(lambda: self.finish_callback(), 20)
  
    