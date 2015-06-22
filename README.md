# README                                                                                                                    
### This is aria2, a major mode for controlling [aria2c](http://aria2.sourceforge.net/) downloader ###
Currrently supported download types are: bittorrent, magnet, meta4, ftp, http, https files (basically what aria2c supports).
There is no support for changing global or per-download options, but this is planned.

This mode tries to work well with evil-mode, just set *aria2-add-evil-quirks* to *t*.

### How does it look like? ###
![aria2-mode.png](https://bitbucket.org/repo/enngMR/images/3703075290-aria2-mode.png)

### How do I get set up? ###

#### El-get ####

```
#!emacs-lisp

  (push
   `(:name aria2
           :type git
           :url "https://bitbucket.org/ukaszg/aria2.git")
   el-get-sources)

  (el-get 'sync '(aria2))
```

#### Packages ####
Avaliable at Melpa [![MELPA](http://melpa.org/packages/aria2-badge.svg)](http://melpa.org/#/aria2)