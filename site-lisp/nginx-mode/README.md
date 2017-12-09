# nginx-mode.el --- major mode for editing nginx config files

Copyright 2010 Andrew J Cosgriff <andrew@cosgriff.name>

* Author: Andrew J Cosgriff <andrew@cosgriff.name>
* Maintainer: Andrew J Cosgriff <andrew@cosgriff.name>
* Created: 15 Oct 2010
* Keywords: nginx

available from http://github.com/ajc/nginx-mode

[![MELPA](https://melpa.org/packages/nginx-mode-badge.svg)](https://melpa.org/#/nginx-mode)

Licensed under the [GPL version 2](http://www.gnu.org/licenses/) or later.

# Commentary

This is a quick mode for editing Nginx config files, as I didn't find
anything else around that did quite this much.

Many thanks to the authors of `puppet-mode.el`, from where I found a
useful indentation function that I've modified to suit this situation.

Put this file into your `load-path` and the following into your `~/.emacs`:
```lisp
  (require 'nginx-mode)
```

The mode automatically activates for:

1. Files, called `nginx.conf`
2. Files ending in `.conf` under `nginx` directory

If you want `sites-enabled` dir, add this to `~/.emacs` (not done by
default, because can be shadowed by `apache-mode`):

```lisp
(add-to-list 'auto-mode-alist '("/nginx/sites-\\(?:available\\|enabled\\)/" . nginx-mode))
```
