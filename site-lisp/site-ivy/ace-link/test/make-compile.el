(setq files '("ace-link.el"))
(setq byte-compile--use-old-handlers nil)
(mapc #'byte-compile-file files)
