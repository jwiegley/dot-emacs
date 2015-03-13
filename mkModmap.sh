#!/bin/sh

# Use graphmod (from hackage) to generate a diagram of the module interrelationships

#graphmod src/*.hs src/*/*/*.hs | dot -Tpng > mod.png
graphmod refactorer/*.hs refactorer/*/*.hs refactorer/*/*/*.hs  | dot -Tpng > mod.png
