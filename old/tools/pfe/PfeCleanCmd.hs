module PfeCleanCmd where
import PfeParse(noArgs)

pfeCleanCmd clean = [("clean", (noArgs clean,"remove cache files"))]
