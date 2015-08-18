These are just examples that I use for testing lentic interactively.
Each one tests a single transformation. There are some big examples aslo for
performance testing.

Most of these files define their configuration in a file local variable.
Sensible in this case, because we have lots of files of different types in one
directory. In practice, there is likely to be a single kind of lentic file in
one directory, so this would be set with a dir-local variable. A couple of the
files have no configuration, and will use the default configuration.

The real test case data is in dev-resources.
