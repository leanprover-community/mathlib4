# Junie Guidelines

You might encounter syntax errors in the lean code, and asking to access the structure of files might fail. This is
simply because the plugin used to provide lean4 support in PyCharm does not understand certain syntax aspects of
modern lean4.

All lean code in this repository actually compiles, so there is no need to worry about apparently broken code at all.

If you can't access the structure of a file, compensate by reading the raw file instead.

## Guidelines for comments and documentation
- Comments and docstrings should be written in English, but the project does not have a preference for either UK nor
  US English. Within a single file, sticking to only one of these is probably advisable.
- Comments and docstrings that consist solely of a sentence fragment, as opposed to one or more complete sentences,
  do not require a capital letter at the beginning and punctuation marks at the end.
- Lines should not exceed 100 characters in length.
- Comments and docstrings should be written in the style of the [lean community documentation style](https://leanprover-community.github.io/contribute/doc.html).