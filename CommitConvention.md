Git Commit Convention
=====================

We are using the following convention for writing git commit messages.
For pull requests, make sure the pull request title and description follow this
convention, as the squash-merge commit will inherit title and body from the
pull request.

This convention is based on the [one from the Lean 4 project](https://github.com/leanprover/lean4/blob/master/doc/dev/commit_convention.md).

Format of the commit message
----------------------------

    <type>: <subject>
    <NEWLINE>
    <body>
    <NEWLINE>
    <footer>

``<type>`` is:

 - chore (adapting to upstream changes, CI, project infrastructure)
 - doc (documentation)
 - feat (new feature)
 - fix (bug fix)
 - perf (performance improvement, optimization)
 - refactor (reorganization, reimplementation)
 - style (formatting, indentation, etc.)
 - test (adding updating tests)

``<subject>`` has the following constraints:

 - use imperative, present tense: "change" not "changed" nor "changes"
 - do not capitalize the first letter
 - no period at the end of the subject line

``<body>`` has the following constraints:

 - just as in ``<subject>``, use imperative, present tense
 - includes motivation for the change and contrasts with previous behavior

``<footer>`` is optional and may contain these items:

 - Breaking changes: All breaking changes have to be mentioned in footer with the description of the change, justification and migration notes
 - Referencing issues: Closed bugs should be listed on a separate line in the footer prefixed with "Closes" keyword like this: "Closes #123, #456"
 - Coauthors

Examples
--------

fix: add declarations for operator<<(std::ostream&, expr const&) and operator<<(std::ostream&, context const&) in the kernel

The actual implementation of these two operators is outside of the kernel.
They are implemented in the file 'library/printer.cpp'.
We declare them in the kernel to prevent the following problem.
Suppose there is a file 'foo.cpp' that does not include 'library/printer.h', but contains

    expr a;
    ...
    std::cout << a << "\n";
    ...

The compiler does not generate an error message.
It silently uses the operator bool() to coerce the expression into a Boolean.
This produces counter-intuitive behavior, and may confuse developers.
