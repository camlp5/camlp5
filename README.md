# Camlp5

Camlp5 is a preprocessor-pretty-printer of OCaml.

It is compatible with all versions of OCaml from 4.05.0 thru 4.14.0.
Previous versions of Camlp5 have supported OCaml versions down to 1.07
and jocaml 3.12.0 to 3.12.1, but this version cuts off support at
4.05.0.  Camlp5 is heavily tested with OCaml versions from 4.10.0
forward, with an extensive and ever-growing testsuite.

This Camlp5 version is 8.00.04.  NOTE WELL that this is an **new**
release (very different from the 7.xx releases), and as such, may
break your code.  If it does, please do reach out to me, and I'll be
happy to help upgrade it.  I'm still working on the documentation, but
.... that could take a while, so I figured I had better get this out
and find out where code breaks, so I can fix that.

## Documentation: Installation, Testsuite, Tutorial

Since most OCaml users will install Camlp5 via opam, all the
documentation has been moved over to Sphinx/RST, and is available in
`doc/rst/_build` as well as
[on ReadTheDocs](https://camlp5.readthedocs.io/en/latest/).

- Introduction: `doc/rst/_build/intro.html`, [on ReadTheDocs](https://camlp5.readthedocs.io/en/latest/intro.html).

  This introduction explains how to use Camlp5 from the commandline
  and toplevel: compiling files, loading into toplevel, selecting
  syntax (original or revised).  I'd recommend starting here before
  trying one of the tutorials.

- Building, Requirements & Installation: `doc/rst/_build/building.html`, [on ReadTheDocs](https://camlp5.readthedocs.io/en/latest/building.html).

  This covers building Camlp5 "manually", as well as building the
  documentation, testsuite, and tutorial examples.

- Tutorials (using Camlp5): `doc/rst/_build/tutorial-language-processing.html`, [on ReadTheDocs](https://camlp5.readthedocs.io/en/latest/tutorial-language-processing.html).

  This covers how to use Camlp5 to write new language processors (the
  running example of a calculator with parsing, pretty-printing, and
  evaluation), using Camlp5 infrastructure, as well as interfacing with
  Ocamllex.

- Tutorials (extending OCaml Syntax): `doc/rst/_build/tutorial-extending-camlp5.html`, [on ReadTheDocs](https://camlp5.readthedocs.io/en/latest/tutorial-extending-camlp5.html).

  This covers how to use Camlp5 to write new syntax-extensions for
  Ocaml, using the example new syntax ``sum 1 ; 2 end``.

Some tutorials are provided in both original and revised syntax:
eventually all will be provided in both forms.

### Outdated HTML Documentation

The directory doc/htmlp contains the sources of outdated HTML
documentation.  It will be removed once the Sphinx documentation is
fully updated.

To build it, cd doc/htmlp, and:
* for its html version, type "make", result in directory ../html
* for its latex version, type "make tex", result camlp5.tex
* for its ps version x-rtype "make ps", result camlp5.ps
* for its pdf version, type "make pdf", result camlp5.pdf
* for its info version, type "make info", result camlp5.info*

## Problems

If you have problems compiling your source files with this version of
Camlp5, please contact me (Chet Murthy <chetsky@gmail.com>) and I'll
help you resolve them.  I can't promise, but it's likely I can just
fork your repo, fix the problem, and send you a PR.

For really old code, the reason can be that there the new type
'location' is now abstract. Consider looking at the file UPGRADING.

## Author(s)

Originally written by Daniel de Rauglaudre <daniel.roglo@free.fr>.
Maintenance and upgrades by Chet Murthy <chetsky@gmail.com>.

All bugs are my (Chet's) fault, all good ideas are Daniel's.
