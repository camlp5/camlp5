# Camlp5

Camlp5 is a preprocessor-pretty-printer of ocaml.

It is (theoretically) compatible with all versions of ocaml from 1.07
to 4.11.0 (when they compile), and jocaml 3.12.0 to 3.12.1, but
maintainers only test against versions of ocaml >= 4.00.0.

This Camlp5 version is 8.00-alpha01.

## Requirements

You need the ocaml compiler installed. It must be accessible in the path.

## Installation

1) First, run the "configure" script by typing:
```shell
   ./configure
```
The `configure` script has a few options. Use the `--help` option to get a
list and short description of each option.

2) It creates a Makefile, which can be invoked by:
```shell
   make
```

Alternatively, you can decompose the operations into:
```shell
   make out
```
Then, to make camlp5 check itself:
```shell
   make bootstrap
```
Further, to make the native-code library:
```shell
   make opt
```
At end, to make more native-code programs:
```shell
   make opt.opt
```

3) The binaries are installed by typing:
```shell
   make install
```
or, if you install to a system location but are not an administrator
```
   sudo make install
```

## Documentation

There are two forms of documentation: HTML and RST (ReStructured Text)
(for Sphinx).  We're switching to RST, but for now will maintain both
in parallel.

The directory doc/htmlp contains the sources of the HTML documentation.
To build it, cd doc/htmlp, and:
* for its html version, type "make", result in directory ../html
* for its latex version, type "make tex", result camlp5.tex
* for its ps version x-rtype "make ps", result camlp5.ps
* for its pdf version, type "make pdf", result camlp5.pdf
* for its info version, type "make info", result camlp5.info*

The directory doc/rst contains the sources of the RST documentation.  To build it requires:
*`python3` (tested with version 3.6.9)
* Sphinx (tested with version 3.0.3)
* sphinx-rtd-theme (tested with 0.4.3)

The easiest way to do that is to use Python's `venv` and install them with `pip3`.  Then
```
make -C doc/rst all
```

This creates the Sphinx documentation in `doc/rst/_build`.

## Developers

The file DEVEL gives information for people who want to make changes
in Camlp5, or who are just curious of how it is implemented. The same
explanations are also in the chapter "Camlp5 sources" in the documentation.

## Problems

If you have problems to compile your source files with this version of
Camlp5, the reason can be that there the new type 'location' is now
abstract. Consider looking at the file UPGRADING.

## Author

Daniel de Rauglaudre <daniel.roglo@free.fr>
