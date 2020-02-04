# Camlp5

Camlp5 is a preprocessor-pretty-printer of ocaml.

It is (theoretically) compatible with all versions of ocaml from 1.07
to 4.10.0 (when they compile), and jocaml 3.12.0 to 3.12.1, but
maintainers only test against version of ocaml >= 4.00.0.

This Camlp5 version is 7.11.

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

The directory doc/htmlp contains the sources of the full documentation.
To build it, cd doc/htmlp, and:
* for its html version, type "make", result in directory ../html
* for its latex version, type "make tex", result camlp5.tex
* for its ps version, type "make ps", result camlp5.ps
* for its pdf version, type "make pdf", result camlp5.pdf
* for its info version, type "make info", result camlp5.info*

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
