==============================
Building and Installing Camlp5
==============================

Most Camlp5 users will install via ``opam``, but for developers and
those investigating bugs, as well as those wishing to build
documentation and the testsuite, here are instructions.

.. contents::
  :local:

Requirements
============

To build Camlp5 you need the ocaml compiler installed. It must be
accessible in the path.  The Sphinx/RST documentation and testsuite
require other packages (Ocaml, Python, Perl) to be installed, and this
is described below.

Installation
============

In the nearly-ubiquitious fashion of open-source, you will run (in the
shell)

::

   ./configure
   make
   make install

``configure`` has arguments allowing you to specify installation
directories and other options.

Detailed Steps (that are almost never needed)
#############################################

Alternatively, you can decompose the operations into:

::

   $ make out

Then, to make camlp5 check itself:

::

   $ make bootstrap

Further, to make the native-code library:

::

   $ make opt

At end, to make more native-code programs:

::

   $ make opt.opt

3) The binaries are installed by typing:

::

   $ make install

or, if you install to a system location but are not an administrator

::

   $ sudo make install

Building Sphinx Documentation
=============================

There are two forms of documentation: HTML and RST (ReStructured Text)
(for Sphinx).  From this release forward, the Sphinx documentation
will be updated and improved; the HTML documentation will soon be
removed.

The directory doc/rst contains the sources of the RST documentation.  To build it requires:

* ``python3`` (tested with version 3.6.9)
* Sphinx (tested with version 3.0.3)
* sphinx-rtd-theme (tested with 0.4.3)

The easiest way to do that is to use Python's ``venv`` and install
them with ``pip3`` (e.g.):


::

   python3 -m venv ~/Sphinx
   source ~/Sphinx/bin/activate
   pip3 install sphinx-rtd-theme

Then

::

   make -C doc/rst all

This creates the Sphinx documentation in ``doc/rst/_build``.

Testsuite
=========

There is a rather extensive testsuite (to which any suggestions or
contributions are welcome) in ``testsuite``.  It assumes only that
camlp5 has been successfully built, but not installed.  To build/run
it, one must install a number of packages:

* `rresult`
* `fmt`
* `pcre`
* `ounit2`
* `patdiff`
* `IPC::System::Simple`
* `String::ShellQuote`

On Debian/Ubuntu systems, the Perl packages can be installed with:

::

   apt-get install libstring-shellquote-perl libipc-system-simple-perl
   
and using opam:

::  

  opam install rresult fmt pcre ounit2 patdiff

These packages are *not* required to build/install camlp5, but only to
build and run the testsuite.  However, for add-on packages (like
``pa_ppx``) they are required, and so it is probably wisest to go
ahead and install them now.

Then to build/run it:

::
   
   make -C testsuite all-tests

Tutorial examples
=================

There are a number of tutorial examples in the directory
``tutorials``; some come with tests.  They assume that camlp5 has been
installed (and hence, do not reference the build-tree).  They also
assume that the testsuite prereqs have been installed.  To build (and
run) the tutorial examples:

::

   make -C tutorials all
   make -C tutorials test

The Sphinx/RST documentation uses these examples to explain how to
write code using Camlp5.

For Camlp5 Developers
=====================

The file DEVEL gives information for people who want to make changes
in Camlp5, or who are just curious of how it is implemented. The same
explanations are also in the chapter "Camlp5 sources" in the documentation.

.. container:: trailer
