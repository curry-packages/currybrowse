CurryBrowser
============

The CurryBrowser is a generic analysis environment for the declarative
multi-paradigm language Curry. The CurryBrowser supports browsing through
the program code of an application written in Curry, i.e., the main
module and all directly or indirectly imported modules. Each module
can be shown in different formats (e.g., source code, interface,
intermediate code) and, inside each module, various properties of
functions defined in this module can be analyzed.

In order to support the integration of various program analyses,
the CurryBrowser has a generic interface to connect local and global
analyses implemented in Curry. The tool is completely implemented
in Curry using libraries for GUI programming and meta-programming.

After installing the CurryBrowser with the Curry package manager,
it can be easily invoked inside interactive environment of
the Curry implementations
[PAKCS](https://www.informatik.uni-kiel.de/~pakcs/) or
[KiCS2](https://www-ps.informatik.uni-kiel.de/kics2)
by the command `:browse`.

_Note:_
Functionalities of the CurryBrowser marked by `(DOT)` require an
installed graph visualization tool (`dot`, see below), otherwise
they have no effect.

Further details can be found in a
[paper on CurryBrowser](http://www.informatik.uni-kiel.de/~mh/papers/WLPE06.html)

![Snapshot of the CurryBrowser GUI](https://cpm.curry-lang.org/PACKAGES/currybrowse-3.0.0/images/currybrowser.jpg)


Software requirements:
----------------------

* A Curry implementation like [PAKCS](https:/www.informatik.uni-kiel.de/~pakcs)
  or [KiCS2](https://www-ps.informatik.uni-kiel.de/kics2/)
  to install and run the browser.
* [Tcl/Tk](https://www.tcl.tk/) for running the browser GUI.
* [dot](https://www.graphviz.org/) to visualize dependency graphs.
  Adapt the definition of dot viewer according to your local installation
  with the menu `Settings`. If this software is not installed,
  one can not use the browser functions marked by `(DOT)`.
