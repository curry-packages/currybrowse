CurryBrowser
============

A tool to browse through the modules and functions of a Curry program,
show them in various formats, and analyze their properties.

Note:
Functionalities of the Browser marked by "(DOT)" require an
installed graph visualization tool (dot, see below), otherwise
they have no effect.

Developed by
Michael Hanus (CAU Kiel, Germany, mh@informatik.uni-kiel.de)


Software requirements:
----------------------

* A Curry implementation like PAKCS (https:/www.informatik.uni-kiel.de/~pakcs)
  or KiCS2 (https://www-ps.informatik.uni-kiel.de/kics2/)
  for compiling and running the browser

* Tcl/Tk (for running the browser GUI)
  https://www.tcl.tk/

* dot/ghostview (for visualizing import graphs):
  https://www.graphviz.org/

  Adapt definition of dot viewer according to your local installation
  with the menu "Settings". If you don't have this software,
  you can't use the browser functions marked by "(DOT)".
