#!/usr/bin/env python3
"""Create the full preprint TeX source with a formatted Lean appendix."""

from __future__ import annotations

import argparse
from pathlib import Path


LISTINGS_PREAMBLE = r"""
\usepackage{xcolor}
\usepackage{listings}

\definecolor{leanKeyword}{HTML}{6D28D9}
\definecolor{leanComment}{HTML}{356B45}
\definecolor{leanString}{HTML}{9A3412}
\definecolor{leanRule}{HTML}{CBD5E1}
\definecolor{leanBackground}{HTML}{F8FAFC}

\lstdefinelanguage{Lean}{
  sensitive=true,
  morekeywords={
    abbrev,attribute,by,case,class,def,deriving,else,end,example,extends,
    for,forall,fun,have,if,import,in,inductive,infix,infixl,infixr,instance,
    let,match,namespace,noncomputable,opaque,open,private,protected,section,
    structure,syntax,theorem,then,universe,variable,where,with
  },
  morecomment=[l]{--},
  morecomment=[s]{/-}{-/},
  morestring=[b]"
}

\lstdefinestyle{leanSource}{
  language=Lean,
  basicstyle=\ttfamily\scriptsize,
  keywordstyle=\color{leanKeyword}\bfseries,
  commentstyle=\color{leanComment}\itshape,
  stringstyle=\color{leanString},
  backgroundcolor=\color{leanBackground},
  rulecolor=\color{leanRule},
  frame=single,
  framerule=0.4pt,
  numbers=left,
  numberstyle=\tiny\color{gray},
  numbersep=8pt,
  xleftmargin=2.2em,
  framexleftmargin=1.8em,
  breaklines=true,
  breakatwhitespace=false,
  columns=fullflexible,
  keepspaces=true,
  showstringspaces=false,
  tabsize=2,
  captionpos=b
}
"""

LEAN_APPENDIX = r"""
\clearpage
\appendix
\section{Lean Formalization}

The following is the complete Lean source corresponding to the mathematical
development above.

\lstinputlisting[
  style=leanSource,
  caption={Complete Lean formalization of DaTra},
  label={lst:datra-lean}
]{datra_code.lean}
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("input", type=Path, help="extracted preprint TeX source")
    parser.add_argument("output", type=Path, help="full preprint TeX destination")
    args = parser.parse_args()

    source = args.input.read_text(encoding="utf-8")
    if "\\begin{document}" not in source or "\\end{document}" not in source:
        parser.error(f"{args.input} is not a complete LaTeX document")

    source = source.replace(
        "\\begin{document}",
        LISTINGS_PREAMBLE + "\n\\begin{document}",
        1,
    )
    source = source.replace(
        "\\end{document}",
        LEAN_APPENDIX + "\n\\end{document}",
        1,
    )
    args.output.write_text(source, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
