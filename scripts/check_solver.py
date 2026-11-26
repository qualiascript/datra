#!/usr/bin/env python3
"""Check the polymorphic datatype selectors used by LiquidHaskell."""
import subprocess


QUERY = """
(set-logic ALL)
(declare-datatypes ((Pagination 3))
  ((par (S O F)
    ((paginationParameters (scope S) (origin O) (final F))
     (pagination (pageElements Int))))))
(declare-datatypes ((Atlas 5))
  ((par (A S D O F)
    ((atlasParameters (atlasScope A) (pageScope S) (data D) (first O) (last F))
     (atlas (storedPagination (Pagination S O F)) (storedData Int))))))
(declare-const owner (Atlas Int Int Int Int Int))
(assert (= (pageElements (storedPagination owner)) 1))
(check-sat)
(push)
(assert (= (pageElements (storedPagination owner)) 2))
(check-sat)
(pop)
"""


def check():
    try:
        result = subprocess.run(
            ["z3", "-in"], input=QUERY, text=True, capture_output=True,
            timeout=15, check=False)
    except (OSError, subprocess.TimeoutExpired) as error:
        raise SystemExit(f"Cannot check Z3: {error}") from error
    if result.returncode or result.stdout.split() != ["sat", "unsat"]:
        raise SystemExit(
            "Z3 failed the nested polymorphic selector check. "
            "Use the CI-pinned Z3 4.15.4.\n" + result.stdout + result.stderr)
    print("Z3: nested polymorphic selectors verified")


if __name__ == "__main__":
    check()
