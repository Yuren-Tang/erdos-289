#!/usr/bin/env python3
"""Reject unfinished or trusted-by-fiat declarations in the package source.

This is a *hygiene* check, not a trust check: it rules out the syntactic forms
that would let an unproved statement enter the build.  The transitive trust
check is the pinned `#print axioms` audit in `Audit.lean`.

Comments and string literals are stripped first, so prose that discusses
`sorry` or `axiom` — as the documentation of the audit itself must — does not
trip the scan.  Lean block comments nest, so the stripper tracks depth.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

ROOTS = [
    "AffineCorrection",
    "Erdos289",
    "Erdos289Test",
    "IndependentTransversals",
    "LeanPool",
]
EXTRA = [
    "AffineCorrection.lean",
    "Erdos289.lean",
    "Erdos289Test.lean",
    "IndependentTransversals.lean",
    "LeanPool.lean",
    "Audit.lean",
]

FORBIDDEN = re.compile(
    r"(?<![A-Za-z0-9_.'])"
    r"(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)"
    r"(?![A-Za-z0-9_'])"
)


def strip_comments(text: str) -> str:
    """Blank out nested block comments, line comments and string literals."""
    out = []
    i, n, depth = 0, len(text), 0
    while i < n:
        two = text[i : i + 2]
        if depth > 0:
            if two == "/-":
                depth += 1
                out.append("  ")
                i += 2
            elif two == "-/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif two == "/-":
            depth = 1
            out.append("  ")
            i += 2
        elif two == "--":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    out.append(" ")
                    i += 1
                    if i < n:
                        out.append(" ")
                        i += 1
                    continue
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
            if i < n:
                out.append(" ")
                i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def files() -> list[pathlib.Path]:
    found: list[pathlib.Path] = []
    for r in ROOTS:
        found.extend(sorted((ROOT / r).rglob("*.lean")))
    found.extend(ROOT / f for f in EXTRA)
    return found


def main() -> None:
    failures = []
    for path in files():
        if not path.exists():
            sys.exit(f"expected source file is missing: {path}")
        stripped = strip_comments(path.read_text())
        for lineno, line in enumerate(stripped.splitlines(), start=1):
            match = FORBIDDEN.search(line)
            if match:
                rel = path.relative_to(ROOT)
                original = path.read_text().splitlines()[lineno - 1]
                failures.append(f"{rel}:{lineno}: `{match.group(1)}` in: {original.strip()}")

    if failures:
        for f in failures:
            print(f"::error::{f}")
        sys.exit(f"{len(failures)} forbidden declaration form(s) found")

    print(
        f"source scan: {len(files())} files, no sorry, admit, axiom, "
        "native_decide, unsafe, implemented_by or extern"
    )


if __name__ == "__main__":
    main()
