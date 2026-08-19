#!/usr/bin/env python3
"""Extract the fully qualified names of the package's public declarations.

The trust audit is generated from this list rather than from a hand-maintained
file, so a new public theorem cannot be added without also being audited.  A
declaration counts as public when it is declared without the `private` modifier
in one of the package's own modules; `Erdos289Test/` is excluded because it is
a consumer, and the vendored directories are excluded because their upstream
statements are recorded in `THIRD_PARTY.md` and audited through the
project-facing theorems that use them.

Extraction is deliberately syntactic.  A mistake cannot go unnoticed: a wrong
name makes `#print axioms` fail and turns the build red.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SOURCE_DIRS = ("Erdos289", "AffineCorrection")

DECL = re.compile(
    r"^(?P<private>private\s+)?(?:protected\s+)?(?:noncomputable\s+)?"
    r"(?:theorem|lemma|def|abbrev)\s+(?P<name>[A-Za-z_][A-Za-z0-9_.'!?₀-₉]*)"
)
NAMESPACE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")
END = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_.']*)\s*$")


def declarations_of(path: pathlib.Path) -> list[str]:
    names: list[str] = []
    stack: list[str] = []
    in_block_comment = False
    for raw in path.read_text().splitlines():
        line = raw.rstrip()
        if in_block_comment:
            if "-/" in line:
                in_block_comment = False
            continue
        if line.lstrip().startswith("/-"):
            if "-/" not in line:
                in_block_comment = True
            continue
        m = NAMESPACE.match(line)
        if m:
            stack.append(m.group(1))
            continue
        m = END.match(line)
        if m and stack and stack[-1] == m.group(1):
            stack.pop()
            continue
        m = DECL.match(line)
        if m and not m.group("private"):
            prefix = ".".join(stack)
            names.append(f"{prefix}.{m.group('name')}" if prefix else m.group("name"))
    return names


def public_declarations() -> list[str]:
    out: list[str] = []
    for directory in SOURCE_DIRS:
        base = ROOT / directory
        for path in sorted(base.rglob("*.lean")):
            out.extend(declarations_of(path))
        aggregate = ROOT / f"{directory}.lean"
        if aggregate.exists():
            out.extend(declarations_of(aggregate))
    seen: set[str] = set()
    unique: list[str] = []
    for name in out:
        if name not in seen:
            seen.add(name)
            unique.append(name)
    return unique


if __name__ == "__main__":
    names = public_declarations()
    print("\n".join(names))
    print(f"-- {len(names)} public declarations", file=sys.stderr)
