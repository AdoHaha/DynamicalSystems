#!/usr/bin/env python3
"""Screen production Lean code for placeholders, ignoring comments and strings.

This source check complements the kernel-level transitive audit in
DynamicalSystemsTest/Foundations/Axioms.lean; it does not replace that audit.
Pass --ref COMMIT to inspect the corresponding committed production tree.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parent.parent
FORBIDDEN = {"sorry", "admit", "proof_wanted", "axiom"}


def code_without_comments_and_strings(source: str) -> str:
    """Blank comments and quoted strings while preserving line numbers.

    Lean block comments nest. Ordinary strings allow escapes, and raw strings
    have the form r#"..."# with any number of hashes.
    """
    output = list(source)
    index = 0
    while index < len(source):
        start = index
        if source.startswith("--", index):
            end = source.find("\n", index)
            index = len(source) if end < 0 else end
        elif source.startswith("/-", index):
            index += 2
            depth = 1
            while index < len(source) and depth:
                if source.startswith("/-", index):
                    depth += 1
                    index += 2
                elif source.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
        else:
            raw = re.match(r'r(#+)"', source[index:]) if source[index] == "r" else None
            if raw:
                terminator = '"' + raw.group(1)
                end = source.find(terminator, index + len(raw.group(0)))
                index = len(source) if end < 0 else end + len(terminator)
            elif source[index] == '"':
                index += 1
                while index < len(source):
                    char = source[index]
                    index += 1
                    if char == "\\":
                        index = min(index + 1, len(source))
                    elif char == '"':
                        break
            else:
                index += 1
                continue
        for position in range(start, index):
            if output[position] != "\n":
                output[position] = " "
    return "".join(output)


def sources(ref: str | None):
    if ref is None:
        for path in sorted((ROOT / "DynamicalSystems").rglob("*.lean")):
            yield path.relative_to(ROOT).as_posix(), path.read_text(encoding="utf-8")
    else:
        paths = subprocess.check_output(
            ["git", "ls-tree", "-r", "--name-only", ref, "--", "DynamicalSystems"],
            cwd=ROOT, text=True,
        ).splitlines()
        for path in paths:
            if path.endswith(".lean"):
                yield path, subprocess.check_output(
                    ["git", "show", f"{ref}:{path}"], cwd=ROOT, text=True,
                )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ref", help="inspect this Git revision instead of the working tree")
    args = parser.parse_args()
    counts: Counter[str] = Counter()
    inspected = 0
    for path, source in sources(args.ref):
        inspected += 1
        code = code_without_comments_and_strings(source)
        for token in re.finditer(r"[A-Za-z_][A-Za-z0-9_']*", code):
            if token.group() in FORBIDDEN:
                counts[token.group()] += 1
                line = code.count("\n", 0, token.start()) + 1
                print(f"{path}:{line}: active {token.group()}")
    summary = ", ".join(f"{name}={counts[name]}" for name in sorted(FORBIDDEN))
    print(f"Inspected {inspected} production Lean files: {summary}.")
    return 1 if counts else 0


if __name__ == "__main__":
    raise SystemExit(main())
