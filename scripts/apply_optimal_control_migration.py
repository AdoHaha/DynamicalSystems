#!/usr/bin/env python3
"""M0 — mechanical FQN rename for the optimal-control concept migration.

For every map entry whose ``change`` is ``rename`` or ``rename-and-move`` this
script

* rewrites qualified occurrences of ``old_fqn`` (and of campaign-qualified
  suffixes such as ``K3.uncurryLagrangian``) to the target (longest first,
  word-boundary aware, idempotent),
* rewrites ``namespace`` / ``end`` lines whose namespace is campaign
  scaffolding (``KirkMedhin``, ``KirkMedhin.K1``, ``K1…``, ``K3…`` …),
* rewrites the declaration site itself so the resulting fully-qualified name
  is the target (handles leaf renames and namespace moves), and
* rewrites bare (relative) references of a declaration whose relative name
  changed, in every file that can see it through the shared campaign
  namespace or an ``open``.

Physical file moves are intentionally *not* performed here; they are left to
the later M1…M6 tasks.  Declarations affected by ``rename-and-move`` are
renamed in place (they end up in their target namespace, which is enough for
the build) but stay in their original module.

Usage::

    python3 scripts/apply_optimal_control_migration.py --dry-run
    python3 scripts/apply_optimal_control_migration.py
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from collections import Counter, defaultdict

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
WORKTREE = os.path.dirname(SCRIPT_DIR)

# Fallback: the canonical absolute location of the map from the task brief.
FALLBACK_MAP = "/home/igor/zabawy/auto_automatyk/notes/reviews/optimal_control_declaration_map.json"

LOG_BASENAME = "M0_RENAME_LOG.txt"

SCAN_DIRS = ("DynamicalSystems", "DynamicalSystemsTest", "docs")
UMBRELLA = "DynamicalSystems.lean"

IDENT = r"A-Za-z0-9_'"

NS_LINE_RE = re.compile(r"^(\s*)(namespace|end)\s+([A-Za-z0-9_.']+)\s*$")
BARE_END_RE = re.compile(r"^(\s*)end\s*$")
OPEN_TOKEN_RE = re.compile(r"[A-Za-z0-9_']+(?:\.[A-Za-z0-9_']+)*")


# ---------------------------------------------------------------------------
# Namespace helpers
# ---------------------------------------------------------------------------

def is_campaign_ns(ns: str) -> bool:
    """Namespaces that are campaign scaffolding / provenance prefixes."""
    if ns == "KirkMedhin" or ns.startswith("KirkMedhin."):
        return True
    first = ns.split(".", 1)[0]
    if first.startswith("K1") or first.startswith("K3"):
        return True
    if ns == "PMPNotSufficient":
        return True
    return False


def _is_marker(part: str) -> bool:
    return (part == "KirkMedhin" or part.startswith("K1")
            or part.startswith("K3") or part == "PMPNotSufficient")


def campaign_suffixes(fqn: str):
    """Qualified suffixes of ``fqn`` usable from inside a campaign scope.

    ``KirkMedhin.K3.uncurryLagrangian`` yields ``K3.uncurryLagrangian``;
    ``KirkMedhin.WeakCoV.foo`` yields ``WeakCoV.foo``.  Only suffixes starting
    at a campaign marker or at the concept namespace directly under the
    campaign root are emitted: nested namespaces (``IsFinitePiecewiseC1`` …)
    keep resolving correctly after the parent namespace is renamed and must not
    be rewritten.  Bare (single-component) suffixes are handled separately
    because they need namespace-visibility filtering.
    """
    parts = fqn.split(".")
    n = len(parts)
    if parts and parts[0] == "KirkMedhin":
        plen = 2 if (n > 1 and _is_marker(parts[1])) else 1
    else:
        plen = 1
    idxs = {0, plen}
    idxs.update(i for i, p in enumerate(parts) if _is_marker(p))
    out = []
    for i in sorted(idxs):
        if 0 <= i < n:
            suf = ".".join(parts[i:])
            if "." in suf:
                out.append(suf)
    return out


def parse_stacks(lines):
    """Return ``{lineno: tuple(stack)}`` for the namespace stack *at* a line."""
    stack: list[str] = []
    stacks: dict[int, tuple[str, ...]] = {}
    for i, line in enumerate(lines):
        stacks[i + 1] = tuple(stack)
        m = NS_LINE_RE.match(line)
        if m:
            kw, ns = m.group(2), m.group(3)
            if kw == "namespace":
                stack.append(ns)
            else:
                if stack and stack[-1] == ns:
                    stack.pop()
                elif ns in stack:
                    while stack and stack[-1] != ns:
                        stack.pop()
                    if stack:
                        stack.pop()
        elif BARE_END_RE.match(line) and stack:
            stack.pop()
    return stacks


def relative_name(old_fqn: str, stack) -> str:
    rel = old_fqn
    for s in stack:
        if rel.startswith(s + "."):
            rel = rel[len(s) + 1:]
    return rel


def suffix_match(target: str, suffix: str):
    """If ``target`` is ``base + "." + suffix`` return ``base`` ('' if equal)."""
    if not suffix:
        return None
    if target == suffix:
        return ""
    if target.endswith("." + suffix):
        return target[: -(len(suffix) + 1)]
    return None


def file_ns_map(entries, stacks):
    """Per-file map campaign namespace -> new namespace (majority vote)."""
    cands: dict[str, Counter] = defaultdict(Counter)
    for e in entries:
        st = stacks.get(e["source_line"], ())
        for i, ns in enumerate(st):
            if not is_campaign_ns(ns):
                continue
            rest = st[i + 1:]
            oldrel = relative_name(e["old_fqn"], st)
            suffix = ".".join(rest + (oldrel,)) if (rest or oldrel) else ""
            base = suffix_match(e["target_fqn"], suffix)
            if base is not None:
                cands[ns][base] += 1
    return {ns: c.most_common(1)[0][0] for ns, c in cands.items()}


def collect_files():
    paths = []
    for d in SCAN_DIRS:
        root = os.path.join(WORKTREE, d)
        for dirpath, _dirnames, filenames in os.walk(root):
            for fn in filenames:
                if fn.endswith(".lean"):
                    paths.append(os.path.relpath(os.path.join(dirpath, fn), WORKTREE))
    umbrella = os.path.join(WORKTREE, UMBRELLA)
    if os.path.exists(umbrella):
        paths.append(UMBRELLA)
    return sorted(set(paths))


def line_contexts(lines, stacks):
    """Namespace names in scope and namespaces pulled in by ``open``."""
    nss = {'.'.join(st) for st in stacks.values() if st}
    opened = set()
    for line in lines:
        s = line.strip()
        if s.startswith("open "):
            for tok in OPEN_TOKEN_RE.findall(s[len("open "):]):
                opened.add(tok)
    return nss, opened


def visible_in(old_ns: str, nss, opened) -> bool:
    if not old_ns:
        return True
    for ns in nss:
        if ns == old_ns or ns.startswith(old_ns + "."):
            return True
    anc = old_ns
    while True:
        if anc in opened:
            return True
        if "." not in anc:
            break
        anc = anc.rsplit(".", 1)[0]
    return False


# ---------------------------------------------------------------------------
# Main transform
# ---------------------------------------------------------------------------

def transform_file(relpath, file_entries, qual_pat, qual_target, bare_pairs,
                   module_pat, module_rename, global_ns_map, log, dry_run):
    abspath = os.path.join(WORKTREE, relpath)
    with open(abspath, encoding="utf-8") as fh:
        original = fh.read()
    lines = original.splitlines(keepends=False)
    trailing_newline = original.endswith("\n")

    stacks = parse_stacks(lines)
    local_ns_map = file_ns_map(file_entries, stacks)

    def resolve_ns(ns: str) -> str:
        # The global map (majority across all files) keeps sibling modules in
        # the same namespace; the local map is only a fallback.
        if ns in global_ns_map:
            return global_ns_map[ns]
        if ns in local_ns_map:
            return local_ns_map[ns]
        return "" if is_campaign_ns(ns) else ns

    def qual_sub(line):
        if qual_pat is None or not qual_pat.search(line):
            return line

        def repl(mo):
            old = mo.group(0)
            new = qual_target[old]
            if new != old:
                log.append(f"{relpath}: qualified {old} -> {new}")
            return new

        return qual_pat.sub(repl, line)

    # ------------------------------------------------------------------
    # Pass over lines: module paths, namespace rewrite, qualified names.
    # ------------------------------------------------------------------
    ns_stack: list[str] = []
    out = []
    for i, line in enumerate(lines):
        lineno = i + 1
        if module_pat is not None and module_pat.search(line):
            def mod_repl(mo):
                src = mo.group(0)
                dst = module_rename[src]
                log.append(f"{relpath}:{lineno}: module {src} -> {dst}")
                return dst
            line = module_pat.sub(mod_repl, line)

        m = NS_LINE_RE.match(line)
        if m:
            indent, kw, ns = m.group(1), m.group(2), m.group(3)
            new_ns = resolve_ns(ns)
            if kw == "namespace":
                if new_ns != ns:
                    log.append(f"{relpath}:{lineno}: namespace {ns} -> {new_ns or '<root>'}")
                if new_ns:
                    out.append(f"{indent}namespace {new_ns}")
                    ns_stack.append(new_ns)
            else:
                if new_ns != ns:
                    log.append(f"{relpath}:{lineno}: end {ns} -> {new_ns or '<root>'}")
                if new_ns:
                    out.append(f"{indent}end {new_ns}")
                    if ns_stack and ns_stack[-1] == new_ns:
                        ns_stack.pop()
                    elif new_ns in ns_stack:
                        while ns_stack and ns_stack[-1] != new_ns:
                            ns_stack.pop()
                        if ns_stack:
                            ns_stack.pop()
        else:
            out.append(qual_sub(line))

    # ------------------------------------------------------------------
    # Name rewrites for declarations that do *not* land at their target
    # through the namespace rewrite alone.  This covers both the declaration
    # site (its relative name appears on its own line) and every reference, in
    # every file that can see the declaration through the shared campaign
    # namespace or an ``open``.
    # ------------------------------------------------------------------
    nss, opened = line_contexts(lines, stacks)
    for p in sorted(bare_pairs, key=lambda p: len(p[1]), reverse=True):
        old_ns, oldrel, newref = p
        if not visible_in(old_ns, nss, opened):
            continue
        pat = re.compile(
            r"(?<![" + IDENT + r".])" + re.escape(oldrel) + r"(?![" + IDENT + r"])"
        )
        for idx, line in enumerate(out):
            new_line, n = pat.subn(newref, line)
            if n:
                log.append(f"{relpath}:{idx + 1}: bare {oldrel} -> {newref} ({n})")
                out[idx] = new_line

    # ------------------------------------------------------------------
    # `open` lines: rewrite namespace tokens, drop campaign ones.
    # ------------------------------------------------------------------
    for idx, line in enumerate(out):
        s = line.lstrip()
        if not (s.startswith("open ") or s == "open"):
            continue
        new_line = OPEN_TOKEN_RE.sub(lambda mo: global_ns_map.get(mo.group(0), mo.group(0)), line)
        new_line = re.sub(r"[ \t]+", " ", new_line).rstrip()
        if new_line.strip() == "open":
            new_line = ""
        if new_line != line:
            log.append(f"{relpath}:{idx + 1}: open {line.strip()} -> {new_line.strip()}")
            out[idx] = new_line

    new_text = "\n".join(out)
    if trailing_newline:
        new_text += "\n"

    changed = new_text != original
    if changed and not dry_run:
        with open(abspath, "w", encoding="utf-8") as fh:
            fh.write(new_text)
    return changed


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--dry-run", action="store_true",
                        help="report changes without writing files")
    parser.add_argument("--map", default=None,
                        help="path to optimal_control_declaration_map.json")
    parser.add_argument("--worktree", default=None)
    global WORKTREE
    args = parser.parse_args(argv)

    map_path = args.map
    if map_path is None:
        map_path = FALLBACK_MAP
    if args.worktree:
        WORKTREE = os.path.abspath(args.worktree)

    with open(map_path, encoding="utf-8") as fh:
        data = json.load(fh)
    entries = [e for e in data["declarations"]
               if e["change"] in ("rename", "rename-and-move")]

    by_file: dict[str, list] = defaultdict(list)
    for e in entries:
        by_file[e["source_path"]].append(e)

    # Module-path renames are only applied to imported *test* modules; library
    # moves are M1…M6 and are deliberately not applied here.
    module_rename: dict[str, str] = {}
    for e in entries:
        if "KirkMedhin" in e.get("source_module", ""):
            module_rename.setdefault(e["source_module"], e["target_module"])
    module_pat = None
    if module_rename:
        srcs = sorted(module_rename, key=len, reverse=True)
        module_pat = re.compile("|".join(re.escape(s) for s in srcs))

    files = collect_files()

    # First pass: per-file namespace maps -> global namespace map + file cache.
    all_ns_cands: dict[str, Counter] = defaultdict(Counter)
    file_data = {}
    for relpath in files:
        abspath = os.path.join(WORKTREE, relpath)
        with open(abspath, encoding="utf-8") as fh:
            lines = fh.read().splitlines()
        stacks = parse_stacks(lines)
        lmap = file_ns_map(by_file.get(relpath, []), stacks)
        file_data[relpath] = (lines, stacks, lmap)
        for ns, new in lmap.items():
            all_ns_cands[ns][new] += 1
    global_ns_map: dict[str, str] = {}
    for ns, c in all_ns_cands.items():
        (best, _), = sorted(c.items(), key=lambda kv: (-kv[1], kv[0] != ""))[:1]
        global_ns_map[ns] = best
    global_ns_map.setdefault("KirkMedhin", "")

    # Qualified replacement map: full old_fqn plus campaign-qualified suffixes.
    qual_map: dict[str, str] = {}
    for e in sorted(entries, key=lambda e: len(e["old_fqn"]), reverse=True):
        qual_map.setdefault(e["old_fqn"], e["target_fqn"])
        for suf in campaign_suffixes(e["old_fqn"]):
            qual_map.setdefault(suf, e["target_fqn"])
    qual_target = qual_map
    if qual_map:
        alts = "|".join(re.escape(o) for o in sorted(qual_map, key=len, reverse=True))
        qual_pat = re.compile(r"(?<![" + IDENT + r".])(?:" + alts + r")(?![" + IDENT + r"])")
    else:
        qual_pat = None

    # Bare-reference pairs: for declarations that do *not* land at their
    # target through the namespace rewrite alone, record (old_ns, oldrel,
    # newref).  These are applied in every file that can see the declaration.
    bare_pairs = []
    seen_pairs = set()
    for relpath in files:
        _lines, stacks, lmap = file_data[relpath]

        def resolve(ns, lmap=lmap):
            if ns in global_ns_map:
                return global_ns_map[ns]
            if ns in lmap:
                return lmap[ns]
            return "" if is_campaign_ns(ns) else ns

        for e in by_file.get(relpath, []):
            st = stacks.get(e["source_line"], ())
            newstack = tuple(x for x in (resolve(s) for s in st) if x)
            oldrel = relative_name(e["old_fqn"], st)
            expected = ".".join(newstack + ((oldrel,) if oldrel else ()))
            if expected == e["target_fqn"]:
                continue
            key = ('.'.join(st), oldrel)
            if key in seen_pairs:
                continue
            seen_pairs.add(key)
            bare_pairs.append((key[0], oldrel, "_root_." + e["target_fqn"]))

    changed_files = []
    log: list[str] = []
    for relpath in files:
        if transform_file(relpath, by_file.get(relpath, []), qual_pat, qual_target,
                          bare_pairs, module_pat, module_rename, global_ns_map,
                          log, args.dry_run):
            changed_files.append(relpath)

    leftovers = []
    if not args.dry_run:
        for relpath in files:
            with open(os.path.join(WORKTREE, relpath), encoding="utf-8") as fh:
                if "KirkMedhin" in fh.read():
                    leftovers.append(relpath)

    log_path = os.path.join(os.path.dirname(os.path.abspath(map_path)), LOG_BASENAME)
    if not args.dry_run:
        with open(log_path, "w", encoding="utf-8") as fh:
            fh.write("# M0 FQN rename log\n")
            fh.write(f"# map: {map_path}\n")
            fh.write(f"# rename entries: {len(entries)}\n")
            fh.write(f"# files changed: {len(changed_files)}\n\n")
            fh.write("\n".join(log))
            fh.write("\n")

    print(f"map:            {map_path}")
    print(f"rename entries: {len(entries)}")
    print(f"lean files:     {len(files)}")
    print(f"changed files:  {len(changed_files)}")
    if leftovers:
        print("leftover 'KirkMedhin' tokens:")
        for p in leftovers:
            print(f"  {p}")
    print("dry run: no files written" if args.dry_run else f"log written to {log_path}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
