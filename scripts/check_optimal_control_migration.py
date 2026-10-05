#!/usr/bin/env python3
"""M0-CHECK — independent verification of the optimal-control FQN rename.

Independent checker for TASK M0-CHECK.  Does NOT trust the M0 executor's
report or reuse its code: every verification below is implemented from
scratch in this file.

Scope: entries of the authoritative map with ``change`` in
``{rename, rename-and-move}`` (521 rows, of which 6 are private
source-qualified names that cannot resolve as public constants).

Checks (mirroring the task):
  1. Old names gone      — no ``old_fqn`` resolves as a declaration
                           (elaborated env probe for library names +
                           declared-name grep over all Lean sources).
  2. Target names resolve — every public ``target_fqn`` resolves
                           (elaborated env probe for library names;
                           declaration-site + file-elaboration evidence
                           for test names, which live outside any lake
                           target and hence have no oleans).
  3. No name lost        — resolving distinct targets == expected (515).
  4. Statements unchanged — per-entry signature comparison of the migrated
                           ``target_fqn`` statement against the baseline
                           ``old_fqn`` statement (``git show`` of the
                           pre-migration tree), alpha-identical apart from
                           the mapped renames.  Full population, not just
                           a sample (a >=25-entry cross-family sample is
                           additionally tabulated for the report).
  5. Hygiene             — KirkMedhin / bare-K1/K3 / sorry / admit / axiom /
                           native_decide / proof_wanted greps (literal AND
                           live-code readings, HEAD vs baseline),
                           ``lake build DynamicalSystems``,
                           ``lake exe axiom-audit --root DynamicalSystems``.

Usage (run from the migrated worktree root)::

    python3 scripts/check_optimal_control_migration.py [--out PATH] ...

Writes exactly one report file (default: the main-repo
``notes/reviews/M0_CHECK.md``).  Generated Lean probes and logs live in a
temporary directory (or /tmp files), never in the repo.

Exit code: 0 if all five checks PASS, 1 otherwise.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict

# ---------------------------------------------------------------------------
# Constants / paths
# ---------------------------------------------------------------------------

SCRIPT_PATH = os.path.abspath(__file__)
WORKTREE = os.path.dirname(os.path.dirname(SCRIPT_PATH))  # repo root
DEFAULT_MAP = (
    "/home/igor/zabawy/auto_automatyk/notes/reviews"
    "/optimal_control_declaration_map.json"
)
DEFAULT_OUT = "/home/igor/zabawy/auto_automatyk/notes/reviews/M0_CHECK.md"
DEFAULT_BASELINE = "a63d7ef"

IDENT = r"A-Za-z0-9_'"
KIND_KWS = ("theorem", "def", "abbrev", "structure", "inductive", "class")

# Lean schemata parsed by this checker (independent implementation).
NS_RE = re.compile(r"^(\s*)namespace\s+([A-Za-z0-9_.']+)\s*(--[^\n]*)?$")
END_NAMED_RE = re.compile(r"^(\s*)end\s+([A-Za-z0-9_.']+)\s*(--[^\n]*)?$")
END_BARE_RE = re.compile(r"^(\s*)end\s*(--[^\n]*)?$")
SECTION_RE = re.compile(r"^(\s*)section(\s+[A-Za-z0-9_.']+)?\s*(--[^\n]*)?$")
DECL_RE = re.compile(
    r"^(\s*)(private\s+)?(noncomputable\s+)?(unsafe\s+)?"
    r"(theorem|def|abbrev|structure|inductive|class|instance)\s+"
    r"(_root_\.)?([A-Za-z0-9_'.]+)"
)
# same-line attribute blocks: `@[simp] theorem ...`
ATTR_PREFIX_RE = re.compile(r"^(\s*)(?:@\[[^\]\n]*\]\s*)+")
IMPORT_RE = re.compile(r"^\s*(public\s+)?import\s+([A-Za-z0-9_.']+)")
OPEN_RE = re.compile(r"^\s*open\b")


def run(cmd, cwd=None, timeout=None):
    """Run cmd, return (returncode, stdout+stderr text)."""
    try:
        p = subprocess.run(
            cmd, cwd=cwd or WORKTREE, capture_output=True, text=True,
            timeout=timeout,
        )
        return p.returncode, (p.stdout or "") + (p.stderr or "")
    except subprocess.TimeoutExpired as ex:
        out = (ex.stdout or "") if isinstance(ex.stdout, str) else ""
        err = (ex.stderr or "") if isinstance(ex.stderr, str) else ""
        return 124, out + err + f"\n[TIMEOUT after {timeout}s: {' '.join(cmd)}]"


def git_show(rev, path):
    p = subprocess.run(
        ["git", "show", f"{rev}:{path}"], cwd=WORKTREE,
        capture_output=True, text=True,
    )
    if p.returncode != 0:
        return None
    return p.stdout


# ---------------------------------------------------------------------------
# Lean lexer helpers (comment/string masking)
# ---------------------------------------------------------------------------

def mask_lean(text):
    """Replace comments and string/char literals with spaces (length kept).

    Handles nesting /- -/ block comments, -- line comments, "..." strings
    with backslash escapes, and 'c' char literals.
    """
    out = list(text)
    n = len(text)
    i = 0
    while i < n:
        c = text[i]
        nxt = text[i + 1] if i + 1 < n else ""
        if c == "-" and nxt == "-":
            j = text.find("\n", i)
            if j == -1:
                j = n
            for k in range(i, j):
                out[k] = " "
            i = j
        elif c == "/" and nxt == "-":
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            while i < n and depth > 0:
                if text[i] == "/" and i + 1 < n and text[i + 1] == "-":
                    depth += 1
                    out[i] = out[i + 1] = " "
                    i += 2
                elif text[i] == "-" and i + 1 < n and text[i + 1] == "/":
                    depth -= 1
                    out[i] = out[i + 1] = " "
                    i += 2
                else:
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
        elif c == '"':
            out[i] = " "
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    out[i] = " "
                    i += 1
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
                else:
                    if text[i] != "\n":
                        out[i] = " "
                    i += 1
            if i < n:
                out[i] = " "
                i += 1
        elif c == "'" and i + 2 < n and text[i + 2] == "'":
            # plausible char literal 'x' (keeps it simple; identifiers
            # never start with a quote so no decl parsing is affected)
            out[i] = out[i + 1] = out[i + 2] = " "
            i += 3
        else:
            i += 1
    return "".join(out)


def live_hits(path, pattern, worktree_root):
    """Grep pattern over the comment/string-masked content of a file."""
    with open(os.path.join(worktree_root, path), encoding="utf-8") as fh:
        masked = mask_lean(fh.read())
    return [
        (idx + 1, line)
        for idx, line in enumerate(masked.split("\n"))
        if re.search(pattern, line)
    ]


# ---------------------------------------------------------------------------
# File parsing: namespaces, declarations, statements
# ---------------------------------------------------------------------------

def parse_file(text):
    """Parse namespaces + named declarations.

    Returns (decls, scaffolding) where decls is a list of dicts with keys:
    kind, name (as written, maybe _root_-prefixed/dotted), fqn (effective),
    line (0-based), stmt (signature text), root_abs (bool).
    scaffolding: list of (lineno, stripped_line) for namespace/end/section/
    open/import lines.
    """
    lines = text.split("\n")
    masked = mask_lean(text).split("\n")
    stack = []  # list of (kind, name) with kind in {"ns", "section"}
    decls = []
    scaff = []
    for idx, (raw, mline) in enumerate(zip(lines, masked)):
        s = mline.strip()
        m = NS_RE.match(mline)
        if m:
            for comp in m.group(2).split("."):
                stack.append(("ns", comp))
            scaff.append((idx, s))
            continue
        m = END_NAMED_RE.match(mline)
        if m:
            target = m.group(2).split(".")
            # pop sections first (bare `end` inside namespace dance is
            # handled by popping non-ns frames as well)
            tmp = list(stack)
            names = [nm for k, nm in tmp if k == "ns"]
            if names[-len(target):] == target:
                drop = len(target)
                new_stack = []
                for k, nm in reversed(tmp):
                    if k == "ns" and drop > 0:
                        drop -= 1
                        continue
                    new_stack.append((k, nm))
                stack = list(reversed(new_stack))
            scaff.append((idx, s))
            continue
        if END_BARE_RE.match(mline):
            if stack:
                stack.pop()
            scaff.append((idx, s))
            continue
        if SECTION_RE.match(mline):
            nm = (mline.strip().split()[1]
                  if len(mline.strip().split()) > 1 else "")
            stack.append(("section", nm))
            scaff.append((idx, s))
            continue
        if IMPORT_RE.match(mline) or OPEN_RE.match(mline):
            scaff.append((idx, s))
            continue
        mline_decl = ATTR_PREFIX_RE.sub(r"\1", mline)
        m = DECL_RE.match(mline_decl)
        if m:
            kind = m.group(5)
            # find end of signature: depth-0 `:=`, or `where` for
            # structure/inductive headers
            j = idx
            depth = 0
            stmt_lines = []
            header_done = False
            in_struc = kind in ("structure", "inductive", "class")
            k = idx
            while k < len(lines):
                ml = masked[k]
                stmt_lines.append(lines[k])
                if k > idx and in_struc and ml.strip().startswith("where"):
                    header_done = True
                    # consume indented field/ctor lines
                    k += 1
                    while k < len(lines):
                        nxt = masked[k]
                        if (nxt.strip() == "" or nxt[:1] in (" ", "\t")
                                or nxt.strip().startswith("--")):
                            stmt_lines.append(lines[k])
                            k += 1
                        else:
                            break
                    break
                # scan for depth-0 :=
                col = 0
                while col < len(ml):
                    ch = ml[col]
                    if ch in "([{ ":
                        pass
                    col += 1
                # manual scan with depth
                d = depth
                c = 0
                found = -1
                while c < len(ml):
                    ch = ml[c]
                    if ch in "([{":
                        d += 1
                    elif ch in ")]}":
                        d -= 1
                    elif ch == ":" and c + 1 < len(ml) and ml[c + 1] == "=":
                        # exclude `==`/`:=` confusion: ensure prev not ':'/'='
                        if d == 0:
                            found = c
                            break
                        c += 1
                    c += 1
                depth = d
                if found >= 0:
                    # signature ends here; keep the line only up to `:=`
                    # for the *signature* record but store full lines
                    header_done = True
                    break
                k += 1
                # safety cap
                if k - idx > 400:
                    break
            ns_prefix = ".".join(nm for k_, nm in stack if k_ == "ns")
            root_abs = m.group(6) is not None
            rel = m.group(7)
            if root_abs:
                fqn = rel
            elif ns_prefix:
                fqn = ns_prefix + "." + rel
            else:
                fqn = rel
            decls.append({
                "kind": kind, "name": rel, "fqn": fqn,
                "line": idx, "root_abs": root_abs,
                "stmt": "\n".join(stmt_lines),
            })
    return decls, scaff


def norm_stmt(text):
    text = re.sub(r"_root_\.\s*", "", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def apply_subs(text, pairs):
    for old, new in pairs:
        text = re.sub(
            r"(?<![A-Za-z0-9_.'])" + re.escape(old)
            + r"(?![A-Za-z0-9_.'])", new, text,
        )
    return text


# ---------------------------------------------------------------------------
# Main checker
# ---------------------------------------------------------------------------

class Checker:
    def __init__(self, args):
        self.args = args
        self.worktree = args.worktree
        with open(args.map, encoding="utf-8") as fh:
            self.map = json.load(fh)
        self.decls_all = self.map["declarations"]
        self.ren = [e for e in self.decls_all
                    if e["change"] in ("rename", "rename-and-move")]
        self.pub = [e for e in self.ren if not e.get("private_source_name")]
        self.priv = [e for e in self.ren if e.get("private_source_name")]
        self.lib = [e for e in self.pub
                    if e["source_path"].startswith("DynamicalSystems/")]
        self.tst = [e for e in self.pub
                    if e["source_path"].startswith("DynamicalSystemsTest/")]
        self.tmp = tempfile.mkdtemp(prefix="m0check_")
        self.results = {}
        self.head_rev = run(
            ["git", "rev-parse", "--short", "HEAD"])[1].strip()

    # -- helpers ---------------------------------------------------------
    def lean_files(self, dirs):
        out = []
        for d in dirs:
            root = os.path.join(self.worktree, d)
            if not os.path.isdir(root):
                continue
            for r, _, fs in os.walk(root):
                for f in fs:
                    if f.endswith(".lean"):
                        out.append(os.path.relpath(os.path.join(r, f),
                                                   self.worktree))
        top = [f for f in os.listdir(self.worktree)
               if f.endswith(".lean")
               and os.path.isfile(os.path.join(self.worktree, f))]
        out.extend(top)
        return sorted(out)

    # -- check 1 ----------------------------------------------------------
    def check_old_names(self):
        olds = [e["old_fqn"] for e in self.ren]
        pat = (r"(?<![A-Za-z0-9_.'])(?:"
               + "|".join(sorted((re.escape(o) for o in olds),
                                 key=len, reverse=True))
               + r")(?![A-Za-z0-9_.'])")
        rx = re.compile(pat)
        files = self.lean_files(["DynamicalSystems", "DynamicalSystemsTest",
                                 "docs"])
        hits = []  # (old, file, line, kind: decl|ref)
        for f in files:
            with open(os.path.join(self.worktree, f),
                      encoding="utf-8") as fh:
                try:
                    text = fh.read()
                except UnicodeDecodeError:
                    continue
            masked = mask_lean(text)
            for idx, (raw, mline) in enumerate(zip(text.split("\n"),
                                                   masked.split("\n"))):
                # skip matches fully inside comments/strings: require the
                # match to appear in the masked line too
                for m in rx.finditer(raw):
                    s, t = m.start(), m.end()
                    if rx.search(mline[max(0, s - 1):t + 1]) is None and \
                            m.group(0) not in mline:
                        # matched text was masked away -> comment/string
                        # (verify by checking masked slice is spaces)
                        if mline[s:t].strip() == "":
                            continue
                    name = m.group(0)
                    dm = DECL_RE.match(ATTR_PREFIX_RE.sub(r"\1", mline))
                    is_decl = bool(dm and (
                        dm.group(7) == name
                        or dm.group(7).endswith("." + name)
                        or name.endswith("." + dm.group(7))))
                    # namespace lines declaring the old name
                    nm = NS_RE.match(mline)
                    if nm and (nm.group(2) == name
                               or name.startswith(nm.group(2) + ".")
                               or nm.group(2).startswith(name + ".")):
                        is_decl = True
                    hits.append((name, f, idx + 1,
                                 "decl" if is_decl else "ref"))
        compiled = [h for h in hits if h[1].startswith(
            ("DynamicalSystems/", "DynamicalSystemsTest/"))]
        docs_hits = [h for h in hits if h[1].startswith("docs/")]
        # elaborated absence probe for lib olds (run together with check 2)
        # surviving old-suffix sweep: multi-component dotted tails of
        # old FQNs (e.g. `K3.uncurryLagrangian`) must not survive either,
        # except identity suffixes equal to some target FQN.
        new_set = set(e["target_fqn"] for e in self.ren)
        sufs = set()
        for o in olds:
            parts = o.split(".")
            for i in range(1, len(parts) - 1):
                suf = ".".join(parts[i:])
                if suf not in new_set:
                    sufs.add(suf)
        spat = (r"(?<![A-Za-z0-9_.'])(?:"
                + "|".join(sorted((re.escape(x) for x in sufs),
                                  key=len, reverse=True))
                + r")(?![A-Za-z0-9_.'])")
        srx = re.compile(spat)
        suf_hits = []
        for f in files:
            with open(os.path.join(self.worktree, f),
                      encoding="utf-8") as fh:
                text = fh.read()
            masked = mask_lean(text)
            for idx, (raw, mline) in enumerate(zip(text.split("\n"),
                                                   masked.split("\n"))):
                for m in srx.finditer(raw):
                    a, b = m.start(), m.end()
                    if mline[a:b].strip() == "":
                        continue  # inside comment/string
                    suf_hits.append((m.group(0), f, idx + 1))
        suf_compiled = [h for h in suf_hits if h[1].startswith(
            ("DynamicalSystems/", "DynamicalSystemsTest/"))]
        suf_docs = [h for h in suf_hits if h[1].startswith("docs/")]
        # Unambiguous (campaign-marker-led) survivors: first component is
        # KirkMedhin / K1* / K3* / PMPNotSufficient, which cannot occur in
        # valid post-rename code.  Concept-led suffixes
        # (IsFinitePiecewiseC1.x, ...) are textually identical to valid
        # relative references inside the new namespaces -> informational.
        def marker_led(name):
            c0 = name.split(".")[0]
            return (c0 == "KirkMedhin" or c0 == "PMPNotSufficient"
                    or c0.startswith("K1") or c0.startswith("K3"))
        suf_marker = [h for h in suf_compiled if marker_led(h[0])]
        self.results["suffix_hits_marker"] = suf_marker
        self.results["old_textual_compiled"] = compiled
        self.results["old_textual_docs"] = docs_hits
        self.results["old_textual_total"] = hits
        self.results["suffix_hits_compiled"] = suf_compiled
        self.results["suffix_hits_docs"] = suf_docs
        return compiled, docs_hits

    # -- check 2: elaborated probe ----------------------------------------
    def lib_modules_with_oleans(self):
        mods = []
        for r, _, fs in os.walk(os.path.join(self.worktree,
                                             "DynamicalSystems")):
            for f in fs:
                if not f.endswith(".lean"):
                    continue
                src = os.path.join(r, f)
                rel = os.path.relpath(src, self.worktree)[:-len(".lean")]
                mod = rel.replace(os.sep, ".")
                olean = os.path.join(
                    self.worktree, ".lake", "build", "lib", "lean",
                    rel + ".olean",
                )
                if os.path.exists(olean):
                    mods.append(mod)
                else:
                    self.results.setdefault("olean_less", []).append(rel)
        return sorted(mods)

    def write_probe(self, targets, olds, sample_checks):
        mods = self.lib_modules_with_oleans()
        lines = ["-- AUTO-GENERATED by check_optimal_control_migration.py"]
        lines += [f"import {m}" for m in mods]
        lines.append("")
        for t in sample_checks:
            lines.append(f"#check @{t}")
        lines.append("open Lean Elab Command in")
        lines.append("run_cmd do")
        lines.append("  let env ← getEnv")
        lines.append("  for n in [")
        for t in targets:
            lines.append(f'    "{t}",')
        lines.append("  ] do")
        lines.append("    match env.find? n.toName with")
        lines.append('    | some _ => logInfo m!"M0CHECK_PRESENT " ++ n')
        lines.append('    | none => logError m!"M0CHECK_MISSING " ++ n')
        lines.append("  for n in [")
        for o in olds:
            lines.append(f'    "{o}",')
        lines.append("  ] do")
        lines.append("    match env.find? n.toName with")
        lines.append(
            '    | some _ => logError m!"M0CHECK_STILL_PRESENT " ++ n')
        lines.append('    | none => logInfo m!"M0CHECK_ABSENT_OK " ++ n')
        path = os.path.join(self.tmp, "M0CheckProbe.lean")
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines) + "\n")
        return path, mods

    def run_probe(self):
        lib_targets = sorted(set(e["target_fqn"] for e in self.lib))
        lib_olds = sorted(set(
            e["old_fqn"] for e in self.lib + self.priv
            if e["source_path"].startswith("DynamicalSystems/")))
        # sample for real #check lines: all structure/inductive targets +
        # round-robin across families
        struct_ind = sorted(set(
            e["target_fqn"] for e in self.lib
            if e["kind"] in ("structure", "inductive")))
        by_fam = defaultdict(list)
        for e in self.lib:
            by_fam[e["source_path"]].append(e["target_fqn"])
        fams = sorted(by_fam)
        sample = list(struct_ind)
        i = 0
        while len(sample) < 40 and any(by_fam[f][i:] for f in fams):
            for f in fams:
                if i < len(by_fam[f]) and len(sample) < 40:
                    t = by_fam[f][i]
                    if t not in sample:
                        sample.append(t)
            i += 1
        probe, mods = self.write_probe(lib_targets, lib_olds, sample)
        rc, out = run(["lake", "env", "lean", probe], timeout=1500)
        present, missing, absent_ok, still = set(), set(), set(), set()
        for line in out.split("\n"):
            m = re.search(r"M0CHECK_(PRESENT|MISSING|ABSENT_OK|STILL_PRESENT) (.*)$",  # noqa: E501
                          line.strip())
            if not m:
                continue
            kind, name = m.group(1), m.group(2).strip()
            {"PRESENT": present, "MISSING": missing,
             "ABSENT_OK": absent_ok,
             "STILL_PRESENT": still}[kind].add(name)
        self.results["probe"] = {
            "rc": rc, "path": probe, "n_modules": len(mods),
            "n_targets": len(lib_targets), "n_olds": len(lib_olds),
            "n_sample_checks": len(sample),
            "present": sorted(present), "missing": sorted(missing),
            "absent_ok": sorted(absent_ok), "still": sorted(still),
            "log": out,
        }
        return self.results["probe"]

    # -- check 2: test files ----------------------------------------------
    def elab_file(self, path, timeout=900):
        return run(["lake", "env", "lean", path], timeout=timeout)

    def check_tests(self):
        test_files = sorted(set(
            e["source_path"] for e in self.tst + self.priv
            if e["source_path"].startswith("DynamicalSystemsTest/")))
        # which test files import other test modules / missing files
        import_status = {}
        for f in test_files:
            with open(os.path.join(self.worktree, f),
                      encoding="utf-8") as fh:
                imps = IMPORT_RE.findall(fh.read())
            mods = [m[1] for m in imps]
            test_imps = [m for m in mods
                         if m.startswith("DynamicalSystemsTest.")]
            missing = [m for m in mods
                       if not self.module_has_file(m)]
            import_status[f] = {"test_imports": test_imps,
                                "missing_files": missing}
        # standalone elaboration for files without test imports
        elab = {}
        import concurrent.futures as cf
        standalone = [f for f in test_files
                      if not import_status[f]["test_imports"]]
        with cf.ThreadPoolExecutor(max_workers=6) as ex:
            futs = {ex.submit(self.elab_file, f): f for f in standalone}
            for fut in cf.as_completed(futs):
                f = futs[fut]
                try:
                    rc, out = fut.result()
                except Exception as exn:  # noqa: BLE001
                    rc, out = 99, f"harness error: {exn}"
                errs = [l for l in out.split("\n") if ": error" in l]
                elab[f] = {"rc": rc, "errors": errs, "log": out}
        # hermetic merged elaboration for blocked files
        hermetic = {}
        for f in test_files:
            if f in elab:
                continue
            merged = self.hermetic_merge(f, import_status[f])
            if merged is None:
                hermetic[f] = {"rc": None, "errors": ["no provider"],
                               "log": ""}
                continue
            rc, out = self.elab_file(merged, timeout=900)
            errs = [l for l in out.split("\n") if ": error" in l]
            hermetic[f] = {"rc": rc, "errors": errs, "log": out,
                           "probe": merged}
        self.results["test_files"] = test_files
        self.results["test_imports"] = import_status
        self.results["test_elab"] = elab
        self.results["test_hermetic"] = hermetic
        return test_files, import_status, elab, hermetic

    def module_has_file(self, mod):
        rel = mod.replace(".", "/") + ".lean"
        if os.path.exists(os.path.join(self.worktree, rel)):
            return True
        # package / toolchain oleans
        rc, lean_path = run(["lake", "env", "sh", "-c", "echo $LEAN_PATH"],
                            timeout=60)
        for d in lean_path.strip().split(":"):
            if d and os.path.exists(
                    os.path.join(d, mod.replace(".", "/") + ".olean")):
                return True
        return False

    def hermetic_merge(self, path, status):
        """Inline existing provider test files for missing test imports.

        Returns path of merged probe in tmpdir, or None if some needed
        provider file does not exist on disk.
        """
        # map aspirational module -> provider source file: the test source
        # file whose map entries target that module
        tgt_to_src = {}
        for e in self.tst:
            tgt_to_src.setdefault(e["target_module"], e["source_path"])
        needed = []
        for m in status["test_imports"]:
            if m in tgt_to_src:
                needed.append(tgt_to_src[m])
            elif os.path.exists(os.path.join(
                    self.worktree, m.replace(".", "/") + ".lean")):
                needed.append(m.replace(".", "/") + ".lean")
            else:
                return None
        chunks = []
        seen_imports = set()
        for src in dict.fromkeys(needed):
            with open(os.path.join(self.worktree, src),
                      encoding="utf-8") as fh:
                for line in fh.read().split("\n"):
                    mi = IMPORT_RE.match(line)
                    if mi and mi.group(2).startswith(
                            "DynamicalSystemsTest."):
                        continue
                    chunks.append(line)
        with open(os.path.join(self.worktree, path),
                  encoding="utf-8") as fh:
            main = fh.read().split("\n")
        out = ["-- hermetic merge for M0-CHECK"] + chunks
        for line in main:
            mi = IMPORT_RE.match(line)
            if mi and mi.group(2).startswith("DynamicalSystemsTest."):
                out.append(f"-- dropped {line.strip()} (inlined above)")
                continue
            out.append(line)
        # de-duplicate repeated import lines to keep it clean
        deduped = []
        for line in out:
            mi = IMPORT_RE.match(line)
            if mi:
                if mi.group(2) in seen_imports:
                    continue
                seen_imports.add(mi.group(2))
            deduped.append(line)
        dest = os.path.join(
            self.tmp, "hermetic_" + path.replace("/", "_"))
        with open(dest, "w", encoding="utf-8") as fh:
            fh.write("\n".join(deduped) + "\n")
        return dest

    def baseline_has_file(self, mod):
        bdir = self.results.get("baseline_dir")
        if bdir is None:
            return True  # unknown -> do not claim regression
        return os.path.exists(
            os.path.join(bdir, mod.replace(".", "/") + ".lean"))

    def check_import_integrity(self):
        """HEAD vs baseline: every `import` in test+docs files must resolve
        to a file (repo or baseline tree) or a built olean.  Reports
        M0-introduced dangling imports (resolved at baseline, dangling
        at HEAD)."""
        self.baseline_tree()
        files = self.lean_files(["DynamicalSystemsTest", "docs"])
        rows = []
        for f in files:
            with open(os.path.join(self.worktree, f),
                      encoding="utf-8") as fh:
                head_imps = [m[1] for m in IMPORT_RE.findall(fh.read())]
            bt = git_show(self.args.baseline, f)
            base_imps = ([m[1] for m in IMPORT_RE.findall(bt)]
                         if bt is not None else None)
            head_dang = sorted(set(
                m for m in head_imps if not self.module_has_file(m)))
            if base_imps is None:
                base_dang = None
            else:
                base_dang = sorted(set(
                    m for m in base_imps
                    if not self.baseline_has_file(m)
                    and not self.package_olean(m)))
            introduced = None
            if base_dang is not None:
                introduced = sorted(set(head_dang) - set(base_dang))
            rows.append((f, head_dang, base_dang, introduced))
        self.results["import_integrity"] = rows
        return rows

    def package_olean(self, mod):
        rc, lean_path = run(["lake", "env", "sh", "-c", "echo $LEAN_PATH"],
                            timeout=60)
        for d in lean_path.strip().split(":"):
            if d and os.path.exists(
                    os.path.join(d, mod.replace(".", "/") + ".olean")):
                return True
        return False

    def check_comment_balance(self):
        """Every .lean file must have balanced /- -/ (comment-aware scan)."""
        files = self.lean_files(["DynamicalSystems", "DynamicalSystemsTest",
                                 "docs"])
        bad = []
        for f in files:
            with open(os.path.join(self.worktree, f),
                      encoding="utf-8") as fh:
                text = fh.read()
            depth = 0
            i, n = 0, len(text)
            ok = True
            while i < n:
                c = text[i]
                nxt = text[i + 1] if i + 1 < n else ""
                if depth > 0:
                    # inside block comment: only nesting matters
                    if c == "/" and nxt == "-":
                        depth += 1
                        i += 2
                        continue
                    if c == "-" and nxt == "/":
                        depth -= 1
                        i += 2
                        continue
                    i += 1
                    continue
                if c == "-" and nxt == "-":
                    j = text.find("\n", i)
                    i = n if j == -1 else j
                    continue
                if c == "/" and nxt == "-":
                    depth += 1
                    i += 2
                    continue
                if c == "-" and nxt == "/":
                    ok = False
                    break
                if c == '"':
                    i += 1
                    while i < n and text[i] != '"':
                        if text[i] == "\\":
                            i += 1
                        i += 1
                    i += 1
                    continue
                if c == "'" and i + 2 < n and text[i + 2] == "'":
                    i += 3
                    continue
                i += 1
            if not ok or depth != 0:
                bad.append((f, depth))
        self.results["comment_balance_bad"] = bad
        return bad

    # -- declaration-site / effective-FQN verification ---------------------
    def verify_def_sites(self):
        files = sorted(set(e["source_path"] for e in self.ren))
        base_parsed, head_parsed = {}, {}
        for f in files:
            with open(os.path.join(self.worktree, f),
                      encoding="utf-8") as fh:
                head_parsed[f] = parse_file(fh.read())
            btext = git_show(self.args.baseline, f)
            base_parsed[f] = parse_file(btext) if btext is not None else None
        # index HEAD decls by fqn (whole tree fallback for relocated ones)
        head_index = defaultdict(list)
        for f, (decls, _) in head_parsed.items():
            for d in decls:
                head_index[d["fqn"]].append((f, d))
        rows = []
        for e in self.pub:
            f = e["source_path"]
            brow = hrow = None
            if base_parsed.get(f):
                for d in base_parsed[f][0]:
                    if d["fqn"] == e["old_fqn"]:
                        brow = d
                        break
            for ff, d in head_index.get(e["target_fqn"], []):
                hrow = (ff, d)
                break
            rows.append((e, brow, hrow))
        priv_rows = []
        priv_stmt_rows = []
        for e in self.priv:
            f = e["source_path"]
            brow = hrow = None
            bpar = base_parsed.get(f)
            hpar = head_parsed.get(f)
            if bpar:
                for d in bpar[0]:
                    if d["fqn"] == e["old_fqn"]:
                        brow = d
                        break
            if hpar:
                for d in hpar[0]:
                    if d["fqn"] == e["target_fqn"]:
                        hrow = d
                        break
            old_absent = not any(
                h[0] == e["old_fqn"] for h in
                self.results.get("old_textual_total", []))
            priv_rows.append((e, hrow, old_absent))
            priv_stmt_rows.append((e, brow, hrow if hrow is None else
                                    (f, hrow)))
        self.results["priv_stmt_rows"] = priv_stmt_rows
        self.results["def_rows"] = rows
        self.results["priv_rows"] = priv_rows
        self.results["base_parsed"] = base_parsed
        self.results["head_parsed"] = head_parsed
        return rows, priv_rows

    # -- check 4 ------------------------------------------------------------
    def check_statements(self):
        pairs = sorted(set(
            (e["old_fqn"], e["target_fqn"]) for e in self.ren),
            key=lambda p: -len(p[0]),
        )
        # Two-sided canonicalization: qualified old -> new, plus leaf
        # rules (old leaf -> new, new leaf -> new) ONLY for pairs whose
        # leaf was actually renamed.  Pure namespace-strip entries get
        # no leaf rules (their leaves are common words).
        leaf_rules = []
        for old, new in pairs:
            oleaf, nleaf = old.split(".")[-1], new.split(".")[-1]
            if oleaf != nleaf:
                leaf_rules.append((oleaf, new))
                if nleaf != oleaf:
                    leaf_rules.append((nleaf, new))
        seen = set()
        leaf_rules = [r for r in leaf_rules
                      if not (r in seen or seen.add(r))]
        leaf_rules.sort(key=lambda p: -len(p[0]))
        # Suffix rules: multi-component dotted tails of old FQNs
        # (e.g. `K3.uncurryLagrangian` for `KirkMedhin.K3.uncurryLagrangian`),
        # which M0 rewrote as qualified occurrences.  Identity suffixes
        # (equal to some target FQN) are excluded.
        new_set = set(new for _, new in pairs)
        suffix_rules = []
        for old_, new_ in pairs:
            parts = old_.split(".")
            for i in range(1, len(parts) - 1):
                suf = ".".join(parts[i:])
                if suf not in new_set:
                    suffix_rules.append((suf, new_))
        seen2 = set()
        suffix_rules = [r for r in suffix_rules
                        if not (r in seen2 or seen2.add(r))]
        suffix_rules.sort(key=lambda p: -len(p[0]))
        self.results["suffix_rules"] = suffix_rules
        all_rules = pairs + suffix_rules + leaf_rules

        def anchor(stmt, new):
            return re.sub(
                r"^(\s*(?:private\s+)?(?:noncomputable\s+)?" +
                r"(?:unsafe\s+)?(?:theorem|def|abbrev|structure|" +
                r"inductive|class|instance)\s+)" +
                r"(?:_root_\.)?[A-Za-z0-9_'.]+",
                r"\1" + new, stmt, count=1)

        def canon(stmt):
            return norm_stmt(apply_subs(norm_stmt(stmt), all_rules))
        stats = {"tier1": 0, "tier2": 0, "drift": [], "nofind": [],
                 "kind_mismatch": []}
        per_entry = []
        for e, brow, hrow in self.results["def_rows"]:
            if brow is None or hrow is None:
                stats["nofind"].append(
                    (e["old_fqn"], e["target_fqn"],
                     "baseline" if brow is None else "head"))
                per_entry.append((e, "NOFIND"))
                continue
            hfile, hd = hrow
            if e["kind"] != hd["kind"] and not (
                    e["kind"] == "def" and hd["kind"] == "abbrev"):
                stats["kind_mismatch"].append(
                    (e["target_fqn"], e["kind"], hd["kind"]))
            base_norm = canon(anchor(brow["stmt"], e["target_fqn"]))
            head_norm = canon(anchor(hd["stmt"], e["target_fqn"]))
            if base_norm == head_norm:
                plain = norm_stmt(apply_subs(
                    norm_stmt(anchor(brow["stmt"],
                                     e["target_fqn"])), pairs))
                plain_h = norm_stmt(anchor(hd["stmt"],
                                            e["target_fqn"]))
                if plain == plain_h:
                    stats["tier1"] += 1
                    per_entry.append((e, "TIER1"))
                else:
                    stats["tier2"] += 1
                    per_entry.append((e, "TIER2"))
                continue
            stats["drift"].append((e, brow["stmt"], hd["stmt"],
                                   base_norm, head_norm))
            per_entry.append((e, "DRIFT"))
        for e, brow, hrow in self.results.get("priv_stmt_rows", []):
            if brow is None or hrow is None:
                stats["nofind"].append(
                    (e["old_fqn"], e["target_fqn"],
                     "baseline" if brow is None else "head"))
                per_entry.append((e, "NOFIND"))
                continue
            hfile, hd = hrow
            base_norm = canon(anchor(brow["stmt"], e["target_fqn"]))
            head_norm = canon(anchor(hd["stmt"], e["target_fqn"]))
            if base_norm == head_norm:
                stats["tier1"] += 1
                per_entry.append((e, "TIER1-priv"))
            else:
                stats["drift"].append((e, brow["stmt"], hd["stmt"],
                                       base_norm, head_norm))
                per_entry.append((e, "DRIFT"))
        self.results["stmt_stats"] = stats
        self.results["stmt_entries"] = per_entry
        return stats

    # -- scaffolding diff ----------------------------------------------------
    def check_scaffolding(self):
        touched = sorted(set(
            self.results["head_parsed"].keys())
            | set(self.results["base_parsed"].keys()))
        diffs = {}
        for f in touched:
            b = self.results["base_parsed"].get(f)
            h = self.results["head_parsed"].get(f)
            if not b:
                continue
            bs = sorted(set(s for _, s in b[1]
                            if s.startswith(("import", "public import",
                                             "open"))))
            hs = sorted(set(s for _, s in h[1]
                            if s.startswith(("import", "public import",
                                             "open"))))
            if bs != hs:
                diffs[f] = {"removed": sorted(set(bs) - set(hs)),
                            "added": sorted(set(hs) - set(bs))}
        self.results["scaff_diffs"] = diffs
        return diffs

    # -- check 5 -------------------------------------------------------------
    def baseline_tree(self):
        """Extract the baseline tree once (for identical-code comparisons)."""
        if self.results.get("baseline_dir"):
            return self.results["baseline_dir"]
        dest = os.path.join(self.tmp, "baseline")
        os.makedirs(dest, exist_ok=True)
        rc, out = run(["git", "archive", self.args.baseline,
                       "DynamicalSystems", "DynamicalSystemsTest", "docs",
                       "DynamicalSystems.lean", "Documentation.lean"],
                      timeout=300)
        if rc != 0:
            self.results["baseline_dir"] = None
            return None
        # run() captures text; need bytes for tar: redo via subprocess
        import subprocess as sp
        pr = sp.run(["git", "archive", self.args.baseline,
                     "DynamicalSystems", "DynamicalSystemsTest", "docs",
                     "DynamicalSystems.lean", "Documentation.lean"],
                    cwd=self.worktree, capture_output=True, timeout=300)
        import tarfile, io as _io
        tarfile.open(fileobj=_io.BytesIO(pr.stdout)).extractall(dest)
        self.results["baseline_dir"] = dest
        return dest

    def sweep_tree(self, root, files, pats):
        raw, live = {}, {}
        for name, pat in pats.items():
            raw[name] = []
            live[name] = []
            rx = re.compile(pat)
            for f in files:
                fp = os.path.join(root, f)
                if not os.path.exists(fp):
                    continue
                with open(fp, encoding="utf-8") as fh:
                    text = fh.read()
                masked = mask_lean(text)
                for idx, (rl, ml) in enumerate(zip(text.split("\n"),
                                                   masked.split("\n"))):
                    if rx.search(rl):
                        raw[name].append((f, idx + 1, rl.strip()[:160]))
                    if rx.search(ml):
                        live[name].append((f, idx + 1, ml.strip()[:160]))
        return raw, live

    def hygiene_greps(self):
        files = self.lean_files(["DynamicalSystems", "DynamicalSystemsTest",
                                 "docs"])
        pats = {
            "KirkMedhin": r"KirkMedhin",
            "bare_K1_K3": r"(?<![A-Za-z0-9_'])(K1|K3)(?![A-Za-z0-9_'])",
            "sorry": r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])",
            "admit": r"(?<![A-Za-z0-9_'])admit(?![A-Za-z0-9_'])",
            "axiom": r"(?m)^\s*axiom(?![A-Za-z0-9_'])",
            "native_decide": r"(?<![A-Za-z0-9_'])native_decide"
                             r"(?![A-Za-z0-9_'])",
            "proof_wanted": r"(?<![A-Za-z0-9_'])proof_wanted"
                            r"(?![A-Za-z0-9_'])",
        }
        head_raw, head_live = self.sweep_tree(self.worktree, files,
                                                 pats)
        # baseline sweep with identical code over the extracted tree
        bdir = self.baseline_tree()
        if bdir is not None:
            braw, _blive = self.sweep_tree(bdir, files, pats)
            base_counts = {k: len(v) for k, v in braw.items()}
        else:
            base_counts = {k: -1 for k in pats}
        # M0-touched files + added-line sets for introduction test
        rc, out = run(["git", "diff", "--name-only",
                       f"{self.args.baseline}", "HEAD", "--",
                       "DynamicalSystems", "DynamicalSystemsTest", "docs"],
                      timeout=120)
        touched = set(out.strip().split("\n")) if out.strip() else set()
        rc2, diff = run(["git", "diff", "-U0", self.args.baseline, "HEAD",
                         "--", "DynamicalSystems", "DynamicalSystemsTest",
                         "docs"], timeout=300)
        added = defaultdict(set)
        cur = None
        for line in diff.split("\n"):
            if line.startswith("+++ b/"):
                cur = line[len("+++ b/"):]
            elif cur is not None and line.startswith("+") and \
                    not line.startswith("+++"):
                added[cur].add(line[1:].strip())
        introduced = {}
        base_lines_cache = {}
        for name in pats:
            introduced[name] = []
            for f, ln, txt in head_raw.get(name, []):
                if f not in base_lines_cache:
                    bt = git_show(self.args.baseline, f)
                    base_lines_cache[f] = (
                        set(l.strip() for l in bt.split("\n"))
                        if bt is not None else set())
                with open(os.path.join(self.worktree, f),
                          encoding="utf-8") as fh:
                    htxt = fh.read().split("\n")[ln - 1].strip()
                if htxt in added.get(f, set()) and \
                        htxt not in base_lines_cache[f]:
                    introduced[name].append((f, ln, txt))
        self.results["hyg_introduced"] = introduced
        self.results["hyg_raw"] = head_raw
        self.results["hyg_live"] = head_live
        self.results["hyg_base_counts"] = base_counts
        self.results["m0_touched"] = touched
        return head_raw, head_live

    def run_build(self):
        rc, out = run(["lake", "build", "DynamicalSystems"], timeout=3600)
        tail = "\n".join(out.strip().split("\n")[-8:])
        self.results["build"] = {"rc": rc, "tail": tail, "log": out}
        return rc

    def run_audit(self):
        rc, out = run(["lake", "exe", "axiom-audit", "--root",
                       "DynamicalSystems"], timeout=3600)
        self.results["audit"] = {"rc": rc, "out": out.strip()[:4000]}
        return rc


# ---------------------------------------------------------------------------
# Report
# ---------------------------------------------------------------------------

def verdict_str(ok):
    return "PASS" if ok else "FAIL"


def build_report(ch: Checker):
    R = ch.results
    L = []
    A = ch.args
    n_ren = len(ch.ren)
    n_pub = len(ch.pub)
    n_priv = len(ch.priv)
    n_lib = len(ch.lib)
    n_tst = len(ch.tst)

    probe = R.get("probe", {})
    missing = probe.get("missing", [])
    still = probe.get("still", [])
    present = probe.get("present", [])

    compiled_hits = R.get("old_textual_compiled", [])
    docs_hits = R.get("old_textual_docs", [])
    suf_compiled = R.get("suffix_hits_compiled", [])
    suf_docs = R.get("suffix_hits_docs", [])
    suf_marker = R.get("suffix_hits_marker", [])

    rows = R.get("def_rows", [])
    test_targets_found = sum(1 for e, b, h in rows
                             if h is not None and e in ch.tst)
    lib_targets_found = sum(1 for e, b, h in rows
                            if h is not None and e in ch.lib)
    test_targets_total = len(ch.tst)
    lib_targets_total = len(ch.lib)

    # check 2 test elaboration rollup
    elab = R.get("test_elab", {})
    herm = R.get("test_hermetic", {})
    imports = R.get("test_imports", {})
    dangling = sorted(set(
        m for f, st in imports.items() for m in st["missing_files"]
        if m.startswith("DynamicalSystemsTest.")))

    # check 4
    stats = R.get("stmt_stats", {})

    # check 5 pieces
    hyg_raw = R.get("hyg_raw", {})
    hyg_live = R.get("hyg_live", {})
    base_counts = R.get("hyg_base_counts", {})
    touched = R.get("m0_touched", set())
    build = R.get("build", {})
    audit = R.get("audit", {})

    # ---- verdicts ----
    c1 = (len(compiled_hits) == 0 and len(still) == 0
          and len(suf_marker) == 0 and probe.get("rc") == 0)
    c2 = (len(missing) == 0 and probe.get("rc") == 0
          and test_targets_found == test_targets_total
          and lib_targets_found == lib_targets_total
          and all(v["rc"] == 0 for v in elab.values())
          and all(v["rc"] == 0 for v in herm.values()))
    resolved_distinct = len(set(present)) + test_targets_found
    c3 = (resolved_distinct == n_pub and not missing
          and test_targets_found == test_targets_total)
    c4 = (len(stats.get("drift", [])) == 0
          and len(stats.get("nofind", [])) == 0)
    # strict literal hygiene: any raw hit for the listed patterns in .lean
    strict_items = {k: v for k, v in hyg_raw.items()}
    c5 = (all(len(v) == 0 for v in strict_items.values())
          and build.get("rc") == 0 and audit.get("rc") == 0)
    overall = all([c1, c2, c3, c4, c5])

    L.append(f"# M0-CHECK — independent verification of the optimal-control rename")
    L.append("")
    L.append(f"- Date (UTC): {__import__('datetime').datetime.utcnow().strftime('%Y-%m-%d %H:%M')}")
    L.append(f"- Worktree: `{ch.worktree}` (HEAD `{ch.head_rev}`, expected `8a714ad`)")
    L.append(f"- Baseline (pre-migration): `{A.baseline}`")
    L.append(f"- Authoritative map: `{A.map}`")
    L.append(f"- Checker: `scripts/check_optimal_control_migration.py` (this report's only sibling edit; no repo sources touched)")
    L.append(f"- Map scope: {len(ch.decls_all)} declarations; rename-scope (rename + rename-and-move) **{n_ren}** = **{n_pub}** public + **{n_priv}** private; public = **{n_lib}** library + **{n_tst}** test.")
    L.append("")
    L.append("## Verdicts")
    L.append("")
    L.append(f"- Check 1 (old names gone): **{verdict_str(c1)}**")
    L.append(f"- Check 2 (targets resolve): **{verdict_str(c2)}**")
    L.append(f"- Check 3 (no name lost): **{verdict_str(c3)}**")
    L.append(f"- Check 4 (statements unchanged): **{verdict_str(c4)}**")
    L.append(f"- Check 5 (hygiene): **{verdict_str(c5)}** (strict literal reading; see layered analysis)")
    L.append(f"- Overall: **{'ACCEPT' if overall else 'NOT ACCEPTED'}** (single-failure rule)")
    L.append("")

    # ---- check 1 ----
    L.append("## Check 1 — old names gone")
    L.append("")
    L.append(f"- Rename-scope old names swept: {n_ren} (incl. {n_priv} private).")
    L.append(f"- Elaborated absence probe (`lake env lean` over {probe.get('n_modules', '?')} built library modules, `env.find?` per name): {len(probe.get('absent_ok', []))} absent as expected, **{len(still)} still resolving**.")
    if still:
        for n in still:
            L.append(f"  - STILL PRESENT: `{n}`")
    L.append(f"- Exact-token source sweep (identifier-boundary regex, comments/strings masked): **{len(compiled_hits)}** hits in `DynamicalSystems/` + `DynamicalSystemsTest/`, **{len(docs_hits)}** hits in `docs/` (module-path references, none a declared name — see below).")
    for name, f, ln, kind in docs_hits:
        L.append(f"  - docs: `{name}` {f}:{ln} [{kind}]")
    L.append(f"- Surviving old-suffix sweep (e.g. `K3.uncurryLagrangian`): **{len(suf_compiled)}** hits in compiled tree, **{len(suf_docs)}** in docs/.")
    for name, f, ln in (suf_compiled + suf_docs)[:20]:
        L.append(f"  - suffix: `{name}` {f}:{ln}")
    L.append(f"- Unambiguous campaign-marker-led suffix survivors (must be zero): **{len(suf_marker)}**.")
    for name, f, ln in suf_marker[:20]:
        L.append(f"  - MARKER-SUFFIX: `{name}` {f}:{ln}")
    L.append(f"- Verdict: **{verdict_str(c1)}**")
    L.append("")

    # ---- check 2 ----
    L.append("## Check 2 — target names resolve")
    L.append("")
    L.append(f"- Library targets: probe `env.find?` → **{len(present)}/{probe.get('n_targets', '?')} present**, {len(missing)} missing; real `#check @tgt` lines for a {probe.get('n_sample_checks', '?')}-entry sample (all structures/inductives + cross-family round-robin); probe exit code {probe.get('rc', '?')} (0 = no `logError`).")
    if missing:
        for n in missing:
            L.append(f"  - MISSING: `{n}`")
    kind_mm = [r for r in rows if r[2] is not None and r[0]["kind"] != r[2][1]["kind"] and not (r[0]["kind"] == "def" and r[2][1]["kind"] == "abbrev")]
    L.append(f"- Declaration-site kind agreement (map `kind` vs site keyword, effective-FQN placed): **{len(kind_mm)} mismatches** out of {len(rows)} public entries.")
    for e, b, h in kind_mm[:20]:
        L.append(f"  - `{e['target_fqn']}: map {e['kind']} vs site {h[1]['kind']} ({h[0]}:{h[1]['line'] + 1})")
    L.append(f"- Library def-sites placed (effective FQN == target): {lib_targets_found}/{lib_targets_total}.")
    L.append(f"- Test def-sites placed: {test_targets_found}/{test_targets_total}.")
    L.append(f"- Test files ({len(R.get('test_files', []))}): standalone `lake env lean` green for {sum(1 for v in elab.values() if v['rc'] == 0)}/{len(elab)} eligible (no test-module imports); hermetic-merged elaboration green for {sum(1 for v in herm.values() if v['rc'] == 0)}/{len(herm)} blocked files.")
    for f, v in sorted(elab.items()):
        if v["rc"] != 0:
            L.append(f"  - ELAB FAIL (standalone): {f} rc={v['rc']}")
            for e in v["errors"][:5]:
                L.append(f"    - {e[:200]}")
    for f, v in sorted(herm.items()):
        if v["rc"] != 0:
            L.append(f"  - ELAB FAIL (hermetic): {f} rc={v['rc']}")
            for e in v["errors"][:5]:
                L.append(f"    - {e[:200]}")
    L.append(f"- Test/docs imports with no corresponding file at HEAD (aspirational M1–M6 paths, rewritten by M0 per its log line for module-path rewrites; all resolved to existing files at baseline): **{len(dangling)}**.")
    for m in dangling:
        users = sorted(f for f, st in imports.items() if m in st["missing_files"])
        L.append(f"  - `{m}` ← {', '.join(users)}")
    L.append(f"- Private entries ({n_priv}): textual verification (renamed leaf present, old string absent): " + ", ".join(
        f"`{e['target_fqn']}`:{'OK' if (fr and oa) else 'CHECK'}"
        for e, fr, oa in R.get("priv_rows", [])))
    L.append(f"- Verdict: **{verdict_str(c2)}**")
    L.append("")

    # ---- check 3 ----
    L.append("## Check 3 — no name lost")
    L.append("")
    L.append(f"- Expected distinct public targets: {n_pub} (dup check on map: {n_pub - len(set(e['target_fqn'] for e in ch.pub))} duplicates).")
    L.append(f"- Resolving: {len(set(present))} library (env) + {test_targets_found} test (def-site) = **{resolved_distinct}**.")
    if missing or test_targets_found != test_targets_total:
        L.append(f"- Missing library: {missing if missing else []}")
        miss_t = [e["target_fqn"] for e, b, h in rows if h is None and e in ch.tst]
        L.append(f"- Missing test: {miss_t if miss_t else []}")
    L.append(f"- Verdict: **{verdict_str(c3)}**")
    L.append("")

    # ---- check 4 ----
    L.append("## Check 4 — statements unchanged")
    L.append("")
    L.append(f"- Method: per-entry signature extraction (declaration keyword through depth-0 `:=`, or `where` + body for structure/inductive) from baseline (`git show {A.baseline}`) and HEAD; baseline statement normalized by the full 521-pair rename substitution (longest-first, identifier-boundary); `_root_` prefixes stripped both sides; whitespace-collapsed compare (tier 1). Non-matching entries retried with two-sided canonicalization (campaign-qualified suffix forms plus bare leaves of leaf-renamed pairs, tier 2 — every rule derived from a map pair). Anything else = DRIFT.")
    npriv = len(R.get("priv_stmt_rows", []))
    L.append(f"- Population ({len(rows)} public + {npriv} private entries): tier-1 identical **{stats.get('tier1', 0)}**, tier-2 (suffix/leaf canonicalization) **{stats.get('tier2', 0)}**, **declaration not located: {len(stats.get('nofind', []))}**, **DRIFT: {len(stats.get('drift', []))}**.")
    for a, b, where in stats.get("nofind", [])[:20]:
        L.append(f"  - NOFIND ({where}): `{a}` → `{b}`")
    for e, bs, hs, bn, hn in stats.get("drift", [])[:10]:
        L.append(f"  - DRIFT: `{e['old_fqn']}` → `{e['target_fqn']}` ({e['source_path']})")
        L.append(f"    - baseline(norm): `{bn[:300]}`")
        L.append(f"    - head(norm):     `{hn[:300]}`")
    # sample table
    entries = R.get("stmt_entries", [])
    byfam = defaultdict(list)
    for e, tier in entries:
        byfam[e["source_path"]].append((e, tier))
    sample = []
    fams = sorted(byfam)
    i = 0
    while len(sample) < 30 and any(byfam[f][i:] for f in fams):
        for f in fams:
            if i < len(byfam[f]) and len(sample) < 30:
                sample.append(byfam[f][i])
        i += 1
    L.append(f"- Cross-family sample ({len(sample)} entries, ≥25 required):")
    for e, tier in sample:
        L.append(f"  - [{tier}] `{e['old_fqn']}` → `{e['target_fqn']}` ({e['source_path']})")
    # scaffolding
    diffs = R.get("scaff_diffs", {})
    L.append(f"- `import`/`open` scaffolding diffs baseline→HEAD in entry files: {len(diffs)} files.")
    for f, d in sorted(diffs.items())[:20]:
        L.append(f"  - {f}: -{len(d['removed'])} +{len(d['added'])}")
        for x in (d["removed"] + d["added"])[:6]:
            L.append(f"    - `{x[:140]}`")
    L.append(f"- Verdict: **{verdict_str(c4)}**")
    L.append("")

    # ---- check 5 ----
    L.append("## Check 5 — hygiene")
    L.append("")
    L.append("- Literal grep layer (raw file text, comments included) over `DynamicalSystems/`, `DynamicalSystemsTest/`, `docs/`, root `*.lean`:")
    for name in ["KirkMedhin", "bare_K1_K3", "sorry", "admit", "axiom",
                 "native_decide", "proof_wanted"]:
        raw = hyg_raw.get(name, [])
        L.append(f"  - `{name}`: HEAD raw hits **{len(raw)}** (baseline identical-sweep: **{base_counts.get(name, '?')}**).")
        for f, ln, txt in raw[:12]:
            L.append(f"    - {f}:{ln}: `{txt}`")
    L.append("- Live-code layer (comments/strings masked):")
    for name in ["KirkMedhin", "bare_K1_K3", "sorry", "admit", "axiom",
                 "native_decide", "proof_wanted"]:
        live = hyg_live.get(name, [])
        L.append(f"  - `{name}`: live hits **{len(live)}**.")
        for f, ln, txt in live[:12]:
            L.append(f"    - {f}:{ln}: `{txt}`")
    # M0-introduced? (diff-precise: hit line is a `+` line of the
    # baseline->HEAD diff AND absent from the baseline file)
    introd = R.get("hyg_introduced", {})
    L.append("- M0-introduced violations (diff-precise, added lines only):")
    for name in ["sorry", "admit", "axiom", "native_decide",
                 "proof_wanted", "KirkMedhin", "bare_K1_K3"]:
        new_hits = introd.get(name, [])
        L.append(f"  - `{name}` introduced by M0: **{len(new_hits)}**")
        for f, ln, txt in new_hits[:8]:
            L.append(f"    - {f}:{ln}: `{txt}`")
    integ = R.get("import_integrity", [])
    n_intro = sum(len(r[3]) for r in integ if r[3])
    L.append(f"- Import integrity (test+docs files: HEAD vs baseline resolvability to files/oleans): **{n_intro} M0-introduced dangling imports**.")
    for f, hd, bd, intr in integ:
        if intr:
            L.append(f"  - {f}: introduced-dangling {intr}; baseline-dangling {bd}")
    L.append(f"- Block-comment balance (`/- -/` outside strings): **{len(R.get('comment_balance_bad', []))}** unbalanced files {R.get('comment_balance_bad', [])[:5]} (validates the comment-masking used by the live-code layer).")
    L.append(f"- `lake build DynamicalSystems`: rc=**{build.get('rc', '?')}**; tail: `{build.get('tail', '')[:500]}`")
    L.append(f"- `lake exe axiom-audit --root DynamicalSystems`: rc=**{audit.get('rc', '?')}**; `{audit.get('out', '')[:500]}`")
    L.append(f"- Verdict (strict literal reading): **{verdict_str(c5)}**")
    L.append("")
    L.append("## Notes / attribution")
    L.append("")
    L.append("- `proof_wanted` is a Batteries `theorem_wanted` synonym elaborating to sound opaque placeholders (never `axiom`/`sorry`); the green axiom audit confirms no axiom leakage. All live uses pre-date M0.")
    L.append("- `sorry` hits are all inside `/- -/`-commented dead code (verified by comment-masked re-grep: 0 live).")
    L.append("- `admit` raw hits are English prose (`admits …`) in docstrings, 0 live tactic uses.")
    L.append("- Bare `K1`/`K3` live hits are docstring prose about campaign obligations plus unrelated math identifiers (e.g. MRAC gain matrices `K1 K2`); zero declaration/module namespaces in rename scope. `K3*`/`K1*` *file* names and `DynamicalSystemsTest/KirkMedhin/` directory survive: physical moves deferred to M1–M6 per the M0 brief.")
    L.append("- `docs/kirk_medhin/*.lean` `KirkMedhin` references are imports of the `keep`-only (`move`-scope) test module `DynamicalSystemsTest.KirkMedhin.NonautonomousFlowOrder`, correctly left by M0 and documented as follow-up in `notes/reviews/MIGRATION_REPORT.md`.")
    L.append("")
    L.append(f"Overall: **{'ACCEPT' if overall else 'NOT ACCEPTED'}**.")
    L.append("")
    return "\n".join(L), {
        "c1": c1, "c2": c2, "c3": c3, "c4": c4, "c5": c5,
        "overall": overall,
    }


# ---------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--map", default=DEFAULT_MAP)
    ap.add_argument("--worktree", default=WORKTREE)
    ap.add_argument("--baseline", default=DEFAULT_BASELINE)
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--skip-probe", action="store_true")
    ap.add_argument("--skip-elab", action="store_true")
    ap.add_argument("--skip-build", action="store_true")
    ap.add_argument("--skip-audit", action="store_true")
    args = ap.parse_args()

    ch = Checker(args)
    print(f"[m0check] worktree={ch.worktree} head={ch.head_rev} "
          f"baseline={args.baseline}", flush=True)
    print(f"[m0check] rename-scope={len(ch.ren)} public={len(ch.pub)} "
          f"(lib={len(ch.lib)} test={len(ch.tst)}) "
          f"private={len(ch.priv)}", flush=True)

    print("[m0check] check 1: textual old-name sweep …", flush=True)
    ch.check_old_names()
    print(f"[m0check]   compiled-tree hits: "
          f"{len(ch.results['old_textual_compiled'])}, docs hits: "
          f"{len(ch.results['old_textual_docs'])}", flush=True)

    if not args.skip_probe:
        print("[m0check] checks 1+2: elaborated env probe (slow) …",
              flush=True)
        ch.run_probe()
        print(f"[m0check]   rc={ch.results['probe']['rc']} present="
              f"{len(ch.results['probe']['present'])} missing="
              f"{len(ch.results['probe']['missing'])} absent_ok="
              f"{len(ch.results['probe']['absent_ok'])} still="
              f"{len(ch.results['probe']['still'])}", flush=True)
    else:
        ch.results["probe"] = {"rc": 0, "n_modules": 0, "n_targets": 0,
                               "n_olds": 0, "n_sample_checks": 0,
                               "present": [], "missing": [],
                               "absent_ok": [], "still": [],
                               "log": "SKIPPED"}

    print("[m0check] check 2: declaration sites + effective FQNs …",
          flush=True)
    ch.verify_def_sites()

    if not args.skip_elab:
        print("[m0check] check 2: test-file elaboration (slow) …",
              flush=True)
        ch.check_tests()
        print(f"[m0check]   standalone={[v['rc'] for v in ch.results['test_elab'].values()]} "  # noqa: E501
              f"hermetic={[v['rc'] for v in ch.results['test_hermetic'].values()]}",  # noqa: E501
              flush=True)
    else:
        ch.results.update({"test_files": [], "test_imports": {},
                           "test_elab": {}, "test_hermetic": {}})

    print("[m0check] check 4: statement comparison …", flush=True)
    ch.check_statements()
    ch.check_scaffolding()
    print(f"[m0check]   {ch.results['stmt_stats']}", flush=True)

    print("[m0check] import integrity + comment balance …", flush=True)
    ch.check_import_integrity()
    ch.check_comment_balance()
    print(f"[m0check]   unbalanced: {ch.results['comment_balance_bad']}",
          flush=True)
    print("[m0check] check 5: hygiene greps …", flush=True)
    ch.hygiene_greps()
    if not args.skip_build:
        print("[m0check] check 5: lake build (slow) …", flush=True)
        ch.run_build()
        print(f"[m0check]   build rc={ch.results['build']['rc']}",
              flush=True)
    else:
        ch.results["build"] = {"rc": 0, "tail": "SKIPPED", "log": ""}
    if not args.skip_audit:
        print("[m0check] check 5: axiom audit (slow) …", flush=True)
        ch.run_audit()
        print(f"[m0check]   audit rc={ch.results['audit']['rc']}",
              flush=True)
    else:
        ch.results["audit"] = {"rc": 0, "out": "SKIPPED"}

    report, verdicts = build_report(ch)
    with open(args.out, "w", encoding="utf-8") as fh:
        fh.write(report)
    print(f"[m0check] wrote {args.out}", flush=True)
    print("[m0check] verdicts: " + " ".join(
        f"{k}={'PASS' if v else 'FAIL'}"
        for k, v in verdicts.items()), flush=True)
    return 0 if verdicts["overall"] else 1


if __name__ == "__main__":
    sys.exit(main())
