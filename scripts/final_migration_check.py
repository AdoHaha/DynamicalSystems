#!/usr/bin/env python3
"""Final conformance + hygiene check of the optimal-control concept-organization migration."""
import json, pathlib, re, subprocess, sys
W = pathlib.Path("/home/igor/zabawy/auto_automatyk/.worktrees/kirk_medhin-migrate")
MAP = pathlib.Path("/home/igor/zabawy/auto_automatyk/notes/reviews/optimal_control_declaration_map.json")
d = json.loads(MAP.read_text()); decls = d["declarations"]
lean = list(W.glob("DynamicalSystems/**/*.lean")) + list(W.glob("DynamicalSystemsTest/**/*.lean"))
text = "\n".join(p.read_text(errors="ignore") for p in lean)

# C1 old names gone (qualified identifier boundary, masked comments)
def masked(t): return re.sub(r"/-.*?-/", "", t, flags=re.S)
live = masked(text)
old_hits = [e["old_fqn"] for e in decls if e["old_fqn"].split(".")[-1]
            and re.search(r"(?<![\w.])"+re.escape(e["old_fqn"])+r"(?![\w])", live)
            and e["old_fqn"] not in e["target_fqn"]]
print(f"C1 old_fqn still resolving: {len(old_hits)}"); [print("  ",h) for h in old_hits[:10]]

# C2/C3 target present at target_path + leaf resolves textually
mp=[e for e in decls if not (W/e["target_path"]).exists()]
mn=[e for e in decls if (W/e["target_path"]).exists() and e["target_fqn"].split(".")[-1] not in (W/e["target_path"]).read_text(errors="ignore")]
print(f"C2/C3 targets present: {len(decls)-len(mp)-len(mn)}/{len(decls)}; missing files {len(mp)}; missing names {len(mn)}")
for e in mn[:10]: print("   name-", e["target_fqn"], "@", e["target_path"])

# C5 hygiene
print("C5 KirkMedhin (live):", len(re.findall(r"KirkMedhin", live)))
print("C5 bare K1/K3 namespace decls:", len(re.findall(r"namespace (K1|K3)\b", live)))
for bad in ("sorry","admit","axiom","native_decide"):
    n=len(re.findall(r"\b"+bad+r"\b", live)); print(f"C5 live {bad}: {n}")
