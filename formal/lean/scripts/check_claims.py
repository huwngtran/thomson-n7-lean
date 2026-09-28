#!/usr/bin/env python3
"""usage: check_claims.py            (from anywhere; paths in claims.tsv are relative to the repository root)

Checks claims.tsv against the Lean files, so that a line number cited in paper/PAPER.md cannot silently go stale:
  * every row's line really declares its name (theorem/lemma/def/abbrev/structure/..., or `namespace X` for kind=region);
  * the theorems named in ComparatorChallenges/thomson_n7.comparator.json each have a `main theorem` row
    (in ThomsonN7/Solution.lean) and a `statement` row (in ComparatorChallenges/ThomsonN7.lean).
No Lean build is needed. Exit 1 on any failure."""
import json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KW = r"(?:theorem|lemma|def|abbrev|structure|instance|inductive|class)"
files, rows, fails = {}, [], []


def lines_of(rel):
    if rel not in files:
        with open(os.path.join(ROOT, rel), encoding="utf-8") as f:
            files[rel] = f.read().split("\n")
    return files[rel]


with open(os.path.join(ROOT, "claims.tsv"), encoding="utf-8") as f:
    for raw in f:
        raw = raw.rstrip("\n")
        if not raw or raw.startswith("#") or raw.startswith("name\t"):
            continue
        name, rel, line, kind, section, topic = raw.split("\t")
        rows.append((name, rel, int(line), kind, section, topic))

for name, rel, line, kind, section, topic in rows:
    src = lines_of(rel)
    last = re.escape(name.split(".")[-1])
    if not 1 <= line <= len(src):
        fails.append(f"{name} @ {rel}:{line}: line out of range (file has {len(src)} lines)")
        continue
    text = src[line - 1]
    pat = rf"^\s*namespace\s+{last}\b" if kind == "region" else rf"\b{KW}\s+(?:[\w.]*\.)?{last}\b"
    if not re.search(pat, text):
        fails.append(f"{name} @ {rel}:{line}: found {text.strip()[:80]!r}")

cfg = json.load(open(os.path.join(ROOT, "ComparatorChallenges", "thomson_n7.comparator.json"), encoding="utf-8"))
for full in cfg["theorem_names"]:
    short = full.split(".")[-1]
    for kind in ("main theorem", "statement"):
        if not any(r[0] == short and r[3] == kind for r in rows):
            fails.append(f"{full}: no `{kind}` row in claims.tsv")

print(f"claims.tsv: {len(rows)} rows checked against {len(files)} Lean files")
for f_ in fails:
    print("FAIL", f_)
print("CLAIMS CHECK:", "FAILED" if fails else "OK")
sys.exit(1 if fails else 0)
