#!/usr/bin/env python3

import sys
import os
import subprocess
import re
import json
from pathlib import Path

# Download a recent artifact.zip from https://github.com/leanprover-community/doc-gen/actions,
# unzip it to obtain export.json (~200MB) and then run
# jq '[ .decls[] | {name: .name, filename: .filename, attributes: .attributes, is_meta: .is_meta } ]' < export.json > 2.json

LEAN3REPO = "/home/lean/.elan/toolchains/leanprover-community--lean---3.50.3/lib/lean/library/"
MATHLIB3REPO = "/home/lean/actions-runner/_work/doc-gen/doc-gen/mathlib/src/"

MYLEANREPO = "lean/library/"
MYMATHLIBREPO = "mathlib/src/"

mathlib4_root = 'Mathlib/'

source_module_re = re.compile(r"^! .*source module (.*)$")
commit_re = re.compile(r"^! leanprover-community/(mathlib|lean) commit ([0-9a-f]*)$")
import_re = re.compile(r"^import ([^ ]*)")

def get_mathlib4_module_commit_info(contents):
    module, repo, commit = None, None, None
    for line in contents.split('\n'):
        m = source_module_re.match(line)
        if m:
            module = m.group(1)
        m = commit_re.match(line)
        if m:
            repo = m.group(1)
            commit = m.group(2)
        if import_re.match(line):
            break
    return module, repo, commit

# Lean 3 file name -> Set(all Lean 3 names in #align statements)
aligned_defs = dict()
for path4 in Path(mathlib4_root).glob('**/*.lean'):
    contents = open(path4).read()

    module, repo, commit = get_mathlib4_module_commit_info(path4.read_text())
    if module is None:
        continue

    assert commit is not None

    if repo == 'lean':
        lean3_filename = LEAN3REPO + module.replace('.', '/') + ".lean"
    elif repo == 'mathlib':
        lean3_filename = MATHLIB3REPO + module.replace('.', '/') + ".lean"
    else:
        assert False, repo

    lean3_names = set()
    for p in contents.split(sep='\n#align')[1:]:
        n3, n4, *_ = p.split(maxsplit=2)
        lean3_names.add(n3)
    for p in contents.split(sep='\n#noalign')[1:]:
        n3, *_ = p.split(maxsplit=1)
        lean3_names.add(n3)

    aligned_defs[lean3_filename] = lean3_names

# print(aligned_defs)

lean3_decls = json.load(open('2.json'))

# Lean 3 file name -> Set(Lean 3 defs in original file)
optional_defs = dict()
original_defs = dict()
for d in lean3_decls:
    if d["filename"] not in aligned_defs:
        continue
    if "instance" in d["attributes"] or d["is_meta"] or d["name"].startswith("library_note."):
        optional_defs.setdefault(d["filename"], set())
        optional_defs[d["filename"]].add(d["name"])
    else:
        original_defs.setdefault(d["filename"], set())
        original_defs[d["filename"]].add(d["name"])

for f in aligned_defs:
    if f not in original_defs and f not in optional_defs:
        print("\nWhat happened to my file?", f)
        continue

    optional_defs.setdefault(f, set())
    original_defs.setdefault(f, set())

    printed_header = False

    if not original_defs[f] <= aligned_defs[f]:
        print("\n===== File", f.replace(MATHLIB3REPO, MYMATHLIBREPO).replace(LEAN3REPO, MYLEANREPO), "=====")
        printed_header = True
        print("Missing aligns:", original_defs[f] - aligned_defs[f])

    if not aligned_defs[f] <= original_defs[f] | optional_defs[f]:
        if not printed_header:
            print("\n===== File", f.replace(MATHLIB3REPO, MYMATHLIBREPO).replace(LEAN3REPO, MYLEANREPO), "=====")
        print("Phantom aligns:", aligned_defs[f] - (original_defs[f] | optional_defs[f]))
