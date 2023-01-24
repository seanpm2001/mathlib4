#!/usr/bin/env python3

import sys
import os
from pathlib import Path
import subprocess
import re
import json

with open('fails.json') as fh:
    fails = json.load(fh)

with open('ml3.json') as fh:
    ml3 = json.load(fh)

align_files = subprocess.run(
    ['git', 'grep', '-l', '^#align'],
    capture_output=True,
    check=True,
    encoding='utf-8')

name_map = dict()
for f in align_files.stdout.splitlines():
    with open(f) as fh:
        contents = fh.read()
        for p in contents.split(sep='\n#align')[1:]:
            n3, n4, *_ = p.split(maxsplit=2)
            name_map[n4] = n3

for k,v in fails.items():
    if not k in name_map:
        continue
    x = name_map[k]
    if not x in ml3:
        print("MISSING IN ML3:", x, k, "?????", v)
        continue
    y = ml3[x]
    print("#align", x, k, "::", "#align", y, v)

