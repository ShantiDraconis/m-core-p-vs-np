#!/usr/bin/env python3
from __future__ import annotations
import argparse
import pathlib
import re
import sys

BAD_TERM = re.compile(r"(^|[^A-Za-z0-9_])(sorry|admit)([^A-Za-z0-9_]|$)")
BAD_DECL = re.compile(r"^\s*(?:@\[[^]]*\]\s*)?(axiom|constant|constants)\s+", re.M)

def main() -> int:
    ap = argparse.ArgumentParser(description="Fail-closed Lean source audit.")
    ap.add_argument("paths", nargs="+")
    ns = ap.parse_args()
    bad = []
    checked = 0
    for raw in ns.paths:
        p = pathlib.Path(raw)
        files = [p] if p.is_file() else sorted(p.rglob("*.lean"))
        for f in files:
            if f.suffix != ".lean":
                continue
            checked += 1
            text = f.read_text(encoding="utf-8")
            for i, line in enumerate(text.splitlines(), 1):
                if BAD_TERM.search(line):
                    bad.append(f"{f}:{i}: forbidden proof placeholder")
                if BAD_DECL.search(line):
                    bad.append(f"{f}:{i}: forbidden axiom/constant declaration")
    print(f"[LEAN-AUDIT] checked={checked}")
    if bad:
        print("\n".join(bad))
        print("[LEAN-AUDIT] RED")
        return 1
    print("[LEAN-AUDIT] PASS")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
