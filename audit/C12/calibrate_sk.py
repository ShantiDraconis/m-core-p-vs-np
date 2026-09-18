#!/usr/bin/env python3
import csv, json, sys
from fractions import Fraction
from pathlib import Path

WEIGHTS = [
    ("1/2,1/2", Fraction(1,2), Fraction(1,2)),
    ("1,2", Fraction(1), Fraction(2)),
    ("2,1", Fraction(2), Fraction(1)),
    ("1/10,10", Fraction(1,10), Fraction(10)),
    ("10,1/10", Fraction(10), Fraction(1,10)),
    ("1,1", Fraction(1), Fraction(1)),
]

def read_rows(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f))

def classify(rows):
    out = {}
    baseline = []
    for r in rows:
        dv = int(r["deltaVars"])
        dr = int(r["deltaRank"])
        cb = int(r["costBits"])
        baseline.append(cb < dv + dr)
    for label,a,b in WEIGHTS:
        vals = []
        flips = 0
        for base,r in zip(baseline, rows):
            dv = int(r["deltaVars"])
            dr = int(r["deltaRank"])
            cb = int(r["costBits"])
            v = Fraction(cb) < a*dv + b*dr
            vals.append(v)
            if v != base:
                flips += 1
        out[label] = {
            "rows": len(rows),
            "true": sum(vals),
            "false": len(vals)-sum(vals),
            "flips_vs_1_1": flips,
            "flip_fraction": (flips/len(rows) if rows else 0.0),
        }
    return out

def main():
    if len(sys.argv) < 4:
        raise SystemExit("usage: calibrate_sk.py OUT.json C12.csv C13.csv")
    outp = Path(sys.argv[1])
    c12 = read_rows(sys.argv[2])
    c13 = read_rows(sys.argv[3])
    result = {
        "schema":"PNP_C12_SK_CALIBRATION_V1",
        "scientific_promotion":"NONE",
        "S":{
            "status":"OPEN_BRIDGE",
            "reason":"No theorem yet identifies Potential/costBits with official TM time or unrestricted circuit size."
        },
        "K":{
            "c12":classify(c12),
            "c13":classify(c13),
        }
    }
    # Fail-closed classification: any observed flip proves the current finite
    # phenomenon is parameter-sensitive.  Zero flips is evidence only.
    total_flips = sum(v["flips_vs_1_1"] for group in result["K"].values() for k,v in group.items() if k!="1,1")
    result["K"]["classification"] = "FINITE_PARAMETER_SENSITIVE" if total_flips else "FINITE_ROBUSTNESS_EVIDENCE_ONLY"
    result["K"]["total_flips"] = total_flips
    outp.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result,sort_keys=True))

if __name__ == "__main__":
    main()
