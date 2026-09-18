#!/usr/bin/env python3
import csv
import hashlib
import json
import sys
from collections import Counter, defaultdict
from pathlib import Path

src = Path(sys.argv[1] if len(sys.argv) > 1 else "distribution.csv")
out = Path(sys.argv[2] if len(sys.argv) > 2 else "audit/C12_REAL_DATA_BASELINE.generated.json")

raw = src.read_bytes()
digest = hashlib.sha256(raw).hexdigest()
with src.open(newline="", encoding="utf-8") as f:
    rows = list(csv.DictReader(f))

if not rows:
    raise SystemExit("empty distribution")

def as_int(r, key):
    return int(r[key])

def pays(r):
    return r["paysOff"].strip().lower() == "true"

families = sorted({r["family"] for r in rows})
family_counts = Counter(r["family"] for r in rows)
payoff_counts = Counter("true" if pays(r) else "false" for r in rows)

family_stats = {}
for fam in families:
    rs = [r for r in rows if r["family"] == fam]
    t = sum(pays(r) for r in rs)
    family_stats[fam] = {
        "rows": len(rs),
        "paysOff_true": t,
        "paysOff_false": len(rs) - t,
        "true_fraction": t / len(rs),
        "min_deltaRank": min(as_int(r, "deltaRank") for r in rs),
        "max_deltaRank": max(as_int(r, "deltaRank") for r in rs),
        "min_costBits": min(as_int(r, "costBits") for r in rs),
        "max_costBits": max(as_int(r, "costBits") for r in rs),
    }

# Canonical finite analogue of A0:
# or/and/reducible use their generated restrictions; random_k_cnf uses seed 0,
# matching the family used in QuantitativeCore.
canonical = [
    r for r in rows
    if r["family"] != "random_k_cnf" or as_int(r, "seed") == 0
]
groups = defaultdict(list)
for r in canonical:
    groups[(r["family"], as_int(r, "n"))].append(r)

coverage = {}
witness_k = {}
missing_groups = []
for (fam, n), rs in sorted(groups.items()):
    good = [r for r in rs if pays(r)]
    key = f"{fam}:n={n}"
    coverage[key] = bool(good)
    witness_k[key] = min((as_int(r, "k") for r in good), default=None)
    if not good:
        missing_groups.append(key)

expected_groups = [(fam, n) for fam in families for n in range(1, 13)]
missing_expected = [
    f"{fam}:n={n}" for fam, n in expected_groups if (fam, n) not in groups
]

# Random-family robustness across all four deterministic seeds.
random_seed_groups = defaultdict(list)
for r in rows:
    if r["family"] == "random_k_cnf":
        random_seed_groups[(as_int(r, "seed"), as_int(r, "n"))].append(r)
random_seed_coverage = {
    f"seed={seed}:n={n}": any(pays(r) for r in rs)
    for (seed, n), rs in sorted(random_seed_groups.items())
}

# Margin > 0 iff PaysOff is true.
margins = [as_int(r, "potentialBefore") - as_int(r, "payoffLhs") for r in rows]
false_rows = [r for r in rows if not pays(r)]
zero_cost = [r for r in rows if as_int(r, "costBits") == 0]

by_n = {}
for n in range(1, 13):
    rs = [r for r in rows if as_int(r, "n") == n]
    t = sum(pays(r) for r in rs)
    by_n[str(n)] = {
        "rows": len(rs),
        "paysOff_true": t,
        "paysOff_false": len(rs) - t,
        "true_fraction": t / len(rs) if rs else None,
    }

summary = {
    "schema": "C12_REAL_DATA_BASELINE_v1",
    "epistemic_status": "FINITE_DETERMINISTIC_EVIDENCE_ONLY / NO_P_VS_NP_PROMOTION",
    "source_sha256": digest,
    "data_rows": len(rows),
    "header_plus_rows": len(rows) + 1,
    "families": families,
    "family_counts": dict(family_counts),
    "paysOff_counts": dict(payoff_counts),
    "family_stats": family_stats,
    "canonical_A0_sample": {
        "sizes": [1, 12],
        "expected_family_size_groups": len(expected_groups),
        "observed_family_size_groups": len(groups),
        "missing_expected_groups": missing_expected,
        "groups_with_sampled_witness": sum(coverage.values()),
        "groups_without_sampled_witness": missing_groups,
        "all_48_groups_have_sampled_witness": len(groups) == len(expected_groups) and all(coverage.values()),
        "minimum_witness_k_by_group": witness_k,
    },
    "random_seed_robustness": {
        "groups": len(random_seed_coverage),
        "groups_with_sampled_witness": sum(random_seed_coverage.values()),
        "groups_without_sampled_witness": [k for k, v in random_seed_coverage.items() if not v],
    },
    "margins": {
        "min_potentialBefore_minus_payoffLhs": min(margins),
        "max_potentialBefore_minus_payoffLhs": max(margins),
        "zero_margin_rows": sum(m == 0 for m in margins),
        "negative_margin_rows": sum(m < 0 for m in margins),
    },
    "zero_costBits": {
        "rows": len(zero_cost),
        "paysOff_true": sum(pays(r) for r in zero_cost),
        "paysOff_false": sum(not pays(r) for r in zero_cost),
    },
    "false_rows": {
        "count": len(false_rows),
        "by_family": dict(Counter(r["family"] for r in false_rows)),
        "first_20_coordinates": [
            {
                "family": r["family"],
                "n": as_int(r, "n"),
                "k": as_int(r, "k"),
                "seed": as_int(r, "seed"),
                "costBits": as_int(r, "costBits"),
                "deltaRank": as_int(r, "deltaRank"),
                "margin": as_int(r, "potentialBefore") - as_int(r, "payoffLhs"),
            }
            for r in false_rows[:20]
        ],
    },
    "by_n": by_n,
    "interpretation_guard": [
        "A sampled witness for every n<=12 is not a proof of FamilyPayoffObligation.",
        "PaysOff is an internal potential inequality, not polynomial-time runtime.",
        "No finite statistic here orients the classical discriminant D.",
    ],
}

out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps(summary, sort_keys=True))
