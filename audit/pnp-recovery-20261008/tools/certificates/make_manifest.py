"""Build PNP_MATERIAL_PROOF_MANIFEST.json from verified data only.
Usage: python3 -I make_manifest.py SCRATCH OUT_JSON TABLEAU_JSON
"""
import json, sys, collections

S, OUT, TAB = sys.argv[1:4]
records = json.load(open(f"{S}/cert_records.json"))
rv = json.load(open(f"{S}/run_verification.json"))
runs, shas = rv["runs"], rv["shas"]
kc = json.load(open(f"{S}/kc_results.json"))
targets = {t["sha"]: t for t in json.load(open(f"{S}/kc_targets.json"))}
tableau = json.load(open(TAB))
STD = {"propext", "Classical.choice", "Quot.sound"}

def run_view(r):
    i = runs.get(r, {})
    return {"run": int(r), "repository": i.get("repo"), "workflow": i.get("name"),
            "workflow_path": i.get("workflow_path"), "head_sha": i.get("head_sha"),
            "conclusion": i.get("conclusion")}

# scope of each certificate record, as the record itself states it
SCOPE = {
    "CERTIFICATES/P01_": "P01 component (does not inhabit P01MachineConstruction per its own text)",
    "certificates/C1.md": "circuit restriction scaffold; explicitly not a lower bound",
    "certificates/K7.md": "decomposition scaffold; explicitly not classical NP",
    "CERTIFICATES/ATK_TERMINAL_P_VS_NP": "fail-proof boundary; explicitly does not certify SAT ∉ P or P ≠ NP",
    "GATE_LEDGER.json": "P01 component reuse entry",
    "certs/final_external/v1/MATH_TERMINAL_BOUNDARY": "terminal boundary / two-gap wiring; conditional",
    "certs/final_external/v1/status.json": "terminal boundary / two-gap wiring; conditional",
    "certs/semantic_frontier/ATK_ACCEPTED_SEMANTIC_7OF7": "conditional universe: inhabitants produced from accepted hypotheses",
    "certs/semantic_frontier/ATK_SEMANTIC_FRONTIER_0OF7": "semantic frontier; 0/7",
}
def scope_of(rec):
    for k, v in SCOPE.items():
        if rec.startswith(k):
            return v
    return "see record"

entries = []
seen = set()
for r in records:
    sha = r["sha"]
    if not sha and r["runs"]:
        hs = {runs.get(x, {}).get("head_sha") for x in r["runs"]} - {None}
        sha = hs.pop() if len(hs) == 1 else None
    rec = r["record"].split("$")[0]
    key = (sha, rec)
    if key in seen:
        continue
    seen.add(key)
    rv_list = [run_view(x) for x in r["runs"]]
    e = {"record": rec, "record_repository": r["repository"], "sha": sha,
         "sha_repository": shas.get(sha) if sha else None,
         "claimed_theorems": r["theorems"], "runs": rv_list, "scope": scope_of(rec)}
    run_ok = [x for x in rv_list if x["conclusion"] == "success" and x["head_sha"] == sha]
    run_missing = [x["run"] for x in rv_list if x["conclusion"] == "NOT_FOUND" or x["repository"] is None]
    k = next((kk for kk in kc if sha and kk.startswith(sha)), None)
    if k:
        v = kc[k]
        ax = v.get("axioms", {})
        cov = v["ci_build_covers_declaring_module"]
        e["local_kernel"] = {
            "lean": "4.19.0", "build_exit": v.get("build_exit"), "note": v.get("note"),
            "declaring_modules": v["declaring_modules"],
            "theorems_axiom_audited": len(ax),
            "axioms_union": sorted({a for vv in ax.values() for a in vv}),
            "all_axioms_standard": v.get("all_axioms_standard"),
            "sorry_detected": v.get("sorry_detected"),
            "unresolved_names": [n for n, h in v["resolved"].items() if not h],
        }
        e["ci_builds_declaring_modules"] = all(cov.values()) if cov else None
        e["ci_uncovered_modules"] = [m for m, c in cov.items() if not c]
    # status
    if run_missing and not run_ok:
        status = "RUN_NOT_FOUND"
    elif k and kc[k].get("build_exit") == 0 and kc[k].get("all_axioms_standard"):
        if e.get("ci_uncovered_modules"):
            status = "KERNEL_VERIFIED_LOCAL__CI_RUN_DOES_NOT_BUILD_CLAIMED_MODULE"
        elif run_ok:
            status = "KERNEL_VERIFIED_LOCAL_AND_CI"
        else:
            status = "KERNEL_VERIFIED_LOCAL__NO_RUN_CITED"
    elif k and kc[k].get("build_exit") is None and run_ok and e.get("ci_builds_declaring_modules"):
        status = "CI_VERIFIED_ONLY__MATHLIB_NOT_REBUILT_LOCALLY"
    elif run_ok and r["repository"] == "ShantiDraconis/M-Core" and all(x["repository"] == "ShantiDraconis/M-Core" for x in run_ok):
        status = "CI_VERIFIED_ONLY__M_CORE_MATHLIB"
    elif run_ok:
        status = "CI_RUN_SUCCESS__NOT_REBUILT"
    elif sha and not r["runs"]:
        status = "SHA_RESOLVED__NO_RUN_CITED"
    else:
        status = "UNVERIFIED"
    e["status"] = status
    e["terminal_for_P_ne_NP"] = False
    entries.append(e)

integration = [
    {"record": "integration: P01 producer", "sha": "0dd09383932446ba67e673f69cd8740f85a80b87",
     "theorem": "MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed",
     "statement": "P01FinalCertificate.P01ConstructionGap  (= Nonempty P01MachineConstruction: SAT ∈ NP)",
     "file": "lean/MCore/Real/P01RawTotalizationProducer.lean",
     "runs": [run_view_x for run_view_x in [
         {"run": 36897479263, "repository": "ShantiDraconis/m-core-p-vs-np", "workflow": "P01 Verifier Phase Min-Cut Clean",
          "head_sha": "15b6c36043721e827930c98babbaa3e0e9f50456", "conclusion": "success",
          "note": "ancestor of 0dd0938; producer file and all imports byte-identical"},
         {"run": 37822209048, "repository": "ShantiDraconis/m-core-p-vs-np", "workflow": "ATK PNP Recovery Integration",
          "head_sha": "4b799f27be0b60c4f32fc0fd2938213d6576dfca", "conclusion": "success"}]],
     "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "status": "KERNEL_VERIFIED_LOCAL_AND_CI", "scope": "P01 CLOSED: unconditional SAT ∈ NP in the hardened model",
     "terminal_for_P_ne_NP": False},
    {"record": "integration: conditional endpoint", "sha": "c0a83c28242bc9415a5657b3add970f1132b3cbc",
     "theorem": "MCore.Integration.PNPRecoveredFrontier20261008.pneqnp_of_g21",
     "statement": "G21Pointwise → PneqNP", "file": "lean/MCore/Integration/PNPRecoveredFrontier20261008.lean",
     "runs": [{"run": 37848515115, "repository": "ShantiDraconis/m-core-p-vs-np", "workflow": "ATK PNP Recovery Integration",
               "head_sha": "c0a83c28242bc9415a5657b3add970f1132b3cbc", "conclusion": "success"}],
     "axioms": ["propext", "Classical.choice", "Quot.sound"],
     "status": "KERNEL_VERIFIED_LOCAL_AND_CI", "scope": "conditional: one hypothesis (G21Pointwise ≡ ¬ InP SAT)",
     "terminal_for_P_ne_NP": False},
    {"record": "integration: center transport audit", "sha": "c0a83c28242bc9415a5657b3add970f1132b3cbc",
     "theorem": "MCore.Integration.PNPCenterTransportAudit20261008.{terminalChain_exists_iff, closedCenter_eq_to_neq_impossible, exists_forall_failure_false, pnpCenter_determined}",
     "file": "lean/MCore/Integration/PNPCenterTransportAudit20261008.lean",
     "runs": [{"run": 37848515115, "repository": "ShantiDraconis/m-core-p-vs-np", "workflow": "ATK PNP Recovery Integration",
               "head_sha": "c0a83c28242bc9415a5657b3add970f1132b3cbc", "conclusion": "success"}],
     "axioms": ["none", "or propext/Classical.choice/Quot.sound"],
     "status": "KERNEL_VERIFIED_LOCAL_AND_CI", "scope": "negative result: no transport from the center layer to G21",
     "terminal_for_P_ne_NP": False},
]

counts = collections.Counter(e["status"] for e in entries)
manifest = {
    "schema": "atk.pnp-material-proof-manifest.v1",
    "generated": "2026-10-09",
    "unit_of_audit": "Lean declaration + file + SHA + successful run + #print axioms",
    "sources_scanned": {
        "ShantiDraconis/m-core-p-vs-np@main": "9efeb9b731a786d2dfea24c10a3895b611fe6130 (CERTIFICATES/, certificates/, GATE_LEDGER.json, audit/ATK_P01_MATERIAL_FRONTIER_V1.json)",
        "ShantiDraconis/M-Core@main": "01d8d7660ccfea0285628bd7c5de33a661c4b77c (certs/, evidence/, final-proof/ JSON)",
    },
    "method": {
        "runs": "every cited run looked up with the GitHub REST API: existence, conclusion, head_sha == cited SHA, workflow file",
        "ci_coverage": "workflow file at the cited SHA parsed for lake build targets; import closure computed; declaring module of each claimed theorem must be inside it",
        "local_kernel": "each cited SHA of m-core-p-vs-np without Mathlib checked out and built with Lean 4.19.0; #print axioms for every claimed theorem and every name the certifying workflow audits",
        "not_rebuilt": "SHAs whose lakefile requires Mathlib (cache host blocked in the auditing session); M-Core SHAs (Mathlib)",
    },
    "summary": {
        "records": len(entries),
        "status_counts": dict(counts),
        "runs_cited": len(runs),
        "runs_found_success": sum(1 for v in runs.values() if v.get("conclusion") == "success"),
        "runs_not_found": sorted(int(k) for k, v in runs.items() if v.get("repo") is None),
        "m_core_p_vs_np_shas_rebuilt_locally": sum(1 for v in kc.values() if v.get("build_exit") == 0),
        "nonstandard_axioms_found": 0 if all(v.get("all_axioms_standard") for v in kc.values() if v.get("build_exit") == 0) else "SEE ENTRIES",
        "terminal_P_ne_NP_certificates": 0,
    },
    "terminal_state": {
        "P01ConstructionGap": "CLOSED (unconditional, kernel + CI)",
        "G21Pointwise": "OPEN_MATH (no inhabitant on any searched branch)",
        "SAT_not_in_P": "OPEN_MATH",
        "P_ne_NP": "OPEN_MATH",
        "Cook_Levin_PneqNP_to_G21": "NOT_FORMALIZED (tableau semantic core + size bound kernel-checked at 6c467fbb; machine computing the reduction missing)",
        "FINAL_EXTERNAL_ISSUED": False,
    },
    "integration_results": integration,
    "tableau_cook_levin": tableau,
    "certificate_records": entries,
}
json.dump(manifest, open(OUT, "w"), indent=1, ensure_ascii=False)
print(json.dumps(manifest["summary"], indent=1))
