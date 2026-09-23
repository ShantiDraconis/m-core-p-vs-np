# FINAL_PROOF CANONICAL RECOVERY LANE

**Canonical repository:** `ShantiDraconis/m-core-p-vs-np`  
**Canonical branch:** `recovery/final-proof-all-reuse-20260923`  
**Canonical terminal aggregator:** `lean/MCore/Real/FinalProofRecoveryChain.lean`  
**Canonical chain manifest:** `recovery/FINAL_PROOF_CHAIN_20260923.json`  
**Certified SHA ledger:** `recovery/CERTIFIED_SHA_REUSE_20260923.json`

## DO NOT SWITCH REPOSITORY

For P-vs-NP FINAL_PROOF work, this repository/branch is the recovery source of truth.
Historical repositories such as `millennium-p-vs-np-I`, `millennium-p-vs-np-classical`,
and aggregator repositories may be mined for evidence or old files, but terminal work
must be imported here before it is treated as part of the chain.

## TERMINAL DELTA

Only two producers remain authoritative:

1. `P01ConstructionGap` via a concrete `P01MachineConstruction`.
2. `G21Pointwise` for the canonical `SATTarget`.

Everything after those two producers is reuse:

`P01ConstructionGap ∧ G21Pointwise`
→ `FinalExternalTwoGap`
→ `FinalExternalGap`
→ `FinalExternalCertificate`
→ `OfficialPneqNP`
→ `FINAL_ROOT`
→ `FINAL_PROOF[P_VS_NP]`.

## FAIL-CLOSED RULES

- Do not reopen the literal fixed-point G2.1 route; it is CLOSED_BY_FALSIFICATION.
- Do not replace `FINAL_ROOT` with any preparatory root.
- Do not promote a conditional theorem, interface, scaffold, CI success, or wiring theorem
  as a proof of either terminal producer.
- Imported historical files must record source branch/SHA in the recovery ledger.
