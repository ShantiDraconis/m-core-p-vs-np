# ATK P01 Frozen Checkpoints — 2026-10-01

STATUS: FROZEN_EVIDENCE_ONLY
POLICY: Any theorem/build/audit explicitly proven by a SUCCESS step below is frozen as historical evidence and must not be reopened merely because later SHAs fail. New work proceeds strictly from the current frontier.

## LATEST_FROZEN_CERTIFIED_PRETERMINAL

SHA: 5866dbefc58db33a1bd04cd45924a99444e113b5
BRANCH_AT_RUN: atk/p01-verifier-phase-mincut-clean-20260930

Evidence:
- certificate run 36793219387 — SUCCESS
- fail-proof-all-gaps run 36793219377 — SUCCESS

Frozen/certified tested scope:
- G0 fail-closed source hygiene
- K-chain / C1-C11 preservation
- C12 family layer
- MCore.Real.CNFStructure build + axiom audit
- MCore.Real.Semantics build + axiom audit
- MCore.Real.SATMachine build + interface axiom audit
- MCore.Real.FinalProof targeted build
- MCore.Real.CanonicalFinalProof build + hardened endpoint axiom audit
- MCore.Real.CanonicalPSubsetNP build + axiom audit
- MCore.Real.CanonicalComplexityBridge build + axiom audit
- MCore.Real.FailProofAllGaps build + axiom audit
- MCore.Real.FailProofFiniteAttack build + axiom audit
- MCore.Real.CanonicalSATBoundary build + axiom audit
- MCore.Real.CanonicalCircuitBits build + axiom audit
- MCore.Real.CanonicalSATWitness build + axiom audit
- MCore.Real.CanonicalSATVerifier build + axiom audit
- MCore.Real.P01EvalStepFrameRefinement build + axiom audit
- canonical SAT NTM attack + axiom audit
- canonical SAT parser attack + axiom audit
- canonical SAT unary payload attack + axiom audit
- C12 semantic-proxy counterexample reproduction
- arbitrary-encoder / finite-evidence negative attacks
- FinalProofAttack build + axiom audit
- direct final-proof compression axiom audit
- bidirectional structural audit
- C12 semantic axiom audit
- C12 endpoint-language firewall
- deterministic C12 distribution + baseline analysis
- targeted C13 bidirectional probe
- C12 open-obligation / non-promotion firewall
- backward oracle A-B endpoint test
- backward dense endpoint audit
- fail-proof-all-gaps jobs canonical-model, gap-compression, sat-foundations, negative-attacks — all SUCCESS

Interpretation:
FROZEN + CERTIFIED for the exact tested scope above at SHA 5866dbefc58db33a1bd04cd45924a99444e113b5.
DOES_NOT_CERTIFY: later P01RawClosureFinal/raw-total-verifier work not present in this successful checkpoint.

## HISTORICAL_DOUBLE_GREEN_CHECKPOINTS

The following SHAs also had BOTH certificate and fail-proof-all-gaps SUCCESS and are frozen as historical GREEN checkpoints:

- fce084db2732093eba3de30686f2e835c26ec313
  - certificate 36793121102 — SUCCESS
  - fail-proof-all-gaps 36793121035 — SUCCESS
- 5ef98cdf6551836f656291254eb5486c1d2107a2
  - certificate 36792966912 — SUCCESS
  - fail-proof-all-gaps 36792966894 — SUCCESS
- 0f09a3f08af112a033bf09adc8b3c378f16c9744
  - certificate 36792830464 — SUCCESS
  - fail-proof-all-gaps 36792830690 — SUCCESS
- 74c78cee6e5ebf04236e7d586debaab390b03977
  - certificate 36792811950 — SUCCESS
  - fail-proof-all-gaps 36792811883 — SUCCESS
- 1b801d24673c9cbfb8f88b559568863a09978b8b
  - certificate 36792790480 — SUCCESS
  - fail-proof-all-gaps 36792790411 — SUCCESS
- 10e09673c376672714055c22877c790e471799fa
  - certificate 36792786099 — SUCCESS
  - fail-proof-all-gaps 36792786224 — SUCCESS
- 12f47f6d17e87c91e03cbdc1dcafb0c985b9b5ee
  - certificate 36792647643 — SUCCESS
  - fail-proof-all-gaps 36792647615 — SUCCESS
- ebdd898381a7bf377aa0c517422b57d356f20702
  - certificate 36792619400 — SUCCESS
  - fail-proof-all-gaps 36792619360 — SUCCESS

These checkpoints are immutable historical evidence. The newest one, 5866dbef..., supersedes them only as the preferred reference; it does not erase them.

## FROZEN_PARTIAL_FINAL_ROOT

SHA: 63ad057d1bcbad46ab537e0a2dcf8b863322e7ac
BRANCH_AT_RUN: atk/auto-compose-terminal-20260930

Evidence:
- ATK FINAL ROOT run 36792757656 — SUCCESS
  - final-root job — SUCCESS
  - Build FINAL_ROOT — SUCCESS

Same-SHA counter-evidence:
- certificate run 36792757604 — FAILURE
- fail-proof-all-gaps run 36792757677 — FAILURE

Interpretation:
FROZEN as a successful FINAL_ROOT workflow checkpoint only.
NOT CERTIFIED as complete P01 terminal closure.

## CURRENT_FRONTIER_NOT_FROZEN_AS_GREEN

Current development branch:
atk/p01-raw-closure-final-20261001

Last failed pre-protection SHA:
f38d59f16288dab78712b2da9a12ad64122357e3

Runs:
- fail-proof-all-gaps 36796944459 — FAILURE
- certificate 36796944391 — FAILURE

No-Actions repair commits:
- a4134928ab524e692654f3ab47c677c6486329bc
- f34d3f768796de649d3f40a64602394b8dc0bcb1

These repair commits remain UNVERIFIED until a real Lean execution exists. They are not promoted to GREEN/CERTIFIED by static analysis alone.

## FREEZE RULE

1. Never reopen or rerun a frozen theorem/build/audit merely because later code fails.
2. Preserve the exact successful SHA and run IDs as provenance.
3. Later failures do not invalidate an earlier successful checkpoint; they only constrain later deltas.
4. Only the unverified delta from the latest frozen checkpoint to P01RawClosureFinal remains eligible for new proof/debug work.
5. No claim of full P01 terminal closure is permitted until the current frontier receives real successful Lean validation.
