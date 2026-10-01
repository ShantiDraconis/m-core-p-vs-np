# ATK P01 Frozen Checkpoints — 2026-10-01

STATUS: FROZEN_EVIDENCE_ONLY
POLICY: Do not reopen or reinterpret frozen GREEN checkpoints. New work must proceed strictly from the current frontier. Historical GREEN evidence remains immutable even if later SHAs fail.

## FROZEN_GREEN_PRETERMINAL

SHA: 5ef98cdf6551836f656291254eb5486c1d2107a2
BRANCH_AT_RUN: atk/p01-verifier-phase-mincut-clean-20260930

Evidence:
- certificate run 36792966912 — SUCCESS
- fail-proof-all-gaps run 36792966894 — SUCCESS

Certified by those runs at that SHA:
- source hygiene gate
- K-chain / C1-C11 preservation
- C12 family layer
- CNFStructure build + axiom audit
- Semantics build + axiom audit
- SATMachine build + interface axiom audit
- FinalProof targeted build
- CanonicalFinalProof build + hardened endpoint axiom audit
- CanonicalPSubsetNP + CanonicalComplexityBridge build + axiom audit
- FailProofAllGaps + FailProofFiniteAttack + CanonicalSATBoundary build + axiom audit
- CanonicalCircuitBits + CanonicalSATWitness + CanonicalSATVerifier build + axiom audit
- P01EvalStepFrameRefinement build + axiom audit
- C12 semantic-proxy counterexample reproduction
- FinalProofAttack build + axiom audit
- bidirectional structural audit
- C12 semantic axiom audit
- C12 endpoint-language firewall
- C12 deterministic distribution + baseline analysis
- C13 bidirectional probe
- C12 open-obligation / non-promotion firewall
- backward oracle A-B endpoint test
- backward dense endpoint audit
- fail-proof-all-gaps jobs: canonical-model, gap-compression, sat-foundations, negative-attacks — all SUCCESS

Interpretation:
FROZEN and CERTIFIED for the exact tested scope above at SHA 5ef98cdf6551836f656291254eb5486c1d2107a2.
DOES_NOT_CERTIFY: P01RawClosureFinal or the later raw-total verifier closure introduced on subsequent SHAs.

## FROZEN_PARTIAL_FINAL_ROOT

SHA: 63ad057d1bcbad46ab537e0a2dcf8b863322e7ac
BRANCH_AT_RUN: atk/auto-compose-terminal-20260930

Evidence:
- ATK FINAL ROOT run 36792757656 — SUCCESS
  - job final-root — SUCCESS
  - Build FINAL_ROOT — SUCCESS

Same-SHA counter-evidence:
- certificate run 36792757604 — FAILURE
- fail-proof-all-gaps run 36792757677 — FAILURE

Interpretation:
FROZEN as a historical successful FINAL_ROOT workflow checkpoint only.
NOT CERTIFIED as a full P01 terminal closure because broader validation failed on the same SHA.

## CURRENT_FRONTIER_NOT_FROZEN_AS_GREEN

Current development branch:
atk/p01-raw-closure-final-20261001

Latest known failed pre-protection SHA:
f38d59f16288dab78712b2da9a12ad64122357e3

Known failing runs:
- fail-proof-all-gaps 36796944459 — FAILURE
- certificate 36796944391 — FAILURE

Subsequent no-Actions repair commits:
- a4134928ab524e692654f3ab47c677c6486329bc
- f34d3f768796de649d3f40a64602394b8dc0bcb1

These repair commits are NOT promoted to GREEN or CERTIFIED without a real Lean execution.
They are protected from automatic Actions execution.

## FORWARD-ONLY RULE

Do not reopen FROZEN_GREEN_PRETERMINAL.
Do not rerun already-certified intermediate layers merely to rediscover the same facts.
Only validate the remaining current frontier needed to close P01RawClosureFinal.
