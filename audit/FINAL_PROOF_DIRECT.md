# Direct Final-Proof Attack — P versus NP

STATUS: DIRECT_ENDPOINT_WIRED / TARGET_CERTIFICATE_NOT_EMITTED

BASE_FROZEN: 7ab06d0430e48a323b1ed0096abe97762303c893
BRANCH: work/final-proof-direct-from-7ab06d04

## Endpoint

The direct machine-model endpoint is:

`MachinePneqNP := ¬ ∀ L, InP L ↔ InNP L`.

The new theorem is:

`SATInNP -> SATNotInP -> MachinePneqNP`.

No SAT-completeness theorem is required for this implication: a single language in NP and outside P separates the classes.

## Positive lower-bound certificate

`SATLowerBoundCertificate` is the operational fail-closed target:

for every `PolyDTMCandidate`, produce a concrete Circuit `φ` for which the candidate is not correct on SAT.

The module proves:

`UniversalSATFailure ↔ SATNotInP`.

Thus the fail proof is exactly equivalent, inside the concrete machine model, to excluding every deterministic polynomial-time SAT decider.

## Current residue

`FINAL_PROOF_RESIDUAL := SATInNP ∧ SATLowerBoundCertificate`.

- `SATInNP`: infrastructure/formal machine witness still needs an inhabited polynomial-time NTM realization.
- `SATLowerBoundCertificate`: genuine lower-bound frontier. This is the mathematical separation content.

Finite timings, PARI/Sage/ellrank behavior, C12/C13 data, bounded search, or a single algorithm's exponential behavior do not inhabit `SATLowerBoundCertificate`.

## Promotion rule

Emit a separation certificate only when `FINAL_PROOF_RESIDUAL` is inhabited and the targeted Lean + axiom gates are GREEN.

No `sorry`, `admit`, source-level axioms, benchmark-to-lower-bound promotion, or hidden endpoint premise is permitted.
