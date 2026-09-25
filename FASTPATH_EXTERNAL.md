# P vs NP — canonical no-loop fast path

Status: FAIL-CLOSED / OPEN_MATH

This file is routing metadata only. It does not replace, delete, rename, weaken, or certify any mathematical source.

## Preservation rule
- Every historical file, branch, frozen SHA, certificate, falsification, and audit remains preserved.
- No deletion, overwrite of historical snapshots, or promotion from CI GREEN to theorem proof.
- No `sorry`, `admit`, `sorryAx`, new axioms, hidden oracle, circularity, or target-as-hypothesis is accepted for certification.

## Canonical active route
1. `P02BoundedComputationClose.executionAssignment_transitionCaseCNF`
2. `executionAssignment_transitionsCNF`
3. `executionAssignment_boundedExecTableauCNF`
4. `tableauCompletenessCertificate`
5. `boundedExecCorrectness_closed`
6. construct `CanonicalSATKleeneRealizerGap` with same-input semantic fidelity
7. `canonicalSATKleeneRealizerGap_to_D3`
8. `D3_to_G21Pointwise` / `D3_to_P02Target`
9. combine real P01 + D3 + real G3 through `P01_D3_G3_to_external_final`
10. only after kernel build + hygiene + axiom/dependency/semantic audits: freeze/certify and emit terminal external artifacts.

## Hard exclusions
- Literal bitstring fixed-point G2.1: CLOSED_BY_FALSIFICATION; never re-enter.
- Exact compiler/same-input routes already falsified: historical evidence only.
- Empty/0/0 endpoints and infrastructure certificates: never count as theorem producers.
- Side lanes may supply lemmas but never become alternate terminal routes.

## Current exact frontier
A1 has one explicit local `sorry` in the newly constructed active transition-case completeness proof. Therefore A1 is RED/OPEN until removed and kernel checked.
A2 remains OPEN_MATH: code/fixed-point semantics must be transported to the exact canonical SAT same-input witness without assuming the lower-bound conclusion.

The terminal wiring after a genuine D3 producer already exists; do not rebuild it.
