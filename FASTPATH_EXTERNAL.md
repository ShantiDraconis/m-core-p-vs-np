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


## Execution discipline
- Search/reuse before construction.
- Work only on the first unresolved producer in the canonical chain; downstream wiring remains untouched until its dependency is kernel-valid.
- A failed build repairs the same lane; it does not spawn a new mathematical route.
- A falsified statement is immutable and cannot be reintroduced under a renamed wrapper.
- Freeze only after source contains zero forbidden placeholders and the target builds.
- Certify only after target `#print axioms`, dependency/hygiene audit, and semantic-scope audit.
- External issuance is terminal: it consumes only the certified P01, D3/P02 and G3 producers and never substitutes metadata/audit GREEN for proof.

## Queue
ACTIVE: A1 realized transition-case completeness.
NEXT: A1 kernel build/hygiene/axioms.
THEN: A2 exact Kleene-to-canonical-SAT same-input producer.
THEN: D3/P02 promotion (existing source only).
THEN: P01/G3 validation and terminal external composition (existing source only).


## ATK reuse invariant
Before creating or reproving any theorem, lemma, certificate, adapter, workflow, or artifact:
1. search the active source, repository history, advanced/frozen branches, and existing certified interfaces;
2. if an equivalent stronger or directly reusable object exists, reference/import/compose it instead of rebuilding it;
3. create new source only for the smallest genuinely missing obligation;
4. never fork a second proof lane merely to rename or restate an existing result;
5. preserve provenance to the reused theorem/SHA/certificate.

This invariant is part of the canonical ATK fast-path discipline.
