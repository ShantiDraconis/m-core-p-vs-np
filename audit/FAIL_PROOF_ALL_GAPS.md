# P vs NP — All-Gaps Fail-Proof Attack

STATUS: PARALLEL_GAP_ATTACK / NO CLAY PROMOTION
BASE_FROZEN: 65dda6873168597c20bca30e3243b725fddae472
WORK_BRANCH: work/fail-proof-all-gaps-from-65dda687

## Compressed frontier

The direct fail-proof endpoint is compressed to three substantive objects.

### G1 — NP target

Provide one explicit bitstring language L together with:

- an exact syntax/bitstring boundary when L is SAT;
- a concrete finite-control NTM in the hardened canonical model;
- a fixed polynomial time bound;
- a proof that the NTM decides L on every bitstring input.

For SAT this is represented by CanonicalSATBoundary.CircuitBitEncoding and CanonicalSATBoundary.SATInNPGap.

### G2 — Universal deterministic fail proof

Provide FailureGenerator L.

This assigns to every PolyDTMCandidate a concrete bitstring on which that candidate is not correct for L.

The repository proves:
- Nonempty (FailureGenerator L) <-> UniversalFailure L;
- UniversalFailure L <-> not InP L.

This is the Clay-level lower-bound content.

### G3 — external/official model match

Provide ExternalModelMatch officialP officialNP.

This proves membership equivalence between the hardened finite-control, canonical-input bitstring model and the selected external formalization.

The repository proves that internal separation transfers through this match.

## All-gap closure

FinalGapCertificate officialP officialNP contains:
- one target language;
- proof target is in internal NP;
- one universal failure generator;
- one external model match.

final_gap_certificate_closes proves the external separation endpoint.

For SAT specifically:
- SATInternalClosure = exact bit encoding + SAT in NP + SAT failure generator;
- SATExternalClosure = SATInternalClosure + external model match.

## Fail-proof attacks already closed

1. Arbitrary input encoder loophole: REFUTED formally.
2. Infinite/precomputed input control loophole: removed by canonical finite model.
3. Finite sampled evidence -> universal lower bound: REFUTED formally by FailProofFiniteAttack.finite_to_universal_principle_refuted.
4. Raw C12 Potential as a semantic lower-bound invariant: previously REFUTED by audit/C12/SRepresentationCounterexample.lean.
5. Benchmark/timing -> universal fail proof: excluded by the quantified type of FailureGenerator.

## Remaining actual mathematics

- G1 exact SAT NTM realization in the hardened canonical model.
- G2 FailureGenerator for SAT, or for any other explicitly proved NP language.
- G3 external model equivalence if an external formalization is required for the publication/certificate claim.

No finite experiment, sampled candidate list, elliptic-curve timing, raw Potential measurement, or arbitrary precomputation can fill G2.
