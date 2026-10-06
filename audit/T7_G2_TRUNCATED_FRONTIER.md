# T7 G2 — Truncated Frontier

Canonical terminal state:

- T7-G2-CLOCK-BRIDGE: GREEN | b74dd288 | run 37389578506
- T7-G2-FINITE-MACHINE-DESC: GREEN | 788651fc | run 37389822164
- T7-G2-TERMINAL: EXPOSED_GREEN | 52ba3d0e | run 37380589374
- T7-G2-COUNTEREXAMPLE: OPEN_MATH | 0/2 material payloads

Search status:

- KERNEL-SEARCH-V2 is disabled forward-only.
- No further exact?/aesop?/library_search attempts are part of this lane.
- certificate and fail-proof-all-gaps remain enabled and authoritative.

Material frontier:

1. T7-G2-UNIVERSAL-SIM — TRUNCATED/WONTFIX in this lane until the finite description is fully serialized and a universal simulator correspondence is kernel-valid.
2. T7-G2-SAT-MATERIALIZATION — TRUNCATED/WONTFIX in this lane until a Cook-Levin-style SATBits materialization with correctness and size control is kernel-valid.
3. T7-G2-SELF-REFERENCE — TRUNCATED/WONTFIX in this lane until a genuine self-reference construction produces x_M that refers to M on x_M, not merely on encode(M).
4. T7-G2-DISAGREEMENT — OPEN_MATH terminal lower-bound obligation:
   forall M : PolyDTMCandidate,
     not M.CorrectAt CanonicalSAT (selfCode M)

No module containing sorry/admit/axiom may be promoted as CLOSED_GREEN.
No use of UniversalFailure, Nonempty UniversalFailureWitness, FailureGenerator,
TotalSemanticFailureProducer, TotalExactDiagonalProducer, or not InP is accepted
as an input hypothesis to close the terminal witness.

The terminal may be promoted to CLOSED_GREEN only after a kernel-valid term:

  def closeG2 : UniversalFailureWitness :=
  { counterexample := selfCode
    fails := universalDisagreement }

is built without sorryAx and passes the existing certificate and fail-proof audits.

This file documents a forward-only truncation point. It does not claim P != NP
and it does not convert OPEN_MATH into a theorem.
