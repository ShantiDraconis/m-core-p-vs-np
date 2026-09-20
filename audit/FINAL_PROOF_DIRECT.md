# Direct Final-Proof Attack — P versus NP

STATUS: OLD_MODEL_REFUTED / CANONICAL_MODEL_GREEN / CLAY_LOWER_BOUND_OPEN

BASE_FROZEN: 7ab06d0430e48a323b1ed0096abe97762303c893
BRANCH: work/final-proof-direct-from-7ab06d04
VALIDATION_HEAD: 986be4dff3062d6622c54af6aba587f549ac4d48
VALIDATION_RUN: 35519289215
VALIDATION_RUN_NUMBER: 751
VALIDATION_JOB: 106100458397
VALIDATION_CONCLUSION: SUCCESS

## 1. Rejected direct model

The first direct endpoint used an arbitrary input encoder:

`encode : Circuit -> Configuration State Symbol`.

That interface is too strong because the encoder is outside the measured machine
runtime. The formal attack in `MCore.Real.FinalProofAttack` constructs a
one-step candidate whose encoder computes language membership classically and
stores the answer bit on the initial tape.

Certified consequences in the rejected model:

`every_language_inP_under_arbitrary_encode`

`current_SATNotInP_refuted`

`current_UniversalSATFailure_refuted`

`current_SATLowerBoundCertificate_refuted`

Therefore the old `SATNotInP` / `UniversalSATFailure` target is not a valid
complexity lower-bound model and must not be promoted.

This is a model refutation, not a result about the actual P-versus-NP problem.

## 2. Hardened canonical model

`MCore.Real.CanonicalFinalProof` removes both identified loopholes:

- no arbitrary input encoder;
- finite control `Fin (stateCount + 1)`;
- canonical bitstring tape input;
- dedicated blank/end symbol `none`;
- fixed polynomial bound constants per machine.

The targeted build and axiom audit were GREEN in run 751.

The hardened endpoint is:

`PneqNP := ¬ ∀ language : BitLanguage, InP language ↔ InNP language`.

For one target language:

`UniversalFailure language :=
  ∀ candidate : PolyDTMCandidate,
    ∃ x : BitString, ¬ candidate.CorrectAt language x`.

The module proves:

`UniversalFailure language ↔ ¬ InP language`

and

`InNP language -> UniversalFailure language -> PneqNP`.

## 3. Real fail-proof residue

The valid certificate payload is now:

`SeparationCertificate`

with:

- an explicit target bitstring language;
- a certified proof that the target is in NP;
- a universal deterministic fail proof for that target.

The actual Clay-level mathematical content remains the universal lower bound:

for every finite-control deterministic polynomial-time candidate, exhibit an
input on which it fails.

No finite benchmark, PARI/Sage timing, elliptic-curve search behavior, C12/C13
sample, raw Potential/costBits measurement, or bounded search inhabits this
universal proposition.

## 4. Additional eliminated route

The existing formal audit `audit/C12/SRepresentationCounterexample.lean`
shows that raw C12 `Potential` is not a semantic invariant: semantically
equivalent circuits can have different Potential values. Therefore direct
identification of raw Potential with a representation-independent complexity
lower bound is refuted. A minimized/representation-invariant calibration remains
an open bridge.

## Promotion rule

Emit a P-versus-NP separation certificate only after a hardened
`SeparationCertificate` is inhabited and its targeted Lean/axiom gates are
GREEN.

No `sorry`, `admit`, source-level axioms, hidden oracle/advice, arbitrary
precomputation in input encoding, benchmark-to-lower-bound promotion, or hidden
endpoint premise is permitted.
