# P-vs-NP structural closure and oriented residue

STATUS: **STRUCTURAL ENVELOPE CLOSED / ORIENTATION UNRESOLVED / NO TARGET CERTIFICATE**

SOURCE LOCK: `6f310228a57984b33503a458f952207561c34c60`

## CLOSED STRUCTURAL CORE

The binary discriminant is

`D := NP ⊆ P`.

The fixed classical start supplied to the certificate is

`StartClosed := P ⊆ NP`.

The structural middle is completely closed:

`MiddleClosed := D ∨ SeparationWitness`,

where

`SeparationWitness := ∃ L, NP L ∧ ¬ P L`.

By classical excluded middle, the repository proves the middle envelope without
choosing an orientation. It also proves exclusivity:

`¬ (D ∧ SeparationWitness)`.

Under `StartClosed`:

`D ↔ EqualityFinal`

and

`SeparationWitness ↔ SeparationFinal`.

Therefore the start, middle envelope and final envelope are structurally closed.

## BIDIRECTIONAL TESTING

Forward scan:

`StartClosed -> MiddleClosed -> FinalClosed`.

Backward scan:

`EqualityFinal -> D`

and

`SeparationFinal + StartClosed -> SeparationWitness`.

The theorem `bidirectional_convergence` proves both scans use exactly the same
binary middle.

The detector

`D ∧ SeparationWitness -> False`

is the automatic inconsistency certificate if both orientations are ever
claimed simultaneously.

## WHAT REMAINS UNRESOLVED

Only the orientation of `D`:

- a genuine proof of `D` would yield `P = NP`;
- a genuine proof of `¬D` / `SeparationWitness` would yield `P ≠ NP`.

This is the Clay-level mathematical content. Structural closure does not choose
the orientation.

The older C12 quantitative route is retained as an experimental research layer,
not as a logical gap in the closed envelope. No theorem currently maps finite
`PaysOff` observations to either orientation of `D`.

## EMPIRICAL DATA

Baseline C12 contains 630 measured rows (n=1..12). The first analysis found:

- 546 `PaysOff=true`;
- 84 `PaysOff=false`;
- every false row has k=0, costBits=0, deltaRank=0 and margin=0;
- all 48 canonical family×size groups have at least one sampled positive witness;
- the smallest sampled positive k is 1 for all 48 groups.

This is finite evidence only.

C13 therefore targets the discovered boundary directly with 1,144 new cases:
n=13..64, k=0/1, three deterministic families plus random_k_cnf with 8 seeds.

## CERTIFICATE POLICY

- No `sorry`, `admit`, source-level `axiom`, or `constant`.
- Classical closure may depend only on Lean's trusted classical foundations.
- No finite dataset may be promoted to `D`, `¬D`, `P=NP`, or `P≠NP`.
- No oriented target certificate is emitted until an actual orientation witness exists.
