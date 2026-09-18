# P-vs-NP backward-dense residue

STATUS: **RESIDUE / NO TARGET_CERTIFICATE / NO MATHEMATICAL PROMOTION**

SOURCE LOCK: `6f310228a57984b33503a458f952207561c34c60`

## THREE-TRACK NORMAL FORM

The audit now uses six syntactically closed boundaries:

- `E0`: `NP ⊆ P`.
- `EF`: extensional equality `P = NP`.
- `A0`: the C12 asymptotic quantitative frontier.
- `AF`: exit from the quantitative zone by delivering either `E0` or `S0`.
- `S0`: `∃ L, L ∈ NP ∧ L ∉ P`.
- `SF`: extensional separation `P ≠ NP`.

"Closed" here means **completely defined and type-checked**, not mathematically established.

With `P ⊆ NP` supplied as classical wiring:

`E0 ↔ EF`

and

`S0 ↔ SF`

are proved in `audit/ThreeTracks.lean`.

The middle notation `P≈NP` is represented only by
`PApproxNPResearchZone := A0`. It is **not a third classical complexity
relation**. The end of that zone is

`AF := E0 ∨ S0`.

Therefore any successful middle route must resolve to one of the two classical
sides.

## OPEN BRIDGE

The central middle obligation is exactly

`ApproximationBridge P NP := A0 → AF P NP`.

No theorem in the repository currently inhabits this proposition.

In expanded form the missing bridge is:

`C12 asymptotic quantitative structure → (NP ⊆ P) ∨ (∃ L ∈ NP \ P)`.

This is stronger and more honest than treating finite C12 measurements as an
endpoint theorem.

## HYPOTHESIS_RESIDUE

1. The repository still has only an abstract `ClassicalComplexityInterface`;
   the fixed official Turing-machine model adapter remains open.
2. Equality route: no proof of `E0 = NP ⊆ P`.
3. Separation route: no proof of `S0 = ∃ L ∈ NP \ P`.
4. Approximate route: neither the universal/asymptotic `A0` nor the transfer
   `A0 → AF` is proved by the finite C12 dataset.

## QUANTIFIER_RESIDUE

- C12 samples finitely many sizes/seeds/restrictions.
- `A0` is universal at the family-obligation level.
- `E0` quantifies over every language in the fixed official universe.
- `S0` requires one actual language in that fixed universe.
- Existing unconstrained K10 existential quantification over `Language` is
  insufficient for the official endpoint.

## SCALING_RESIDUE

`costBits`, `BranchingCost`, `stateRank`, and `Potential` are internally
certified quantities. No theorem currently turns them into a standard
polynomial-time upper bound or a superpolynomial lower bound in the official
complexity model.

## CONSTANT_RESIDUE

C12 uses explicit `alpha = beta = 1`. Robustness under weights, encoding
overheads, simulation constants, and asymptotic normalization is open.

## AXIOM_AUDIT

- Source-lock C12 hygiene remains GREEN.
- `audit/ThreeTracks.lean` is compiled directly by CI.
- CI prints axioms for the three routing theorems.
- New `sorry`, `admit`, source-level `axiom`, or `constant` in audit
  Lean files is a hard failure.

## EXACT FINAL SHAPE

Equality route:

`P ⊆ NP + E0 -> EF`.

Intermediate route:

`A0 + OPEN_BRIDGE(A0 -> AF) -> AF -> EF ∨ SF`.

Separation route:

`S0 -> SF`.

The only classical final outcomes represented are `EF` and `SF`.
No `TARGET_CERTIFICATE` is emitted because no real frontier has been closed.
