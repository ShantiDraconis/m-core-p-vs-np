# Oriented witness boundary — P vs NP

STATUS: **STRUCTURAL CORE CLOSED / ORIENTED MATERIAL ABSENT**

The closed 0–1–2 envelope is not the Clay solution. The only genuinely new
mathematical material that can orient the binary discriminant `D := NP ⊆ P`
is one of the following.

## Type A — equality orientation

Required payload:

1. a concrete algorithm deciding SAT/3-SAT;
2. a correctness theorem for every input;
3. a fixed polynomial runtime bound;
4. a formal NP-completeness transfer in the fixed official machine model.

Lean interface: `PolySATCertificate` + `SATCompletenessTransfer`.

Only after both are supplied does `typeA_closes_equality` produce `P = NP`.

## Type B — separation orientation

Required payload:

1. a concrete language `L`;
2. a proof `L ∈ NP`;
3. a proof `L ∉ P`.

Lean interface: `LowerBoundWitness`.

The field `not_in_p` is exactly where a genuine lower-bound theorem must
enter. Merely naming diagonalization, primes, RH, or a circuit heuristic does
not populate this field.

## Barrier audit

The following are recorded as technique-audit barriers, not assumptions:

- Baker–Gill–Solovay relativization (1975): oracle worlds exist with
  `P^A = NP^A` and others with `P^B ≠ NP^B`.
- Razborov–Rudich Natural Proofs: under their hardness/cryptographic framework,
  broad classes of natural circuit-lower-bound arguments cannot yield the
  needed general lower bounds.
- Aaronson–Wigderson algebrization: major questions including P vs NP require
  non-algebrizing techniques.

References:
- https://doi.org/10.1137/0204037
- https://doi.org/10.1006/jcss.1997.1494
- https://doi.org/10.1145/1490270.1490272

The barrier audit is intentionally metadata. It cannot be passed to a theorem
as a substitute for `not_in_p`.

## Cross-problem claims

Any RH/primes route must provide a formal implication into `D` or `¬D`.
Until such a bridge is proved, it is a candidate research program only.
