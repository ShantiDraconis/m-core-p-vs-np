# P02 G2.1 LITERAL FIXED-POINT ROUTE — CLOSED BY FALSIFICATION

Repository: ShantiDraconis/m-core-p-vs-np
Source SHA: 17c04b62d03946aab4573894833f087ade25bc33
Source blob: lean/MCore/Real/P02LiteralFixedPointCountermodel.lean
Source blob SHA: 7c73c72c7d43edd149b5ee22a3a1c01e60b19d49
Chain: P02 / G2.1
Classification: CLOSED_BY_FALSIFICATION
Verified run: 35721158651 — ATK P02 normalization frontier — SUCCESS

Formal payload:
- constantPairCandidate
- constantPair_false_correct
- constantPair_true_correct
- no_literal_fixed_point_if_constants_correct
- no_universal_literal_fixed_point

Verified gate properties:
- source hygiene passed
- lake build passed
- axiom audit passed
- no sorry/admit/partial promotion accepted by the gate

Meaning:
The current literal fixed-point strategy based on semanticDiagonalBits is not a universal producer.
There exists a polynomial deterministic candidate that is CorrectAt on both constant canonical SAT encodings,
and for that candidate the two-point semantic diagonal transformer has no literal fixed point.
Therefore the literal fixed-point route is closed by falsification and must not be reopened.

Scope firewall:
This certificate does NOT prove SAT ∉ P.
It does NOT construct a FailureGenerator for canonical SAT.
It does NOT close G2.2, G2.3, P02 FINAL, FINAL_INTERNAL, or FINAL_EXTERNAL.

Terminal status:
G2.1 literal fixed-point route: CLOSED_BY_FALSIFICATION
P02 final: OPEN_MATH at the universal SAT failure-generator witness.
